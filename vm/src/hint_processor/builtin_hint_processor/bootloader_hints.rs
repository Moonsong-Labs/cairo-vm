use std::collections::HashMap;

use serde::Deserialize;

use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_ptr_from_var_name,
    insert_value_from_var_name,
};
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::ApTracking;
use crate::types::exec_scope::ExecutionScopes;
use crate::types::relocatable::Relocatable;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::errors::vm_errors::VirtualMachineError;
use crate::vm::runners::builtin_runner::OutputBuiltinRunner;
use crate::vm::vm_core::VirtualMachine;

mod vars {
    /// Deserialized bootloader input.
    pub(crate) const BOOTLOADER_INPUT: &str = "bootloader_input";

    /// Saved state of the output builtin.
    pub(crate) const OUTPUT_BUILTIN_STATE: &str = "output_builtin_state";

    /// Deserialized simple bootloader input.
    pub(crate) const SIMPLE_BOOTLOADER_INPUT: &str = "simple_bootloader_input";
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
#[serde(transparent)]
pub struct ProgramHash(pub u64);

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct BootloaderConfig {
    pub simple_bootloader_program_hash: ProgramHash,
    pub supported_cairo_verifier_program_hashes: Vec<ProgramHash>,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct PackedOutput {
    // TODO: missing definitions of PlainPackedOutput, CompositePackedOutput
}

impl PackedOutput {
    // TODO: implement and define return type
    pub fn elements_for_hash(&self) -> Vec<()> {
        Default::default()
    }
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct SimpleBootloaderInput {
    pub fact_topologies_path: Option<String>,
    pub single_page: bool,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct BootloaderInput {
    pub simple_bootloader_input: SimpleBootloaderInput,
    pub bootloader_config: BootloaderConfig,
    pub packed_outputs: Vec<PackedOutput>,
}

fn replace_output_builtin(
    vm: &mut VirtualMachine,
    mut new_builtin: OutputBuiltinRunner,
) -> Result<OutputBuiltinRunner, VirtualMachineError> {
    let old_builtin = vm.get_output_builtin()?;
    std::mem::swap(old_builtin, &mut new_builtin);
    Ok(new_builtin)
}

/// Implements
/// %{
///     from starkware.cairo.bootloaders.bootloader.objects import BootloaderInput
///     bootloader_input = BootloaderInput.Schema().load(program_input)
///
///     ids.simple_bootloader_output_start = segments.add()
///
///     # Change output builtin state to a different segment in preparation for calling the
///     # simple bootloader.
///     output_builtin_state = output_builtin.get_state()
///     output_builtin.new_state(base=ids.simple_bootloader_output_start)
/// %}
pub fn prepare_simple_bootloader_output_segment(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // Python: bootloader_input = BootloaderInput.Schema().load(program_input)
    // -> Assert that the bootloader input has been loaded when setting up the VM
    let _bootloader_input: BootloaderInput = exec_scopes.get(vars::BOOTLOADER_INPUT)?;

    // Python: ids.simple_bootloader_output_start = segments.add()
    let new_segment_base = vm.add_memory_segment();
    insert_value_from_var_name(
        "simple_bootloader_output_start",
        new_segment_base.clone(),
        vm,
        ids_data,
        ap_tracking,
    )?;

    // Python:
    // output_builtin_state = output_builtin.get_state()
    // output_builtin.new_state(base=ids.simple_bootloader_output_start)
    let new_output_builtin = OutputBuiltinRunner::from_segment(&new_segment_base, true);
    let previous_output_builtin = replace_output_builtin(vm, new_output_builtin)?;
    exec_scopes.insert_value(vars::OUTPUT_BUILTIN_STATE, previous_output_builtin);

    insert_value_from_var_name(
        "simple_bootloader_output_start",
        new_segment_base,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

/// Implements %{ simple_bootloader_input = bootloader_input %}
pub fn prepare_simple_bootloader_input(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let bootloader_input: BootloaderInput = exec_scopes.get(vars::BOOTLOADER_INPUT)?;
    exec_scopes.insert_value(vars::SIMPLE_BOOTLOADER_INPUT, bootloader_input);

    Ok(())
}

/// Implements
/// # Restore the bootloader's output builtin state.
/// output_builtin.set_state(output_builtin_state)
pub fn restore_bootloader_output(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let previous_output_builtin: OutputBuiltinRunner =
        exec_scopes.get(vars::OUTPUT_BUILTIN_STATE)?;
    let _ = replace_output_builtin(vm, previous_output_builtin)?;

    Ok(())
}

/*
Implements hint:
%{
    output_start = ids.output_ptr
%}
*/
pub fn save_output_pointer(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    exec_scopes.insert_value("output_start", output_ptr);
    Ok(())
}

/*
Implements hint:
%{
    packed_outputs = bootloader_input.packed_outputs
%}
*/
pub fn save_packed_outputs(
    _vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let bootloader_input: BootloaderInput = exec_scopes.get("bootloader_input")?;
    let packed_outputs = bootloader_input.packed_outputs;
    exec_scopes.insert_value("packed_outputs", packed_outputs);
    Ok(())
}

/*
Implements hint:
%{
    packed_outputs = packed_output.subtasks
%}
*/
pub fn set_packed_output_to_subtasks(
    _vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    use felt::Felt252;

    let packed_outputs = exec_scopes.get::<Felt252>("packed_output")?; // TODO: need real type
    let subtasks = packed_outputs; // TODO: need type for packed_output / query its subtasks field
    exec_scopes.insert_value("packed_outputs", subtasks);
    Ok(())
}

/*
Implements hint:
%{
    data = packed_output.elements_for_hash()
    ids.nested_subtasks_output_len = len(data)
    ids.nested_subtasks_output = segments.gen_arg(data)";
%}
*/
pub fn guess_pre_image_of_subtasks_output_hash(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    use felt::Felt252;

    let packed_output = exec_scopes.get::<PackedOutput>("packed_output")?;
    let data = packed_output.elements_for_hash();
    insert_value_from_var_name("nested_subtasks_output_len", data.len(), vm, ids_data, ap_tracking)?;
    // TODO: equivalent of 'segments.gen_arg'
    insert_value_from_var_name("nested_subtasks_output", Felt252::from(42), vm, ids_data, ap_tracking)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::hint_processor::builtin_hint_processor::hint_utils::{
        get_integer_from_var_name,
        get_maybe_relocatable_from_var_name,
    };
    use crate::hint_processor::hint_processor_definition::HintReference;
    use crate::types::exec_scope::ExecutionScopes;
    use crate::types::relocatable::MaybeRelocatable;
    use crate::utils::test_utils::*;
    use crate::vm::runners::builtin_runner::BuiltinRunner;
    use crate::vm::vm_core::VirtualMachine;
    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::HintProcessorData;
    use crate::serde::deserialize_program::OffsetValue;
    use assert_matches::assert_matches;
    use crate::{any_box, relocatable};
    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::BuiltinHintProcessor;
    use crate::hint_processor::hint_processor_definition::HintProcessorLogic;


    use super::*;

    #[test]
    fn test_prepare_simple_bootloader_output_segment() {
        let mut vm = vm!();
        vm.segments.add();
        vm.run_context.fp = 1;

        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin.clone()));

        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = ids_data!["simple_bootloader_output_start"];
        let ap_tracking = ApTracking::new();

        let bootloader_input = BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path: None,
                single_page: false,
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: ProgramHash(1234),
                supported_cairo_verifier_program_hashes: vec![ProgramHash(5678), ProgramHash(8765)],
            },
            packed_outputs: vec![],
        };

        exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input);
        prepare_simple_bootloader_output_segment(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
        )
        .expect("Hint failed unexpectedly");

        let current_output_builtin = vm
            .get_output_builtin()
            .expect("The VM should have an output builtin")
            .clone();
        let stored_output_builtin: OutputBuiltinRunner = exec_scopes
            .get(vars::OUTPUT_BUILTIN_STATE)
            .expect("The output builtin is not stored in the execution scope as expected");

        // Check the content of the stored output builtin
        assert_ne!(current_output_builtin.base(), stored_output_builtin.base());
        assert_eq!(stored_output_builtin.base(), output_builtin.base());
        assert_eq!(stored_output_builtin.stop_ptr, output_builtin.stop_ptr);
        assert_eq!(stored_output_builtin.included, output_builtin.included);

        let simple_bootloader_output_start = get_maybe_relocatable_from_var_name(
            "simple_bootloader_output_start",
            &vm,
            &ids_data,
            &ap_tracking,
        )
        .expect("Simple bootloader output start not accessible from program IDs");
        assert!(
            matches!(simple_bootloader_output_start, MaybeRelocatable::RelocatableValue(relocatable) if relocatable.segment_index == current_output_builtin.base() as isize)
        );
    }

    #[test]
    fn test_prepare_simple_bootloader_output_segment_missing_input() {
        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = HashMap::<String, HintReference>::new();
        let ap_tracking = ApTracking::default();

        let result = prepare_simple_bootloader_output_segment(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
        );
        let hint_error =
            result.expect_err("Hint should fail, the bootloader input variable is not set");
        assert!(
            matches!(hint_error, HintError::VariableNotInScopeError(s) if s == vars::BOOTLOADER_INPUT.into())
        );
    }
    #[test]
    fn test_prepare_simple_bootloader_input() {
        let mut exec_scopes = ExecutionScopes::new();
        let bootloader_input = BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path: None,
                single_page: false,
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: ProgramHash(123),
                supported_cairo_verifier_program_hashes: vec![ProgramHash(456), ProgramHash(789)],
            },
            packed_outputs: vec![],
        };
        exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input.clone());

        prepare_simple_bootloader_input(&mut exec_scopes).expect("Hint failed unexpectedly");

        let simple_bootloader_input: BootloaderInput = exec_scopes
            .get(vars::SIMPLE_BOOTLOADER_INPUT)
            .expect("Simple bootloader input not in scope");
        assert_eq!(simple_bootloader_input, bootloader_input);
    }

    #[test]
    fn test_restore_bootloader_output() {
        let mut vm: VirtualMachine = vm!();
        // The VM must have an existing output segment
        vm.builtin_runners =
            vec![OutputBuiltinRunner::from_segment(&vm.add_memory_segment(), true).into()];

        let mut exec_scopes = ExecutionScopes::new();
        let new_segment = vm.add_memory_segment();
        let original_output_builtin = OutputBuiltinRunner::from_segment(&new_segment, true);
        exec_scopes.insert_value(vars::OUTPUT_BUILTIN_STATE, original_output_builtin.clone());

        restore_bootloader_output(&mut vm, &mut exec_scopes).expect("Error while executing hint");

        assert_eq!(vm.builtin_runners.len(), 1);
        match &vm.builtin_runners[0] {
            BuiltinRunner::Output(output_builtin) => {
                assert_eq!(output_builtin.base(), original_output_builtin.base());
                assert_eq!(output_builtin.stop_ptr, original_output_builtin.stop_ptr);
                assert_eq!(output_builtin.included, original_output_builtin.included);
            }
            other => panic!("Expected an output builtin, found {:?}", other),
        }
    }

    #[test]
    fn test_save_output_pointer() {
        use crate::hint_processor::builtin_hint_processor::hint_code::BOOTLOADER_SAVE_OUTPUT_POINTER;

        let mut vm = vm!();
        vm.segments = segments![((1, 0), (0, 0))];
        let mut hint_ref = HintReference::new(0, 0, true, false);
        hint_ref.offset2 = OffsetValue::Value(2);
        let ids_data = HashMap::from([("output_ptr".to_string(), hint_ref)]);

        let mut exec_scopes = ExecutionScopes::new();

        let hint_data =
            HintProcessorData::new_default(String::from(BOOTLOADER_SAVE_OUTPUT_POINTER), ids_data);
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            hint_processor.execute_hint(
                &mut vm,
                &mut exec_scopes,
                &any_box!(hint_data),
                &HashMap::new(),
            ),
            Ok(())
        );

        let output_ptr = exec_scopes.get::<Relocatable>("output_start");
        assert_matches!(
            output_ptr,
            Ok(x) if x == relocatable!(0, 2)
        );
    }

    #[test]
    fn test_save_packed_ouputs() {
        use crate::hint_processor::builtin_hint_processor::hint_code::BOOTLOADER_SAVE_PACKED_OUTPUTS;

        let packed_outputs = vec![
            PackedOutput {},
            PackedOutput {},
            PackedOutput {},
        ];

        let bootloader_input = BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput { fact_topologies_path: None, single_page: false },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: ProgramHash(42u64),
                supported_cairo_verifier_program_hashes: Default::default(),
            },
            packed_outputs: packed_outputs.clone(), 
        };

        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box("bootloader_input", Box::new(bootloader_input.clone()));

        let hint_data =
            HintProcessorData::new_default(String::from(BOOTLOADER_SAVE_PACKED_OUTPUTS), HashMap::new());
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            hint_processor.execute_hint(
                &mut vm,
                &mut exec_scopes,
                &any_box!(hint_data),
                &HashMap::new(),
            ),
            Ok(())
        );

        let saved_packed_outputs = exec_scopes.get::<Vec<PackedOutput>>("packed_outputs");
        assert_matches!(
            saved_packed_outputs,
            Ok(ref x) if x == &packed_outputs
        );

        assert_eq!(saved_packed_outputs.expect("asserted Ok above, qed").len(), 3);
    }

    #[test]
    fn test_set_packed_output_to_subtasks() {
        use crate::hint_processor::builtin_hint_processor::hint_code::BOOTLOADER_SET_PACKED_OUTPUT_TO_SUBTASKS;
        use felt::Felt252;

        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box("packed_output", Box::new(Felt252::from(42)));

        let hint_data =
            HintProcessorData::new_default(String::from(BOOTLOADER_SET_PACKED_OUTPUT_TO_SUBTASKS), HashMap::new());
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            hint_processor.execute_hint(
                &mut vm,
                &mut exec_scopes,
                &any_box!(hint_data),
                &HashMap::new(),
            ),
            Ok(())
        );

        let packed_outputs = exec_scopes.get::<Felt252>("packed_outputs");
        assert_matches!(
            packed_outputs,
            Ok(x) if x == Felt252::from(42)
        );
    }

    #[test]
    fn test_guess_pre_image_of_subtasks_output_hash() {
        use crate::hint_processor::builtin_hint_processor::hint_code::BOOTLOADER_GUESS_PRE_IMAGE_OF_SUBTASKS_OUTPUT_HASH;

        let mut vm = vm!();
        add_segments!(vm, 2);
        vm.run_context.fp = 2;
        let ids_data = ids_data!["nested_subtasks_output_len", "nested_subtasks_output"];

        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box("packed_output", Box::new(PackedOutput {}));

        let hint_data =
            HintProcessorData::new_default(String::from(BOOTLOADER_GUESS_PRE_IMAGE_OF_SUBTASKS_OUTPUT_HASH), ids_data);
        let hint_data = any_box!(hint_data);
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            hint_processor.execute_hint(
                &mut vm,
                &mut exec_scopes,
                &hint_data,
                &HashMap::new(),
            ),
            Ok(())
        );

        let hint_data: &HintProcessorData = hint_data.downcast_ref().expect("type given above");
        let nested_subtasks_output_len = get_integer_from_var_name(
            "nested_subtasks_output_len",
            &vm,
            &hint_data.ids_data,
            &hint_data.ap_tracking
        )
        .expect("nested_subtasks_output_len should be set")
        .into_owned();
        assert_eq!(nested_subtasks_output_len, 0.into());
        
        let nested_subtasks_output = get_integer_from_var_name(
            "nested_subtasks_output",
            &vm,
            &hint_data.ids_data,
            &hint_data.ap_tracking
        )
        .expect("nested_subtasks_output should be set")
        .into_owned();
        assert_eq!(nested_subtasks_output, 42.into());
    }

}
