use std::any::Any;
use std::collections::HashMap;

use felt::Felt252;
use num_traits::ToPrimitive;
use serde::Deserialize;

use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_integer_from_var_name, get_ptr_from_var_name, insert_value_from_var_name, insert_value_into_ap,
};
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::ApTracking;
use crate::types::exec_scope::ExecutionScopes;
use crate::types::relocatable::{MaybeRelocatable, Relocatable};
use crate::vm::errors::hint_errors::HintError;
use crate::vm::errors::memory_errors::MemoryError;
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

    /// Packed outputs.
    pub(crate) const PACKED_OUTPUTS: &str = "packed_outputs";

    /// Packed output for the current task.
    pub(crate) const PACKED_OUTPUT: &str = "packed_output";
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct BootloaderConfig {
    pub simple_bootloader_program_hash: Felt252,
    pub supported_cairo_verifier_program_hashes: Vec<Felt252>,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub enum PackedOutput {
    Plain(Vec<Felt252>),
    Composite(Vec<Felt252>),
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
/// Mimics the behaviour of the Python VM `gen_arg`.
///
/// Creates a new segment for each vector encountered in `args`. For each new
/// segment, the pointer to the segment will be added to the current segment.
///
/// Example: `vec![1, 2, vec![3, 4]]`
/// -> Allocates segment N, starts writing at offset 0:
/// (N, 0): 1       # Write the values of the vector one by one
/// (N, 1): 2
/// -> a vector is encountered, allocate a new segment
/// (N, 2): N+1     # Pointer to the new segment
/// (N+1, 0): 3     # Write the values of the nested vector
/// (N+1, 1): 4
fn gen_arg(vm: &mut VirtualMachine, args: &Vec<Box<dyn Any>>) -> Result<Relocatable, MemoryError> {
    let base = vm.segments.add();
    let mut ptr = base.clone();

    for arg in args {
        if let Some(value) = arg.downcast_ref::<MaybeRelocatable>() {
            ptr = vm.segments.load_data(ptr, &vec![value.clone()])?;
        } else if let Some(vector) = arg.downcast_ref::<Vec<Box<dyn Any>>>() {
            let nested_base = gen_arg(vm, vector)?;
            ptr = vm.segments.load_data(ptr, &vec![nested_base.into()])?;
        } else {
            return Err(MemoryError::GenArgInvalidType);
        }
    }

    Ok(base)
}

/// Implements
/// from starkware.cairo.bootloaders.bootloader.objects import BootloaderConfig
/// bootloader_config: BootloaderConfig = bootloader_input.bootloader_config
///
/// ids.bootloader_config = segments.gen_arg(
///     [
///         bootloader_config.simple_bootloader_program_hash,
///         len(bootloader_config.supported_cairo_verifier_program_hashes),
///         bootloader_config.supported_cairo_verifier_program_hashes,
///     ],
/// )
pub fn load_bootloader_config(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let bootloader_input: BootloaderInput = exec_scopes.get(vars::BOOTLOADER_INPUT)?;
    let config = bootloader_input.bootloader_config;

    // Organize args as
    // [
    //     bootloader_config.simple_bootloader_program_hash,
    //     len(bootloader_config.supported_cairo_verifier_program_hashes),
    //     bootloader_config.supported_cairo_verifier_program_hashes,
    // ]
    let mut program_hashes = Vec::<Box<dyn Any>>::new();
    for program_hash in &config.supported_cairo_verifier_program_hashes {
        program_hashes.push(Box::new(MaybeRelocatable::from(program_hash)));
    }

    let mut args = Vec::<Box<dyn Any>>::new();
    args.push(Box::new(MaybeRelocatable::from(
        config.simple_bootloader_program_hash,
    )));
    args.push(Box::new(MaybeRelocatable::from(
        config.supported_cairo_verifier_program_hashes.len(),
    )));
    args.push(Box::new(program_hashes));

    // Store the args in the VM memory
    let args_segment = gen_arg(vm, &args)?;
    insert_value_from_var_name("bootloader_config", args_segment, vm, ids_data, ap_tracking)?;

    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.bootloader.objects import PackedOutput
///
/// task_id = len(packed_outputs) - ids.n_subtasks
/// packed_output: PackedOutput = packed_outputs[task_id]
///
/// vm_enter_scope(new_scope_locals=dict(packed_output=packed_output))
pub fn enter_packed_output_scope(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // task_id = len(packed_outputs) - ids.n_subtasks
    let packed_outputs: Vec<PackedOutput> = exec_scopes.get(vars::PACKED_OUTPUTS)?;
    let n_subtasks = get_integer_from_var_name("n_subtasks", vm, ids_data, ap_tracking)
        .unwrap()
        .to_usize()
        .unwrap();
    let task_id = packed_outputs.len() - n_subtasks;
    // packed_output: PackedOutput = packed_outputs[task_id]
    let packed_output: Box<dyn Any> = Box::new(packed_outputs[task_id].clone());

    // vm_enter_scope(new_scope_locals=dict(packed_output=packed_output))
    exec_scopes.enter_scope(HashMap::from([(
        vars::PACKED_OUTPUT.to_string(),
        packed_output,
    )]));

    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.bootloader.objects import (
///     CompositePackedOutput,
///     PlainPackedOutput,
/// )
pub fn import_packed_output_schemas() -> Result<(), HintError> {
    // Nothing to do!
    Ok(())
}

/// Implements %{ isinstance(packed_output, PlainPackedOutput) %}
///
/// Stores the result in the `ap` register to be accessed by the program.
pub fn is_plain_packed_output(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let packed_output: PackedOutput = exec_scopes.get(vars::PACKED_OUTPUT)?;
    let result = match packed_output {
        PackedOutput::Plain(_) => 1,
        _ => 0,
    };
    insert_value_into_ap(vm, result)?;

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
pub fn save_packed_outputs(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
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
pub fn set_packed_output_to_subtasks(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
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
    let packed_output = exec_scopes.get::<PackedOutput>("packed_output")?;
    let data = packed_output.elements_for_hash();
    insert_value_from_var_name(
        "nested_subtasks_output_len",
        data.len(),
        vm,
        ids_data,
        ap_tracking,
    )?;
    // TODO: equivalent of 'segments.gen_arg'
    insert_value_from_var_name(
        "nested_subtasks_output",
        Felt252::from(42),
        vm,
        ids_data,
        ap_tracking,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::BuiltinHintProcessor;
    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::HintProcessorData;
    use crate::hint_processor::builtin_hint_processor::hint_code;
    use crate::hint_processor::builtin_hint_processor::hint_utils::{
        get_integer_from_var_name, get_maybe_relocatable_from_var_name,
    };
    use crate::hint_processor::hint_processor_definition::HintProcessorLogic;
    use std::ops::Add;

    use num_traits::ToPrimitive;
    use rstest::{fixture, rstest};

    use crate::hint_processor::builtin_hint_processor::hint_utils::get_ptr_from_var_name;
    use crate::hint_processor::hint_processor_definition::HintReference;
    use crate::serde::deserialize_program::OffsetValue;
    use crate::types::exec_scope::ExecutionScopes;
    use crate::types::relocatable::MaybeRelocatable;
    use crate::utils::test_utils::*;
    use crate::vm::runners::builtin_runner::BuiltinRunner;
    use crate::vm::vm_core::VirtualMachine;
    use crate::{any_box, relocatable};
    use assert_matches::assert_matches;

    use super::*;

    #[fixture]
    fn bootloader_input() -> BootloaderInput {
        BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path: None,
                single_page: false,
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: Felt252::new(1234),
                supported_cairo_verifier_program_hashes: vec![
                    Felt252::new(5678),
                    Felt252::new(8765),
                ],
            },
            packed_outputs: vec![],
        }
    }

    #[rstest]
    fn test_prepare_simple_bootloader_output_segment(bootloader_input: BootloaderInput) {
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
    #[rstest]
    fn test_prepare_simple_bootloader_input(bootloader_input: BootloaderInput) {
        let mut exec_scopes = ExecutionScopes::new();
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

    #[rstest]
    fn test_load_bootloader_config(bootloader_input: BootloaderInput) {
        let config = bootloader_input.bootloader_config.clone();

        let mut vm = vm!();
        add_segments!(vm, 2);
        vm.run_context.fp = 2;

        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = ids_data!["bootloader_config"];
        let ap_tracking = ApTracking::new();

        exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input);

        load_bootloader_config(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Bootloader hint failed unexpectedly");

        let bootloader_config_segment =
            get_ptr_from_var_name("bootloader_config", &mut vm, &ids_data, &ap_tracking).unwrap();

        let config_segment = vm
            .segments
            .memory
            .get_continuous_range(bootloader_config_segment, 3)
            .unwrap();

        // Assert that the values in the config segment match
        let bootloader_hash = &config_segment[0];
        assert!(
            matches!(bootloader_hash, MaybeRelocatable::Int(x) if *x == config.simple_bootloader_program_hash)
        );

        let nb_programs = &config_segment[1];
        let expected_nb_programs = config.supported_cairo_verifier_program_hashes.len();
        assert!(
            matches!(nb_programs, MaybeRelocatable::Int(x) if x.to_usize().unwrap() == expected_nb_programs)
        );

        // Assert that the values in the programs segment match
        let programs_segment = &config_segment[2];
        match programs_segment {
            MaybeRelocatable::RelocatableValue(relocatable) => {
                let program_hashes: Vec<Felt252> = vm
                    .segments
                    .memory
                    .get_integer_range(relocatable.clone(), expected_nb_programs)
                    .unwrap()
                    .iter()
                    .map(|cow| cow.clone().into_owned())
                    .collect();

                assert_eq!(
                    program_hashes,
                    config.supported_cairo_verifier_program_hashes
                );
            }
            other => {
                panic!("Expected a pointer to another segment, got {:?}", other);
            }
        }
    }

    #[rstest]
    fn test_gen_arg() {
        let mut vm = vm!();

        let mut nested_args = Vec::<Box<dyn Any>>::new();
        nested_args.push(Box::new(MaybeRelocatable::from(128)));
        nested_args.push(Box::new(MaybeRelocatable::from(42)));

        let mut args = Vec::<Box<dyn Any>>::new();
        args.push(Box::new(MaybeRelocatable::from(1001)));
        args.push(Box::new(MaybeRelocatable::from(2048)));
        args.push(Box::new(nested_args));

        let args_base: Relocatable = gen_arg(&mut vm, &args).expect("gen_args failed unexpectedly");

        let values = vm
            .segments
            .memory
            .get_integer_range(args_base, 2)
            .expect("Loading values failed");

        assert_eq!(*values[0], 1001.into());
        assert_eq!(*values[1], 2048.into());

        let nested_args_address: Relocatable = args_base.add(2i32).unwrap();
        let nested_args_base = vm
            .segments
            .memory
            .get_relocatable(nested_args_address)
            .expect("Nested vector should be here");

        let nested_values = vm
            .segments
            .memory
            .get_integer_range(nested_args_base, 2)
            .expect("Loading nested values failed");

        assert_eq!(*nested_values[0], 128.into());
        assert_eq!(*nested_values[1], 42.into());
    }

    #[rstest]
    fn test_enter_packed_output_scope() {
        let mut vm = vm!();
        // Set n_subtasks to 2
        vm.run_context.fp = 1;
        vm.segments = segments![((1, 0), 2)];
        let ids_data = ids_data!["n_subtasks"];

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let packed_outputs = vec![
            PackedOutput::Plain(vec![]),
            PackedOutput::Composite(vec![]),
            PackedOutput::Plain(vec![]),
        ];
        exec_scopes.insert_value(vars::PACKED_OUTPUTS, packed_outputs);

        enter_packed_output_scope(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that we entered a new scope
        assert_eq!(exec_scopes.data.len(), 2);
        assert_eq!(exec_scopes.data[1].len(), 1);

        let packed_output = exec_scopes
            .get(vars::PACKED_OUTPUT)
            .expect("PACKED_OUTPUT not present in scope");

        assert!(matches!(packed_output, PackedOutput::Composite(_)));
    }

    #[test]
    fn test_is_plain_packed_output() {
        let mut vm = vm!();
        add_segments!(vm, 2);

        let mut exec_scopes = ExecutionScopes::new();

        fn is_plain(
            vm: &mut VirtualMachine,
            exec_scopes: &mut ExecutionScopes,
            packed_output: PackedOutput,
        ) -> bool {
            exec_scopes.insert_value(vars::PACKED_OUTPUT, packed_output);
            is_plain_packed_output(vm, exec_scopes).expect("Hint failed unexpectedly");
            let result = vm
                .segments
                .memory
                .get_integer(vm.run_context.get_ap())
                .unwrap();

            result.into_owned() != Felt252::from(0)
        }

        let plain_packed_output = PackedOutput::Plain(Vec::<Felt252>::new());
        let composite_packed_output = PackedOutput::Composite(Vec::<Felt252>::new());

        assert!(is_plain(&mut vm, &mut exec_scopes, plain_packed_output));

        // Increment AP to avoid an inconsistent memory error writing in the same slot
        vm.run_context.ap += 1;
        assert!(!is_plain(
            &mut vm,
            &mut exec_scopes,
            composite_packed_output
        ));
    }

    #[test]
    fn test_save_output_pointer() {
        let mut vm = vm!();
        vm.segments = segments![((1, 0), (0, 0))];
        let mut hint_ref = HintReference::new(0, 0, true, false);
        hint_ref.offset2 = OffsetValue::Value(2);
        let ids_data = HashMap::from([("output_ptr".to_string(), hint_ref)]);

        let mut exec_scopes = ExecutionScopes::new();

        let hint_data = HintProcessorData::new_default(
            String::from(hint_code::BOOTLOADER_SAVE_OUTPUT_POINTER),
            ids_data,
        );
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
        let packed_outputs = vec![
            PackedOutput::Plain(Default::default()),
            PackedOutput::Plain(Default::default()),
            PackedOutput::Plain(Default::default()),
        ];

        let bootloader_input = BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path: None,
                single_page: false,
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: 42u64.into(),
                supported_cairo_verifier_program_hashes: Default::default(),
            },
            packed_outputs: packed_outputs.clone(),
        };

        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box("bootloader_input", Box::new(bootloader_input.clone()));

        let hint_data = HintProcessorData::new_default(
            String::from(hint_code::BOOTLOADER_SAVE_PACKED_OUTPUTS),
            HashMap::new(),
        );
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

        assert_eq!(
            saved_packed_outputs.expect("asserted Ok above, qed").len(),
            3
        );
    }

    #[test]
    fn test_set_packed_output_to_subtasks() {
        use felt::Felt252;

        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box("packed_output", Box::new(Felt252::from(42)));

        let hint_data = HintProcessorData::new_default(
            String::from(hint_code::BOOTLOADER_SET_PACKED_OUTPUT_TO_SUBTASKS),
            HashMap::new(),
        );
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
        let mut vm = vm!();
        add_segments!(vm, 2);
        vm.run_context.fp = 2;

        let ids_data = ids_data!["nested_subtasks_output_len", "nested_subtasks_output"];

        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box(
            "packed_output",
            Box::new(PackedOutput::Plain(Default::default())),
        );

        let ap_tracking = ApTracking::new();

        assert_matches!(
            run_hint!(
                vm,
                ids_data.clone(),
                hint_code::BOOTLOADER_GUESS_PRE_IMAGE_OF_SUBTASKS_OUTPUT_HASH,
                &mut exec_scopes
            ),
            Ok(())
        );
        let nested_subtasks_output_len =
            get_integer_from_var_name("nested_subtasks_output_len", &vm, &ids_data, &ap_tracking)
                .expect("nested_subtasks_output_len should be set")
                .into_owned();
        assert_eq!(nested_subtasks_output_len, 0.into());

        let nested_subtasks_output =
            get_integer_from_var_name("nested_subtasks_output", &vm, &ids_data, &ap_tracking)
                .expect("nested_subtasks_output should be set")
                .into_owned();
        assert_eq!(nested_subtasks_output, 42.into());
    }
}
