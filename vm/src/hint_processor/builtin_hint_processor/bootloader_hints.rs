use std::collections::HashMap;

use serde::Deserialize;

use crate::hint_processor::builtin_hint_processor::hint_utils::insert_value_from_var_name;
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::ApTracking;
use crate::types::exec_scope::ExecutionScopes;
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

#[cfg(test)]
mod tests {
    use crate::hint_processor::builtin_hint_processor::hint_utils::get_maybe_relocatable_from_var_name;
    use crate::hint_processor::hint_processor_definition::HintReference;
    use crate::types::exec_scope::ExecutionScopes;
    use crate::types::relocatable::MaybeRelocatable;
    use crate::utils::test_utils::*;
    use crate::vm::runners::builtin_runner::BuiltinRunner;
    use crate::vm::vm_core::VirtualMachine;

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
}
