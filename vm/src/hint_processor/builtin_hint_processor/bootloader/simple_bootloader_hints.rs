use std::collections::HashMap;

use felt::Felt252;

use crate::hint_processor::builtin_hint_processor::bootloader::types::{
    FactTopology, SimpleBootloaderInput,
};
use crate::hint_processor::builtin_hint_processor::bootloader::vars;
use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_ptr_from_var_name, insert_value_from_var_name,
};
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::ApTracking;
use crate::types::exec_scope::ExecutionScopes;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::vm_core::VirtualMachine;

/// Implements
/// n_tasks = len(simple_bootloader_input.tasks)
/// memory[ids.output_ptr] = n_tasks
///
/// # Task range checks are located right after simple bootloader validation range checks, and
/// # this is validated later in this function.
/// ids.task_range_check_ptr = ids.range_check_ptr + ids.BuiltinData.SIZE * n_tasks
///
/// # A list of fact_toplogies that instruct how to generate the fact from the program output
/// # for each task.
/// fact_topologies = []
pub fn prepare_task_range_checks(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // n_tasks = len(simple_bootloader_input.tasks)
    let simple_bootloader_input: SimpleBootloaderInput =
        exec_scopes.get(vars::SIMPLE_BOOTLOADER_INPUT)?;
    let n_tasks = simple_bootloader_input.tasks.len();

    // memory[ids.output_ptr] = n_tasks
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    vm.insert_value(output_ptr, Felt252::from(n_tasks))?;

    // ids.task_range_check_ptr = ids.range_check_ptr + ids.BuiltinData.SIZE * n_tasks
    // BuiltinData is a struct with 8 members defined in execute_task.cairo.
    const BUILTIN_DATA_SIZE: usize = 8;
    let range_check_ptr = get_ptr_from_var_name("range_check_ptr", vm, ids_data, ap_tracking)?;
    let task_range_check_ptr = (range_check_ptr + BUILTIN_DATA_SIZE * n_tasks)?;
    insert_value_from_var_name(
        "task_range_check_ptr",
        task_range_check_ptr,
        vm,
        ids_data,
        ap_tracking,
    )?;

    // fact_topologies = []
    let fact_topologies = Vec::<FactTopology>::new();
    exec_scopes.insert_value(vars::FACT_TOPOLOGIES, fact_topologies);

    Ok(())
}

#[cfg(test)]
mod tests {
    use num_traits::ToPrimitive;
    use std::collections::HashMap;

    use rstest::{fixture, rstest};

    use crate::hint_processor::builtin_hint_processor::bootloader::simple_bootloader_hints::prepare_task_range_checks;
    use crate::hint_processor::builtin_hint_processor::bootloader::types::{
        FactTopology, SimpleBootloaderInput, Task,
    };
    use crate::hint_processor::builtin_hint_processor::bootloader::vars;
    use crate::hint_processor::builtin_hint_processor::hint_utils::get_ptr_from_var_name;
    use crate::hint_processor::hint_processor_definition::HintReference;
    use crate::serde::deserialize_program::ApTracking;
    use crate::types::exec_scope::ExecutionScopes;
    use crate::types::relocatable::Relocatable;
    use crate::utils::test_utils::*;
    use crate::vm::vm_core::VirtualMachine;

    #[fixture]
    fn simple_bootloader_input() -> SimpleBootloaderInput {
        SimpleBootloaderInput {
            fact_topologies_path: None,
            single_page: false,
            tasks: vec![Task {}, Task {}],
        }
    }

    #[rstest]
    fn test_prepare_task_range_checks(simple_bootloader_input: SimpleBootloaderInput) {
        let mut vm = vm!();
        vm.run_context.fp = 3;
        vm.segments = segments![((1, 0), (2, 0)), ((1, 1), (2, 2))];
        let ids_data = ids_data!["output_ptr", "range_check_ptr", "task_range_check_ptr"];
        vm.add_memory_segment();

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(
            vars::SIMPLE_BOOTLOADER_INPUT,
            simple_bootloader_input.clone(),
        );

        let ap_tracking = ApTracking::new();

        prepare_task_range_checks(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        let task_range_check_ptr =
            get_ptr_from_var_name("task_range_check_ptr", &mut vm, &ids_data, &ap_tracking)
                .unwrap();

        // Assert *output_ptr == n_tasks
        let output = vm
            .segments
            .memory
            .get_integer(Relocatable {
                segment_index: 2,
                offset: 0,
            })
            .unwrap()
            .to_usize()
            .unwrap();
        assert_eq!(output, simple_bootloader_input.tasks.len());

        // Assert task_range_check_ptr == range_check_ptr (2, 2) + BUILTIN_DATA_SIZE (8) * n_tasks (2)
        assert_eq!(
            task_range_check_ptr,
            Relocatable {
                segment_index: 2,
                offset: 18
            }
        );

        let fact_topologies: Vec<FactTopology> = exec_scopes
            .get(vars::FACT_TOPOLOGIES)
            .expect("Fact topologies missing from scope");
        assert!(fact_topologies.is_empty());
    }
}
