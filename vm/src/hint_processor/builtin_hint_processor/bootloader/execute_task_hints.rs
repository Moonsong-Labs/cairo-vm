use crate::hint_processor::builtin_hint_processor::bootloader::fact_topologies::{
    get_program_task_fact_topology, FactTopology,
};
use num_traits::ToPrimitive;
use std::collections::HashMap;

use crate::hint_processor::builtin_hint_processor::bootloader::program_loader::ProgramLoader;
use crate::hint_processor::builtin_hint_processor::bootloader::types::{BootloaderVersion, Task};
use crate::hint_processor::builtin_hint_processor::bootloader::vars;
use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_ptr_from_var_name, get_relocatable_from_var_name, insert_value_from_var_name,
};
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::ApTracking;
use crate::types::errors::math_errors::MathError;
use crate::types::exec_scope::ExecutionScopes;
use crate::types::relocatable::Relocatable;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::runners::cairo_pie::OutputBuiltinAdditionalData;
use crate::vm::vm_core::VirtualMachine;

/// Implements %{ ids.program_data_ptr = program_data_base = segments.add() %}.
///
/// Creates a new segment to store the program data.
pub fn allocate_program_data_segment(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_data_segment = vm.add_memory_segment();
    exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_data_segment.clone());
    insert_value_from_var_name(
        "program_data_ptr",
        program_data_segment,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

/// Implements
///
/// from starkware.cairo.bootloaders.simple_bootloader.utils import load_program
///
/// # Call load_program to load the program header and code to memory.
/// program_address, program_data_size = load_program(
///     task=task, memory=memory, program_header=ids.program_header,
///     builtins_offset=ids.ProgramHeader.builtin_list)
/// segments.finalize(program_data_base.segment_index, program_data_size)
pub fn load_program_hint(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_data_base: Relocatable = exec_scopes.get(vars::PROGRAM_DATA_BASE)?;
    let task: Task = exec_scopes.get(vars::TASK)?;
    let program = task.get_program();

    let program_header_ptr = get_ptr_from_var_name("program_header", vm, ids_data, ap_tracking)?;

    // Offset of the builtin_list field in `ProgramHeader`, cf. execute_task.cairo
    let builtins_offset = 4;
    let mut program_loader = ProgramLoader::new(&mut vm.segments.memory, builtins_offset);
    let bootloader_version: BootloaderVersion = 0;
    let loaded_program = program_loader
        .load_program(&program_header_ptr, program, Some(bootloader_version))
        .map_err(Into::<HintError>::into)?;

    vm.segments.finalize(
        Some(loaded_program.size),
        program_data_base.segment_index as usize,
        None,
    );

    exec_scopes.insert_value(vars::PROGRAM_ADDRESS, loaded_program.code_address);

    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.simple_bootloader.utils import get_task_fact_topology
///
/// # Add the fact topology of the current task to 'fact_topologies'.
/// output_start = ids.pre_execution_builtin_ptrs.output
/// output_end = ids.return_builtin_ptrs.output
/// fact_topologies.append(get_task_fact_topology(
///     output_size=output_end - output_start,
///     task=task,
///     output_builtin=output_builtin,
///     output_runner_data=output_runner_data,
/// ))
pub fn append_fact_topologies(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;
    let output_runner_data: OutputBuiltinAdditionalData =
        exec_scopes.get(vars::OUTPUT_RUNNER_DATA)?;
    let fact_topologies: &mut Vec<FactTopology> = exec_scopes.get_mut_ref(vars::FACT_TOPOLOGIES)?;

    let pre_execution_builtin_ptrs_addr =
        get_relocatable_from_var_name("pre_execution_builtin_ptrs", vm, ids_data, ap_tracking)?;
    let return_builtin_ptrs_addr =
        get_relocatable_from_var_name("return_builtin_ptrs", vm, ids_data, ap_tracking)?;

    // The output field is the first one in the BuiltinData struct
    let output_start = vm
        .get_integer(pre_execution_builtin_ptrs_addr)?
        .into_owned();
    let output_end = vm.get_integer(return_builtin_ptrs_addr)?.into_owned();
    let output_size = {
        let output_size_felt = output_end - output_start;
        output_size_felt
            .to_usize()
            .ok_or(MathError::Felt252ToUsizeConversion(Box::new(
                output_size_felt,
            )))
    }?;

    let output_builtin = vm.get_output_builtin()?;
    let fact_topology =
        get_program_task_fact_topology(output_size, &task, output_builtin, output_runner_data)
            .map_err(Into::<HintError>::into)?;
    fact_topologies.push(fact_topology);

    Ok(())
}

#[cfg(test)]
mod tests {
    use rstest::{fixture, rstest};

    use crate::hint_processor::builtin_hint_processor::hint_utils::get_ptr_from_var_name;
    use crate::types::relocatable::Relocatable;
    use crate::utils::test_utils::*;
    use crate::vm::runners::builtin_runner::{BuiltinRunner, OutputBuiltinRunner};
    use crate::vm::runners::cairo_pie::{BuiltinAdditionalData, PublicMemoryPage};

    use super::*;

    #[rstest]
    fn test_allocate_program_data_segment() {
        let mut vm = vm!();
        // Allocate space for program_data_ptr
        vm.run_context.fp = 1;
        add_segments!(vm, 2);
        let ids_data = ids_data!["program_data_ptr"];
        let expected_program_data_segment_index = vm.segments.num_segments();

        let mut exec_scopes = ExecutionScopes::new();
        let ap_tracking = ApTracking::new();

        allocate_program_data_segment(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        let program_data_ptr =
            get_ptr_from_var_name("program_data_ptr", &mut vm, &ids_data, &ap_tracking)
                .expect("program_data_ptr is not set");

        let program_data_base: Relocatable = exec_scopes
            .get(vars::PROGRAM_DATA_BASE)
            .expect(format!("{} is not set", vars::PROGRAM_DATA_BASE).as_ref());

        assert_eq!(program_data_ptr, program_data_base);
        // Check that we allocated a new segment and that the pointers point to it
        assert_eq!(
            vm.segments.num_segments(),
            expected_program_data_segment_index + 1
        );
        assert_eq!(
            program_data_ptr,
            Relocatable {
                segment_index: expected_program_data_segment_index as isize,
                offset: 0
            }
        );
    }

    #[fixture]
    fn fibonacci() -> Program {
        let program_content =
            include_bytes!("../../../../../cairo_programs/fibonacci.json").to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    #[rstest]
    fn test_load_program(fibonacci: Program) {
        let task = Task {
            program: fibonacci.clone(),
        };

        let mut vm = vm!();
        vm.run_context.fp = 1;
        // Set program_header_ptr to (2, 0)
        vm.segments = segments![((1, 0), (2, 0))];
        let program_header_ptr = Relocatable::from((2, 0));
        add_segments!(vm, 1);

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_header_ptr.clone());
        exec_scopes.insert_value(vars::TASK, task);

        let ids_data = ids_data!["program_header"];
        let ap_tracking = ApTracking::new();

        load_program_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Note that we do not check the loaded content in memory here, this is tested
        // in `program_loader.rs`

        // The Fibonacci program has no builtins -> the header size is 4
        let header_size = 4;
        let expected_code_address = &program_header_ptr + header_size;

        let program_address: Relocatable = exec_scopes.get(vars::PROGRAM_ADDRESS).unwrap();
        assert_eq!(program_address, expected_code_address);

        // Check that the segment was finalized
        let expected_program_size = header_size + fibonacci.shared_program_data.data.len();
        assert_eq!(
            vm.segments.segment_sizes[&(program_address.segment_index as usize)],
            expected_program_size
        );
    }

    #[rstest]
    fn test_append_fact_topologies(fibonacci: Program) {
        let task = Task {
            program: fibonacci.clone(),
        };

        let mut vm = vm!();

        // Allocate space for the pre-execution and return builtin structs (2 x 8 felts).
        // The pre-execution struct starts at (1, 0) and the return struct at (1, 8).
        // We only set the output values to 0 and 10, respectively, to get an output size of 10.
        vm.segments = segments![((1, 0), 0), ((1, 8), 10),];
        vm.run_context.fp = 16;
        add_segments!(vm, 1);

        let tree_structure = vec![1, 2, 3, 4];
        let program_output_data = OutputBuiltinAdditionalData {
            base: 0,
            pages: HashMap::from([
                (1, PublicMemoryPage { start: 0, size: 7 }),
                (2, PublicMemoryPage { start: 7, size: 3 }),
            ]),
            attributes: HashMap::from([("gps_fact_topology".to_string(), tree_structure.clone())]),
        };
        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.set_state(program_output_data.clone());
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin));

        let ids_data = non_continuous_ids_data![
            ("pre_execution_builtin_ptrs", -16),
            ("return_builtin_ptrs", -8),
        ];

        let ap_tracking = ApTracking::new();

        let mut exec_scopes = ExecutionScopes::new();

        let output_runner_data = OutputBuiltinAdditionalData {
            base: 0,
            pages: HashMap::new(),
            attributes: HashMap::new(),
        };
        exec_scopes.insert_value(vars::OUTPUT_RUNNER_DATA, output_runner_data.clone());
        exec_scopes.insert_value(vars::TASK, task);
        exec_scopes.insert_value(vars::FACT_TOPOLOGIES, Vec::<FactTopology>::new());

        append_fact_topologies(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that the fact topology matches the data from the output builtin
        let fact_topologies: Vec<FactTopology> = exec_scopes.get(vars::FACT_TOPOLOGIES).unwrap();
        assert_eq!(fact_topologies.len(), 1);

        let fact_topology = &fact_topologies[0];
        assert_eq!(fact_topology.page_sizes, vec![0, 7, 3]);
        assert_eq!(fact_topology.tree_structure, tree_structure);

        // Check that the output builtin was updated
        let output_builtin_additional_data = vm.get_output_builtin().unwrap().get_additional_data();
        assert!(matches!(
            output_builtin_additional_data,
            BuiltinAdditionalData::Output(data) if data == output_runner_data,
        ));
    }
}
