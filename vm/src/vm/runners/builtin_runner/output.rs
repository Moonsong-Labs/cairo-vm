use crate::stdlib::{collections::HashMap, prelude::*};
use crate::types::relocatable::{MaybeRelocatable, Relocatable};
use crate::vm::errors::memory_errors::MemoryError;
use crate::vm::errors::runner_errors::RunnerError;
use crate::vm::runners::cairo_pie::{
    BuiltinAdditionalData, OutputBuiltinAdditionalData, Pages, PublicMemoryPage,
};
use crate::vm::vm_core::VirtualMachine;
use crate::vm::vm_memory::memory::Memory;
use crate::vm::vm_memory::memory_segments::MemorySegmentManager;

use super::OUTPUT_BUILTIN_NAME;

#[derive(Debug, Clone)]
pub struct OutputBuiltinRunner {
    base: usize,
    pub(crate) pages: Pages,
    pub(crate) stop_ptr: Option<usize>,
    pub(crate) included: bool,
}

impl OutputBuiltinRunner {
    pub fn new(included: bool) -> OutputBuiltinRunner {
        OutputBuiltinRunner {
            base: 0,
            pages: HashMap::default(),
            stop_ptr: None,
            included,
        }
    }

    pub fn from_segment(segment: &Relocatable, included: bool) -> Self {
        Self {
            base: segment.segment_index as usize,
            pages: HashMap::default(),
            stop_ptr: None,
            included,
        }
    }

    pub fn initialize_segments(&mut self, segments: &mut MemorySegmentManager) {
        self.base = segments.add().segment_index as usize // segments.add() always returns a positive index
    }

    pub fn initial_stack(&self) -> Vec<MaybeRelocatable> {
        if self.included {
            vec![MaybeRelocatable::from((self.base as isize, 0))]
        } else {
            vec![]
        }
    }

    pub fn base(&self) -> usize {
        self.base
    }

    pub fn add_validation_rule(&self, _memory: &mut Memory) {}

    pub fn deduce_memory_cell(
        &self,
        _address: Relocatable,
        _memory: &Memory,
    ) -> Result<Option<MaybeRelocatable>, RunnerError> {
        Ok(None)
    }

    pub fn get_allocated_memory_units(&self, _vm: &VirtualMachine) -> Result<usize, MemoryError> {
        Ok(0)
    }

    pub fn get_memory_segment_addresses(&self) -> (usize, Option<usize>) {
        (self.base, self.stop_ptr)
    }

    pub fn get_used_cells(&self, segments: &MemorySegmentManager) -> Result<usize, MemoryError> {
        segments
            .get_segment_used_size(self.base)
            .ok_or(MemoryError::MissingSegmentUsedSizes)
    }

    pub fn get_used_instances(
        &self,
        segments: &MemorySegmentManager,
    ) -> Result<usize, MemoryError> {
        self.get_used_cells(segments)
    }

    pub fn final_stack(
        &mut self,
        segments: &MemorySegmentManager,
        pointer: Relocatable,
    ) -> Result<Relocatable, RunnerError> {
        if self.included {
            let stop_pointer_addr = (pointer - 1)
                .map_err(|_| RunnerError::NoStopPointer(Box::new(OUTPUT_BUILTIN_NAME)))?;
            let stop_pointer = segments
                .memory
                .get_relocatable(stop_pointer_addr)
                .map_err(|_| RunnerError::NoStopPointer(Box::new(OUTPUT_BUILTIN_NAME)))?;
            if self.base as isize != stop_pointer.segment_index {
                return Err(RunnerError::InvalidStopPointerIndex(Box::new((
                    OUTPUT_BUILTIN_NAME,
                    stop_pointer,
                    self.base,
                ))));
            }
            let stop_ptr = stop_pointer.offset;
            let used = self.get_used_cells(segments).map_err(RunnerError::Memory)?;
            if stop_ptr != used {
                return Err(RunnerError::InvalidStopPointer(Box::new((
                    OUTPUT_BUILTIN_NAME,
                    Relocatable::from((self.base as isize, used)),
                    Relocatable::from((self.base as isize, stop_ptr)),
                ))));
            }
            self.stop_ptr = Some(stop_ptr);
            Ok(stop_pointer_addr)
        } else {
            self.stop_ptr = Some(0);
            Ok(pointer)
        }
    }

    pub fn get_additional_data(&self) -> BuiltinAdditionalData {
        BuiltinAdditionalData::Output(OutputBuiltinAdditionalData {
            pages: self.pages.clone(),
            attributes: HashMap::default(),
        })
    }

    pub fn add_page(
        &mut self,
        page_id: usize,
        page_start: Relocatable,
        page_size: usize,
    ) -> Result<(), RunnerError> {
        if page_start.segment_index as usize != self.base {
            return Err(RunnerError::PageNotOnSegment(page_start, self.base));
        }

        self.pages.insert(
            page_id,
            PublicMemoryPage {
                start: page_start.offset,
                size: page_size,
            },
        );

        Ok(())
    }
}

impl Default for OutputBuiltinRunner {
    fn default() -> Self {
        Self::new(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::relocatable;
    use crate::stdlib::collections::HashMap;

    use crate::{
        utils::test_utils::*,
        vm::{
            errors::memory_errors::MemoryError, runners::builtin_runner::BuiltinRunner,
            vm_core::VirtualMachine,
        },
    };

    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_instances() {
        let builtin = OutputBuiltinRunner::new(true);

        let mut vm = vm!();
        vm.segments.segment_used_sizes = Some(vec![1]);

        assert_eq!(builtin.get_used_instances(&vm.segments), Ok(1));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack() {
        let mut builtin = OutputBuiltinRunner::new(true);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), (0, 0))
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer).unwrap(),
            Relocatable::from((2, 1))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_error_stop_pointer() {
        let mut builtin = OutputBuiltinRunner::new(true);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), (0, 0))
        ];

        vm.segments.segment_used_sizes = Some(vec![998]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer),
            Err(RunnerError::InvalidStopPointer(Box::new((
                OUTPUT_BUILTIN_NAME,
                relocatable!(0, 998),
                relocatable!(0, 0)
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_error_when_notincluded() {
        let mut builtin = OutputBuiltinRunner::new(false);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), (0, 0))
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer).unwrap(),
            Relocatable::from((2, 2))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_error_non_relocatable() {
        let mut builtin = OutputBuiltinRunner::new(true);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), 2)
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer),
            Err(RunnerError::NoStopPointer(Box::new(OUTPUT_BUILTIN_NAME)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_and_allocated_size_test() {
        let builtin: BuiltinRunner = OutputBuiltinRunner::new(true).into();

        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);

        assert_eq!(
            builtin.get_used_cells_and_allocated_size(&vm),
            Ok((0_usize, 0))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_allocated_memory_units() {
        let builtin = OutputBuiltinRunner::new(true);

        let vm = vm!();

        assert_eq!(builtin.get_allocated_memory_units(&vm), Ok(0));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn initialize_segments_for_output() {
        let mut builtin = OutputBuiltinRunner::new(true);
        let mut segments = MemorySegmentManager::new();
        builtin.initialize_segments(&mut segments);
        assert_eq!(builtin.base, 0);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_initial_stack_for_output_with_base() {
        let mut builtin = OutputBuiltinRunner::new(true);
        builtin.base = 1;
        let initial_stack = builtin.initial_stack();
        assert_eq!(
            initial_stack[0].clone(),
            MaybeRelocatable::RelocatableValue((builtin.base() as isize, 0).into())
        );
        assert_eq!(initial_stack.len(), 1);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_segment_addresses() {
        let builtin = OutputBuiltinRunner::new(true);

        assert_eq!(builtin.get_memory_segment_addresses(), (0, None),);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses_missing_segment_used_sizes() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let vm = vm!();

        assert_eq!(
            builtin.get_memory_accesses(&vm),
            Err(MemoryError::MissingSegmentUsedSizes),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses_empty() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);
        assert_eq!(builtin.get_memory_accesses(&vm), Ok(vec![]));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![4]);
        assert_eq!(
            builtin.get_memory_accesses(&vm),
            Ok(vec![
                (builtin.base() as isize, 0).into(),
                (builtin.base() as isize, 1).into(),
                (builtin.base() as isize, 2).into(),
                (builtin.base() as isize, 3).into(),
            ]),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_missing_segment_used_sizes() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let vm = vm!();

        assert_eq!(
            builtin.get_used_cells(&vm.segments),
            Err(MemoryError::MissingSegmentUsedSizes)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_empty() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);
        assert_eq!(builtin.get_used_cells(&vm.segments), Ok(0));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![4]);
        assert_eq!(builtin.get_used_cells(&vm.segments), Ok(4));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_get_used_instances_missing_segments() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let memory_segment_manager = MemorySegmentManager::new();

        assert_eq!(
            builtin.get_used_instances(&memory_segment_manager),
            Err(MemoryError::MissingSegmentUsedSizes)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_get_used_instances_valid() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let mut memory_segment_manager = MemorySegmentManager::new();
        memory_segment_manager.segment_used_sizes = Some(vec![0]);

        assert_eq!(builtin.get_used_instances(&memory_segment_manager), Ok(0));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_deduce_memory_cell_output_builtin() {
        let builtin = BuiltinRunner::Output(OutputBuiltinRunner::new(true));
        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), 2)
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.deduce_memory_cell(pointer, &vm.segments.memory),
            Ok(None)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_add_validation_rule() {
        let builtin = OutputBuiltinRunner::new(true);
        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), 2)
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);
        builtin.add_validation_rule(&mut vm.segments.memory);
    }

    #[test]
    fn get_additional_info_no_pages_no_attributes() {
        let builtin = OutputBuiltinRunner::new(true);
        assert_eq!(
            builtin.get_additional_data(),
            BuiltinAdditionalData::Output(OutputBuiltinAdditionalData {
                pages: HashMap::default(),
                attributes: HashMap::default()
            })
        )
    }

    #[test]
    fn add_page() {
        let mut builtin = OutputBuiltinRunner::new(true);
        assert_eq!(
            builtin.add_page(
                1,
                Relocatable {
                    segment_index: builtin.base() as isize,
                    offset: 0
                },
                3
            ),
            Ok(())
        );

        assert_eq!(
            builtin.pages,
            HashMap::from([(1, PublicMemoryPage { start: 0, size: 3 }),])
        )
    }

    #[test]
    fn add_page_wrong_segment() {
        let mut builtin = OutputBuiltinRunner::new(true);
        let page_start = Relocatable {
            segment_index: 18,
            offset: 0,
        };

        let result = builtin.add_page(1, page_start.clone(), 3);
        assert!(
            matches!(result, Err(RunnerError::PageNotOnSegment(relocatable, base)) if relocatable == page_start && base == builtin.base())
        )
    }
}
