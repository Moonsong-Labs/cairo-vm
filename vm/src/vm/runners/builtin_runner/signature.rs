use crate::air_private_input::{PrivateInput, PrivateInputSignature, SignatureInput};
use crate::math_utils::div_mod;
use crate::stdlib::{cell::RefCell, collections::HashMap, prelude::*, rc::Rc};

use crate::types::errors::math_errors::MathError;
use crate::types::instance_definitions::ecdsa_instance_def::CELLS_PER_SIGNATURE;
use crate::vm::runners::cairo_pie::{BuiltinAdditionalData, SignatureBuiltinAdditionalData};
use crate::Felt252;
use crate::{
    types::{
        instance_definitions::ecdsa_instance_def::EcdsaInstanceDef,
        relocatable::{MaybeRelocatable, Relocatable},
    },
    vm::{
        errors::{memory_errors::MemoryError, runner_errors::RunnerError},
        vm_memory::{
            memory::{Memory, ValidationRule},
            memory_segments::MemorySegmentManager,
        },
    },
};
use lazy_static::lazy_static;
use num_bigint::{BigInt, Sign};
use num_integer::div_ceil;
use num_traits::{Num, One};
use starknet_crypto::{verify, FieldElement, Signature};

lazy_static! {
    static ref EC_ORDER: BigInt = BigInt::from_str_radix(
        "3618502788666131213697322783095070105526743751716087489154079457884512865583",
        10
    )
    .unwrap();
}

use super::SIGNATURE_BUILTIN_NAME;

#[derive(Debug, Clone)]
pub struct SignatureBuiltinRunner {
    pub(crate) included: bool,
    ratio: Option<u32>,
    base: usize,
    pub(crate) cells_per_instance: u32,
    pub(crate) n_input_cells: u32,
    _total_n_bits: u32,
    pub(crate) stop_ptr: Option<usize>,
    pub(crate) instances_per_component: u32,
    signatures: Rc<RefCell<HashMap<Relocatable, Signature>>>,
}

impl SignatureBuiltinRunner {
    pub(crate) fn new(instance_def: &EcdsaInstanceDef, included: bool) -> Self {
        SignatureBuiltinRunner {
            base: 0,
            included,
            ratio: instance_def.ratio,
            cells_per_instance: 2,
            n_input_cells: 2,
            _total_n_bits: 251,
            stop_ptr: None,
            instances_per_component: 1,
            signatures: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn add_signature(
        &mut self,
        relocatable: Relocatable,
        (r, s): &(Felt252, Felt252),
    ) -> Result<(), MemoryError> {
        let r_be_bytes = r.to_bytes_be();
        let s_be_bytes = s.to_bytes_be();
        let (r_felt, s_felt) = (
            FieldElement::from_bytes_be(&r_be_bytes).map_err(|_| MathError::ByteConversionError)?,
            FieldElement::from_bytes_be(&s_be_bytes).map_err(|_| MathError::ByteConversionError)?,
        );

        let signature = Signature {
            r: r_felt,
            s: s_felt,
        };

        self.signatures
            .borrow_mut()
            .entry(relocatable)
            .or_insert(signature);

        Ok(())
    }
}

impl SignatureBuiltinRunner {
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
    pub fn add_validation_rule(&self, memory: &mut Memory) {
        let cells_per_instance = self.cells_per_instance;
        let signatures = Rc::clone(&self.signatures);
        let rule: ValidationRule = ValidationRule(Box::new(
            move |memory: &Memory, addr: Relocatable| -> Result<Vec<Relocatable>, MemoryError> {
                let cell_index = addr.offset % cells_per_instance as usize;

                let (pubkey_addr, message_addr) = match cell_index {
                    0 => (addr, (addr + 1)?),
                    1 => match addr - 1 {
                        Ok(prev_addr) => (prev_addr, addr),
                        Err(_) => return Ok(vec![]),
                    },
                    _ => return Ok(vec![]),
                };

                let pubkey = match memory.get_integer(pubkey_addr) {
                    Ok(num) => num,
                    Err(_) if cell_index == 1 => return Ok(vec![]),
                    _ => return Err(MemoryError::PubKeyNonInt(Box::new(pubkey_addr))),
                };

                let msg = match memory.get_integer(message_addr) {
                    Ok(num) => num,
                    Err(_) if cell_index == 0 => return Ok(vec![]),
                    _ => return Err(MemoryError::MsgNonInt(Box::new(message_addr))),
                };

                let signatures_map = signatures.borrow();
                let signature = signatures_map
                    .get(&pubkey_addr)
                    .ok_or_else(|| MemoryError::SignatureNotFound(Box::new(pubkey_addr)))?;

                let public_key = FieldElement::from_bytes_be(&pubkey.to_bytes_be())
                    .map_err(|_| MathError::ByteConversionError)?;
                let (r, s) = (signature.r, signature.s);
                let message = FieldElement::from_bytes_be(&msg.to_bytes_be())
                    .map_err(|_| MathError::ByteConversionError)?;
                match verify(&public_key, &message, &r, &s) {
                    Ok(true) => Ok(vec![]),
                    _ => Err(MemoryError::InvalidSignature(Box::new((
                        format!("({}, {})", signature.r, signature.s),
                        pubkey.into_owned(),
                        msg.into_owned(),
                    )))),
                }
            },
        ));
        memory.add_validation_rule(self.base, rule);
    }

    pub fn deduce_memory_cell(
        &self,
        _address: Relocatable,
        _memory: &Memory,
    ) -> Result<Option<MaybeRelocatable>, RunnerError> {
        Ok(None)
    }

    pub fn ratio(&self) -> Option<u32> {
        self.ratio
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
        let used_cells = self.get_used_cells(segments)?;
        Ok(div_ceil(used_cells, self.cells_per_instance as usize))
    }

    pub fn final_stack(
        &mut self,
        segments: &MemorySegmentManager,
        pointer: Relocatable,
    ) -> Result<Relocatable, RunnerError> {
        if self.included {
            let stop_pointer_addr = (pointer - 1)
                .map_err(|_| RunnerError::NoStopPointer(Box::new(SIGNATURE_BUILTIN_NAME)))?;
            let stop_pointer = segments
                .memory
                .get_relocatable(stop_pointer_addr)
                .map_err(|_| RunnerError::NoStopPointer(Box::new(SIGNATURE_BUILTIN_NAME)))?;
            if self.base as isize != stop_pointer.segment_index {
                return Err(RunnerError::InvalidStopPointerIndex(Box::new((
                    SIGNATURE_BUILTIN_NAME,
                    stop_pointer,
                    self.base,
                ))));
            }
            let stop_ptr = stop_pointer.offset;
            let num_instances = self.get_used_instances(segments)?;
            let used = num_instances * self.cells_per_instance as usize;
            if stop_ptr != used {
                return Err(RunnerError::InvalidStopPointer(Box::new((
                    SIGNATURE_BUILTIN_NAME,
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
        // Convert signatures to Felt tuple
        let signatures: HashMap<Relocatable, (Felt252, Felt252)> = self
            .signatures
            .borrow()
            .iter()
            .map(|(k, v)| {
                (
                    *k,
                    (
                        Felt252::from_bytes_be(&v.r.to_bytes_be()),
                        Felt252::from_bytes_be(&v.s.to_bytes_be()),
                    ),
                )
            })
            .collect();
        BuiltinAdditionalData::Signature(SignatureBuiltinAdditionalData(signatures))
    }

    pub fn air_private_input(&self, memory: &Memory) -> Vec<PrivateInput> {
        let mut private_inputs = vec![];
        for (addr, signature) in self.signatures.borrow().iter() {
            if let (Ok(pubkey), Ok(msg)) = (memory.get_integer(*addr), memory.get_integer(addr + 1))
            {
                private_inputs.push(PrivateInput::Signature(PrivateInputSignature {
                    index: addr
                        .offset
                        .saturating_sub(self.base)
                        .checked_div(CELLS_PER_SIGNATURE as usize)
                        .unwrap_or_default(),
                    pubkey: *pubkey,
                    msg: *msg,
                    signature_input: SignatureInput {
                        r: Felt252::from_bytes_be(&signature.r.to_bytes_be()),
                        w: Felt252::from(
                            &div_mod(
                                &BigInt::one(),
                                &BigInt::from_bytes_be(Sign::Plus, &signature.s.to_bytes_be()),
                                &EC_ORDER,
                            )
                            .unwrap_or_default(),
                        ),
                    },
                }))
            }
        }
        private_inputs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        relocatable,
        types::instance_definitions::ecdsa_instance_def::EcdsaInstanceDef,
        utils::test_utils::*,
        vm::{
            errors::memory_errors::{InsufficientAllocatedCellsError, MemoryError},
            runners::builtin_runner::BuiltinRunner,
            vm_core::VirtualMachine,
            vm_memory::{memory::Memory, memory_segments::MemorySegmentManager},
        },
    };

    use crate::felt_str;
    use crate::vm::runners::cairo_pie::SignatureBuiltinAdditionalData;
    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    fn get_used_cells_and_allocated_size_valid() {
        let builtin: BuiltinRunner =
            SignatureBuiltinRunner::new(&EcdsaInstanceDef::new(Some(10)), true).into();
        let mut vm = vm!();
        vm.current_step = 110;
        vm.segments.segment_used_sizes = Some(vec![1]);
        assert_eq!(builtin.get_used_cells_and_allocated_size(&vm), Ok((1, 22)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn initialize_segments_for_ecdsa() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        let mut segments = MemorySegmentManager::new();
        builtin.initialize_segments(&mut segments);
        assert_eq!(builtin.base, 0);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_instances() {
        let builtin: BuiltinRunner =
            SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true).into();

        let mut vm = vm!();
        vm.segments.segment_used_sizes = Some(vec![1]);

        assert_eq!(builtin.get_used_instances(&vm.segments), Ok(1));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);

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
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);

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
                SIGNATURE_BUILTIN_NAME,
                relocatable!(0, 998),
                relocatable!(0, 0)
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_error_non_relocatable() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);

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
            Err(RunnerError::NoStopPointer(Box::new(SIGNATURE_BUILTIN_NAME)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_segment_addresses() {
        let builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);

        assert_eq!(builtin.get_memory_segment_addresses(), (0, None));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses_missing_segment_used_sizes() {
        let builtin = BuiltinRunner::Signature(SignatureBuiltinRunner::new(
            &EcdsaInstanceDef::default(),
            true,
        ));
        let vm = vm!();

        assert_eq!(
            builtin.get_memory_accesses(&vm),
            Err(MemoryError::MissingSegmentUsedSizes),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses_empty() {
        let builtin = BuiltinRunner::Signature(SignatureBuiltinRunner::new(
            &EcdsaInstanceDef::default(),
            true,
        ));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);
        assert_eq!(builtin.get_memory_accesses(&vm), Ok(vec![]));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses() {
        let builtin = BuiltinRunner::Signature(SignatureBuiltinRunner::new(
            &EcdsaInstanceDef::default(),
            true,
        ));
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
        let builtin = BuiltinRunner::Signature(SignatureBuiltinRunner::new(
            &EcdsaInstanceDef::default(),
            true,
        ));
        let vm = vm!();

        assert_eq!(
            builtin.get_used_cells(&vm.segments),
            Err(MemoryError::MissingSegmentUsedSizes)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_empty() {
        let builtin = BuiltinRunner::Signature(SignatureBuiltinRunner::new(
            &EcdsaInstanceDef::default(),
            true,
        ));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);
        assert_eq!(builtin.get_used_cells(&vm.segments), Ok(0));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells() {
        let builtin = BuiltinRunner::Signature(SignatureBuiltinRunner::new(
            &EcdsaInstanceDef::default(),
            true,
        ));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![4]);
        assert_eq!(builtin.get_used_cells(&vm.segments), Ok(4));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_initial_stack_for_range_check_with_base() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
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
    fn initial_stack_not_included_test() {
        let ecdsa_builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), false);
        assert_eq!(ecdsa_builtin.initial_stack(), Vec::new())
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_memory_cell_test() {
        let memory = Memory::new();
        let builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        let result = builtin.deduce_memory_cell(Relocatable::from((0, 5)), &memory);
        assert_eq!(result, Ok(None));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_ratio() {
        let builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        assert_eq!(builtin.ratio(), Some(512));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_base() {
        let builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        assert_eq!(builtin.base(), 0);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_get_memory_segment_addresses() {
        let builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);

        assert_eq!(builtin.get_memory_segment_addresses(), (0, None));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_memory_cell() {
        let memory = Memory::new();
        let builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        let result = builtin.deduce_memory_cell(Relocatable::from((0, 5)), &memory);
        assert_eq!(result, Ok(None));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_allocated_memory_min_step_not_reached() {
        let builtin: BuiltinRunner =
            SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true).into();
        let mut vm = vm!();
        vm.current_step = 500;
        assert_eq!(
            builtin.get_allocated_memory_units(&vm),
            Err(MemoryError::InsufficientAllocatedCells(
                InsufficientAllocatedCellsError::MinStepNotReached(Box::new((
                    512,
                    SIGNATURE_BUILTIN_NAME
                )))
            ))
        )
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_and_allocated_size_insufficient_allocated() {
        let builtin: BuiltinRunner =
            SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true).into();
        let mut vm = vm!();
        vm.segments.segment_used_sizes = Some(vec![50]);
        vm.current_step = 512;
        assert_eq!(
            builtin.get_used_cells_and_allocated_size(&vm),
            Err(MemoryError::InsufficientAllocatedCells(
                InsufficientAllocatedCellsError::BuiltinCells(Box::new((
                    SIGNATURE_BUILTIN_NAME,
                    50,
                    2
                )))
            ))
        )
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_invalid_stop_pointer() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        let mut vm = vm!();
        vm.segments = segments![((0, 0), (1, 0))];
        assert_eq!(
            builtin.final_stack(&vm.segments, (0, 1).into()),
            Err(RunnerError::InvalidStopPointerIndex(Box::new((
                SIGNATURE_BUILTIN_NAME,
                relocatable!(1, 0),
                0
            ))))
        )
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_no_used_instances() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        let mut vm = vm!();
        vm.segments = segments![((0, 0), (0, 0))];
        assert_eq!(
            builtin.final_stack(&vm.segments, (0, 1).into()),
            Err(RunnerError::Memory(MemoryError::MissingSegmentUsedSizes))
        )
    }

    #[test]
    fn get_additional_info() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        let signatures = HashMap::from([(
            Relocatable::from((4, 0)),
            Signature {
                r: FieldElement::from_dec_str("45678").unwrap(),
                s: FieldElement::from_dec_str("1239").unwrap(),
            },
        )]);
        builtin.signatures = Rc::new(RefCell::new(signatures));
        let signatures = HashMap::from([(
            Relocatable::from((4, 0)),
            (felt_str!("45678"), felt_str!("1239")),
        )]);
        assert_eq!(
            builtin.get_additional_data(),
            BuiltinAdditionalData::Signature(SignatureBuiltinAdditionalData(signatures))
        )
    }
}
