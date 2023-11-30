use crate::stdlib::{any::Any, borrow::Cow, collections::HashMap, prelude::*};

use crate::{
    hint_processor::hint_processor_definition::HintProcessor,
    types::{
        errors::math_errors::MathError,
        exec_scope::ExecutionScopes,
        instruction::{
            is_call_instruction, ApUpdate, FpUpdate, Instruction, Opcode, PcUpdate, Res,
        },
        relocatable::{MaybeRelocatable, Relocatable},
    },
    vm::{
        context::run_context::RunContext,
        decoding::decoder::decode_instruction,
        errors::{
            exec_scope_errors::ExecScopeError, memory_errors::MemoryError,
            vm_errors::VirtualMachineError,
        },
        runners::builtin_runner::{BuiltinRunner, RangeCheckBuiltinRunner, SignatureBuiltinRunner},
        trace::trace_entry::TraceEntry,
        vm_memory::memory_segments::MemorySegmentManager,
    },
};

use core::cmp::Ordering;
use felt::Felt252;
use num_traits::{ToPrimitive, Zero};

use super::errors::runner_errors::RunnerError;
use super::errors::trace_errors::TraceError;
use super::runners::builtin_runner::{OutputBuiltinRunner, OUTPUT_BUILTIN_NAME};

const MAX_TRACEBACK_ENTRIES: u32 = 20;

#[derive(PartialEq, Eq, Debug)]
pub struct Operands {
    dst: MaybeRelocatable,
    res: Option<MaybeRelocatable>,
    op0: MaybeRelocatable,
    op1: MaybeRelocatable,
}

#[derive(PartialEq, Eq, Debug)]
pub struct OperandsAddresses {
    dst_addr: Relocatable,
    op0_addr: Relocatable,
    op1_addr: Relocatable,
}

#[derive(Default, Debug, Clone, Copy)]
pub struct DeducedOperands(u8);

impl DeducedOperands {
    fn set_dst(&mut self, value: bool) {
        self.0 |= value as u8;
    }
    fn set_op0(&mut self, value: bool) {
        self.0 |= (value as u8) << 1;
    }
    fn set_op1(&mut self, value: bool) {
        self.0 |= (value as u8) << 2;
    }

    fn was_dest_deducted(&self) -> bool {
        self.0 & 1 != 0
    }
    fn was_op0_deducted(&self) -> bool {
        self.0 & 1 << 1 != 0
    }
    fn was_op1_deducted(&self) -> bool {
        self.0 & 1 << 2 != 0
    }
}

pub struct VirtualMachine {
    pub(crate) run_context: RunContext,
    pub(crate) builtin_runners: Vec<BuiltinRunner>,
    pub(crate) segments: MemorySegmentManager,
    pub(crate) trace: Option<Vec<TraceEntry>>,
    pub(crate) current_step: usize,
    pub(crate) rc_limits: Option<(isize, isize)>,
    trace_relocated: bool,
    skip_instruction_execution: bool,
    run_finished: bool,
    instruction_cache: Vec<Option<Instruction>>,
    #[cfg(feature = "hooks")]
    pub(crate) hooks: crate::vm::hooks::Hooks,
    pub(crate) relocation_table: Option<Vec<usize>>,
}

impl VirtualMachine {
    pub fn new(trace_enabled: bool) -> VirtualMachine {
        let run_context = RunContext {
            pc: Relocatable::from((0, 0)),
            ap: 0,
            fp: 0,
        };

        let trace = if trace_enabled {
            Some(Vec::<TraceEntry>::new())
        } else {
            None
        };

        VirtualMachine {
            run_context,
            builtin_runners: Vec::new(),
            trace,
            current_step: 0,
            skip_instruction_execution: false,
            segments: MemorySegmentManager::new(),
            rc_limits: None,
            run_finished: false,
            trace_relocated: false,
            instruction_cache: Vec::new(),
            #[cfg(feature = "hooks")]
            hooks: Default::default(),
            relocation_table: None,
        }
    }

    pub fn compute_segments_effective_sizes(&mut self) {
        self.segments.compute_effective_sizes();
    }

    fn update_fp(
        &mut self,
        instruction: &Instruction,
        operands: &Operands,
    ) -> Result<(), VirtualMachineError> {
        let new_fp_offset: usize = match instruction.fp_update {
            FpUpdate::APPlus2 => self.run_context.ap + 2,
            FpUpdate::Dst => match operands.dst {
                MaybeRelocatable::RelocatableValue(ref rel) => rel.offset,
                MaybeRelocatable::Int(ref num) => num
                    .to_usize()
                    .ok_or_else(|| MathError::Felt252ToUsizeConversion(Box::new(num.clone())))?,
            },
            FpUpdate::Regular => return Ok(()),
        };
        self.run_context.fp = new_fp_offset;
        Ok(())
    }

    fn update_ap(
        &mut self,
        instruction: &Instruction,
        operands: &Operands,
    ) -> Result<(), VirtualMachineError> {
        let new_apset: usize = match instruction.ap_update {
            ApUpdate::Add => match &operands.res {
                Some(res) => (self.run_context.get_ap() + res)?.offset,
                None => return Err(VirtualMachineError::UnconstrainedResAdd),
            },
            ApUpdate::Add1 => self.run_context.ap + 1,
            ApUpdate::Add2 => self.run_context.ap + 2,
            ApUpdate::Regular => return Ok(()),
        };
        self.run_context.ap = new_apset;
        Ok(())
    }

    fn update_pc(
        &mut self,
        instruction: &Instruction,
        operands: &Operands,
    ) -> Result<(), VirtualMachineError> {
        let new_pc: Relocatable = match instruction.pc_update {
            PcUpdate::Regular => (self.run_context.pc + instruction.size())?,
            PcUpdate::Jump => match operands.res.as_ref().and_then(|x| x.get_relocatable()) {
                Some(ref res) => *res,
                None => return Err(VirtualMachineError::UnconstrainedResJump),
            },
            PcUpdate::JumpRel => match &operands.res {
                Some(res) => match res {
                    MaybeRelocatable::Int(num_res) => (self.run_context.pc + num_res)?,
                    _ => return Err(VirtualMachineError::JumpRelNotInt),
                },
                None => return Err(VirtualMachineError::UnconstrainedResJumpRel),
            },
            PcUpdate::Jnz => match VirtualMachine::is_zero(&operands.dst) {
                true => (self.run_context.pc + instruction.size())?,
                false => (self.run_context.pc + &operands.op1)?,
            },
        };
        self.run_context.pc = new_pc;
        Ok(())
    }

    fn update_registers(
        &mut self,
        instruction: &Instruction,
        operands: Operands,
    ) -> Result<(), VirtualMachineError> {
        self.update_fp(instruction, &operands)?;
        self.update_ap(instruction, &operands)?;
        self.update_pc(instruction, &operands)?;
        Ok(())
    }

    /// Returns true if the value is zero
    /// Used for JNZ instructions
    fn is_zero(addr: &MaybeRelocatable) -> bool {
        match addr {
            MaybeRelocatable::Int(num) => num.is_zero(),
            _ => false,
        }
    }

    ///Returns a tuple (deduced_op0, deduced_res).
    ///Deduces the value of op0 if possible (based on dst and op1). Otherwise, returns None.
    ///If res was already deduced, returns its deduced value as well.
    fn deduce_op0(
        &self,
        instruction: &Instruction,
        dst: Option<&MaybeRelocatable>,
        op1: Option<&MaybeRelocatable>,
    ) -> Result<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError> {
        match instruction.opcode {
            Opcode::Call => Ok((
                Some(MaybeRelocatable::from(
                    (self.run_context.pc + instruction.size())?,
                )),
                None,
            )),
            Opcode::AssertEq => match (&instruction.res, dst, op1) {
                (Res::Add, Some(dst_addr), Some(op1_addr)) => {
                    Ok((Some(dst_addr.sub(op1_addr)?), dst.cloned()))
                }
                (
                    Res::Mul,
                    Some(MaybeRelocatable::Int(num_dst)),
                    Some(MaybeRelocatable::Int(num_op1)),
                ) if !num_op1.is_zero() => {
                    Ok((Some(MaybeRelocatable::Int(num_dst / num_op1)), dst.cloned()))
                }
                _ => Ok((None, None)),
            },
            _ => Ok((None, None)),
        }
    }

    /// Returns a tuple (deduced_op1, deduced_res).
    ///Deduces the value of op1 if possible (based on dst and op0). Otherwise, returns None.
    ///If res was already deduced, returns its deduced value as well.
    fn deduce_op1(
        &self,
        instruction: &Instruction,
        dst: Option<&MaybeRelocatable>,
        op0: Option<MaybeRelocatable>,
    ) -> Result<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError> {
        if let Opcode::AssertEq = instruction.opcode {
            match instruction.res {
                Res::Op1 => return Ok((dst.cloned(), dst.cloned())),
                Res::Add => {
                    return Ok((
                        dst.zip(op0).and_then(|(dst, op0)| dst.sub(&op0).ok()),
                        dst.cloned(),
                    ))
                }
                Res::Mul => match (dst, op0) {
                    (
                        Some(MaybeRelocatable::Int(num_dst)),
                        Some(MaybeRelocatable::Int(num_op0)),
                    ) if !num_op0.is_zero() => {
                        return Ok((Some(MaybeRelocatable::Int(num_dst / num_op0)), dst.cloned()))
                    }
                    _ => (),
                },
                _ => (),
            };
        };
        Ok((None, None))
    }

    fn deduce_memory_cell(
        &self,
        address: Relocatable,
    ) -> Result<Option<MaybeRelocatable>, VirtualMachineError> {
        for builtin in self.builtin_runners.iter() {
            if builtin.base() as isize == address.segment_index {
                match builtin.deduce_memory_cell(address, &self.segments.memory) {
                    Ok(maybe_reloc) => return Ok(maybe_reloc),
                    Err(error) => return Err(VirtualMachineError::RunnerError(error)),
                };
            }
        }
        Ok(None)
    }

    ///Computes the value of res if possible
    fn compute_res(
        &self,
        instruction: &Instruction,
        op0: &MaybeRelocatable,
        op1: &MaybeRelocatable,
    ) -> Result<Option<MaybeRelocatable>, VirtualMachineError> {
        match instruction.res {
            Res::Op1 => Ok(Some(op1.clone())),
            Res::Add => Ok(Some(op0.add(op1)?)),
            Res::Mul => {
                if let (MaybeRelocatable::Int(num_op0), MaybeRelocatable::Int(num_op1)) = (op0, op1)
                {
                    return Ok(Some(MaybeRelocatable::Int(num_op0 * num_op1)));
                }
                Err(VirtualMachineError::ComputeResRelocatableMul(Box::new((
                    op0.clone(),
                    op1.clone(),
                ))))
            }
            Res::Unconstrained => Ok(None),
        }
    }

    fn deduce_dst(
        &self,
        instruction: &Instruction,
        res: &Option<MaybeRelocatable>,
    ) -> Result<MaybeRelocatable, VirtualMachineError> {
        let dst = match (instruction.opcode, res) {
            (Opcode::AssertEq, Some(res)) => res.clone(),
            (Opcode::Call, _) => MaybeRelocatable::from(self.run_context.get_fp()),
            _ => return Err(VirtualMachineError::NoDst),
        };
        Ok(dst)
    }

    fn opcode_assertions(
        &self,
        instruction: &Instruction,
        operands: &Operands,
    ) -> Result<(), VirtualMachineError> {
        match instruction.opcode {
            Opcode::AssertEq => match &operands.res {
                None => Err(VirtualMachineError::UnconstrainedResAssertEq),
                Some(res) if res != &operands.dst => Err(VirtualMachineError::DiffAssertValues(
                    Box::new((operands.dst.clone(), res.clone())),
                )),
                _ => Ok(()),
            },
            Opcode::Call => {
                let return_pc = MaybeRelocatable::from((self.run_context.pc + instruction.size())?);
                if operands.op0 != return_pc {
                    return Err(VirtualMachineError::CantWriteReturnPc(Box::new((
                        operands.op0.clone(),
                        return_pc,
                    ))));
                };

                if MaybeRelocatable::from(self.run_context.get_fp()) != operands.dst {
                    return Err(VirtualMachineError::CantWriteReturnFp(Box::new((
                        operands.dst.clone(),
                        MaybeRelocatable::from(self.run_context.get_fp()),
                    ))));
                };
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn insert_deduced_operands(
        &mut self,
        deduced_operands: DeducedOperands,
        operands: &Operands,
        operands_addresses: &OperandsAddresses,
    ) -> Result<(), VirtualMachineError> {
        if deduced_operands.was_op0_deducted() {
            self.segments
                .memory
                .insert(operands_addresses.op0_addr, &operands.op0)
                .map_err(VirtualMachineError::Memory)?;
        }
        if deduced_operands.was_op1_deducted() {
            self.segments
                .memory
                .insert(operands_addresses.op1_addr, &operands.op1)
                .map_err(VirtualMachineError::Memory)?;
        }
        if deduced_operands.was_dest_deducted() {
            self.segments
                .memory
                .insert(operands_addresses.dst_addr, &operands.dst)
                .map_err(VirtualMachineError::Memory)?;
        }

        Ok(())
    }

    fn run_instruction(&mut self, instruction: &Instruction) -> Result<(), VirtualMachineError> {
        let (operands, operands_addresses, deduced_operands) =
            self.compute_operands(instruction)?;
        self.insert_deduced_operands(deduced_operands, &operands, &operands_addresses)?;
        self.opcode_assertions(instruction, &operands)?;

        if let Some(ref mut trace) = &mut self.trace {
            trace.push(TraceEntry {
                pc: self.run_context.pc.offset,
                ap: self.run_context.ap,
                fp: self.run_context.fp,
            });
        }

        // Update range check limits
        const OFFSET_BITS: u32 = 16;
        let (off0, off1, off2) = (
            instruction.off0 + (1_isize << (OFFSET_BITS - 1)),
            instruction.off1 + (1_isize << (OFFSET_BITS - 1)),
            instruction.off2 + (1_isize << (OFFSET_BITS - 1)),
        );
        let (min, max) = self.rc_limits.unwrap_or((off0, off0));
        self.rc_limits = Some((
            min.min(off0).min(off1).min(off2),
            max.max(off0).max(off1).max(off2),
        ));

        self.segments
            .memory
            .mark_as_accessed(operands_addresses.dst_addr);
        self.segments
            .memory
            .mark_as_accessed(operands_addresses.op0_addr);
        self.segments
            .memory
            .mark_as_accessed(operands_addresses.op1_addr);

        self.update_registers(instruction, operands)?;
        self.current_step += 1;

        Ok(())
    }

    fn decode_current_instruction(&self) -> Result<Instruction, VirtualMachineError> {
        let instruction = self
            .segments
            .memory
            .get_integer(self.run_context.pc)?
            .to_u64()
            .ok_or(VirtualMachineError::InvalidInstructionEncoding)?;
        decode_instruction(instruction)
    }

    pub fn step_hint(
        &mut self,
        hint_executor: &mut dyn HintProcessor,
        exec_scopes: &mut ExecutionScopes,
        hint_data: &[Box<dyn Any>],
        constants: &HashMap<String, Felt252>,
    ) -> Result<(), VirtualMachineError> {
        for (hint_index, hint_data) in hint_data.iter().enumerate() {
            hint_executor
                .execute_hint(self, exec_scopes, hint_data, constants)
                .map_err(|err| VirtualMachineError::Hint(Box::new((hint_index, err))))?
        }
        Ok(())
    }

    pub fn step_instruction(&mut self) -> Result<(), VirtualMachineError> {
        let pc = self.run_context.pc.offset;

        if self.segments.memory.data[0].len() <= pc {
            return Err(MemoryError::UnknownMemoryCell(Box::new((0, pc).into())))?;
        }

        let mut inst_cache = core::mem::take(&mut self.instruction_cache);
        inst_cache.resize((pc + 1).max(inst_cache.len()), None);

        let instruction = inst_cache.get_mut(pc).unwrap();
        if instruction.is_none() {
            *instruction = Some(self.decode_current_instruction()?);
        }
        let instruction = instruction.as_ref().unwrap();
        if !self.skip_instruction_execution {
            self.run_instruction(instruction)?;
        } else {
            self.run_context.pc += instruction.size();
            self.skip_instruction_execution = false;
        }
        self.instruction_cache = inst_cache;
        Ok(())
    }

    pub fn step(
        &mut self,
        hint_executor: &mut dyn HintProcessor,
        exec_scopes: &mut ExecutionScopes,
        hint_data: &[Box<dyn Any>],
        constants: &HashMap<String, Felt252>,
    ) -> Result<(), VirtualMachineError> {
        self.step_hint(hint_executor, exec_scopes, hint_data, constants)?;

        #[cfg(feature = "hooks")]
        self.execute_pre_step_instruction(hint_executor, exec_scopes, hint_data, constants)?;
        self.step_instruction()?;
        #[cfg(feature = "hooks")]
        self.execute_post_step_instruction(hint_executor, exec_scopes, hint_data, constants)?;

        Ok(())
    }

    fn compute_op0_deductions(
        &self,
        op0_addr: Relocatable,
        res: &mut Option<MaybeRelocatable>,
        instruction: &Instruction,
        dst_op: &Option<MaybeRelocatable>,
        op1_op: &Option<MaybeRelocatable>,
    ) -> Result<MaybeRelocatable, VirtualMachineError> {
        let op0_op = match self.deduce_memory_cell(op0_addr)? {
            None => {
                let op0;
                (op0, *res) = self.deduce_op0(instruction, dst_op.as_ref(), op1_op.as_ref())?;
                op0
            }
            deduced_memory_cell => deduced_memory_cell,
        };
        let op0 = op0_op.ok_or_else(|| {
            VirtualMachineError::FailedToComputeOperands(Box::new(("op0".to_string(), op0_addr)))
        })?;
        Ok(op0)
    }

    fn compute_op1_deductions(
        &self,
        op1_addr: Relocatable,
        res: &mut Option<MaybeRelocatable>,
        instruction: &Instruction,
        dst_op: &Option<MaybeRelocatable>,
        op0: &MaybeRelocatable,
    ) -> Result<MaybeRelocatable, VirtualMachineError> {
        let op1_op = match self.deduce_memory_cell(op1_addr)? {
            None => {
                let (op1, deduced_res) =
                    self.deduce_op1(instruction, dst_op.as_ref(), Some(op0.clone()))?;
                if res.is_none() {
                    *res = deduced_res
                }
                op1
            }
            deduced_memory_cell => deduced_memory_cell,
        };
        let op1 = op1_op.ok_or_else(|| {
            VirtualMachineError::FailedToComputeOperands(Box::new(("op1".to_string(), op1_addr)))
        })?;
        Ok(op1)
    }

    /// Compute operands and result, trying to deduce them if normal memory access returns a None
    /// value.
    pub fn compute_operands(
        &self,
        instruction: &Instruction,
    ) -> Result<(Operands, OperandsAddresses, DeducedOperands), VirtualMachineError> {
        //Get operands from memory
        let dst_addr = self.run_context.compute_dst_addr(instruction)?;
        let dst_op = self.segments.memory.get(&dst_addr).map(Cow::into_owned);

        let op0_addr = self.run_context.compute_op0_addr(instruction)?;
        let op0_op = self.segments.memory.get(&op0_addr).map(Cow::into_owned);

        let op1_addr = self
            .run_context
            .compute_op1_addr(instruction, op0_op.as_ref())?;
        let op1_op = self.segments.memory.get(&op1_addr).map(Cow::into_owned);

        let mut res: Option<MaybeRelocatable> = None;

        let mut deduced_operands = DeducedOperands::default();

        //Deduce op0 if it wasnt previously computed
        let op0 = match op0_op {
            Some(op0) => op0,
            None => {
                deduced_operands.set_op0(true);
                self.compute_op0_deductions(op0_addr, &mut res, instruction, &dst_op, &op1_op)?
            }
        };

        //Deduce op1 if it wasnt previously computed
        let op1 = match op1_op {
            Some(op1) => op1,
            None => {
                deduced_operands.set_op1(true);
                self.compute_op1_deductions(op1_addr, &mut res, instruction, &dst_op, &op0)?
            }
        };

        //Compute res if it wasnt previously deduced
        if res.is_none() {
            res = self.compute_res(instruction, &op0, &op1)?;
        }

        //Deduce dst if it wasnt previously computed
        let dst = match dst_op {
            Some(dst) => dst,
            None => {
                deduced_operands.set_dst(true);
                self.deduce_dst(instruction, &res)?
            }
        };
        let accessed_addresses = OperandsAddresses {
            dst_addr,
            op0_addr,
            op1_addr,
        };
        Ok((
            Operands { dst, op0, op1, res },
            accessed_addresses,
            deduced_operands,
        ))
    }

    ///Makes sure that all assigned memory cells are consistent with their auto deduction rules.
    pub fn verify_auto_deductions(&self) -> Result<(), VirtualMachineError> {
        for builtin in self.builtin_runners.iter() {
            let index: usize = builtin.base();
            for (offset, value) in self.segments.memory.data[index].iter().enumerate() {
                if let Some(deduced_memory_cell) = builtin
                    .deduce_memory_cell(
                        Relocatable::from((index as isize, offset)),
                        &self.segments.memory,
                    )
                    .map_err(VirtualMachineError::RunnerError)?
                {
                    let value = value.as_ref().map(|x| x.get_value());
                    if Some(&deduced_memory_cell) != value && value.is_some() {
                        return Err(VirtualMachineError::InconsistentAutoDeduction(Box::new((
                            builtin.name(),
                            deduced_memory_cell,
                            value.cloned(),
                        ))));
                    }
                }
            }
        }
        Ok(())
    }

    //Makes sure that the value at the given address is consistent with the auto deduction rules.
    pub fn verify_auto_deductions_for_addr(
        &self,
        addr: Relocatable,
        builtin: &BuiltinRunner,
    ) -> Result<(), VirtualMachineError> {
        let value = match builtin.deduce_memory_cell(addr, &self.segments.memory)? {
            Some(value) => value,
            None => return Ok(()),
        };
        let current_value = match self.segments.memory.get(&addr) {
            Some(value) => value.into_owned(),
            None => return Ok(()),
        };
        if value != current_value {
            return Err(VirtualMachineError::InconsistentAutoDeduction(Box::new((
                builtin.name(),
                value,
                Some(current_value),
            ))));
        }
        Ok(())
    }

    pub fn end_run(&mut self, exec_scopes: &ExecutionScopes) -> Result<(), VirtualMachineError> {
        self.verify_auto_deductions()?;
        self.run_finished = true;
        match exec_scopes.data.len() {
            1 => Ok(()),
            _ => Err(ExecScopeError::NoScopeError.into()),
        }
    }

    pub fn mark_address_range_as_accessed(
        &mut self,
        base: Relocatable,
        len: usize,
    ) -> Result<(), VirtualMachineError> {
        if !self.run_finished {
            return Err(VirtualMachineError::RunNotFinished);
        }
        for i in 0..len {
            self.segments.memory.mark_as_accessed((base + i)?);
        }
        Ok(())
    }

    // Returns the values (fp, pc) corresponding to each call instruction in the traceback.
    // Returns the most recent call last.
    pub(crate) fn get_traceback_entries(&self) -> Vec<(Relocatable, Relocatable)> {
        let mut entries = Vec::<(Relocatable, Relocatable)>::new();
        let mut fp = Relocatable::from((1, self.run_context.fp));
        // Fetch the fp and pc traceback entries
        for _ in 0..MAX_TRACEBACK_ENTRIES {
            // Get return pc
            let ret_pc = match (fp - 1)
                .ok()
                .map(|r| self.segments.memory.get_relocatable(r))
            {
                Some(Ok(opt_pc)) => opt_pc,
                _ => break,
            };
            // Get fp traceback
            match (fp - 2)
                .ok()
                .map(|r| self.segments.memory.get_relocatable(r))
            {
                Some(Ok(opt_fp)) if opt_fp != fp => fp = opt_fp,
                _ => break,
            }
            // Try to check if the call instruction is (instruction0, instruction1) or just
            // instruction1 (with no immediate).
            let call_pc = match (ret_pc - 1)
                .ok()
                .map(|r| self.segments.memory.get_integer(r))
            {
                Some(Ok(instruction1)) => {
                    match is_call_instruction(&instruction1) {
                        true => (ret_pc - 1).unwrap(), // This unwrap wont fail as it is checked before
                        false => {
                            match (ret_pc - 2)
                                .ok()
                                .map(|r| self.segments.memory.get_integer(r))
                            {
                                Some(Ok(instruction0)) => {
                                    match is_call_instruction(&instruction0) {
                                        true => (ret_pc - 2).unwrap(), // This unwrap wont fail as it is checked before
                                        false => break,
                                    }
                                }
                                _ => break,
                            }
                        }
                    }
                }
                _ => break,
            };
            // Append traceback entries
            entries.push((fp, call_pc))
        }
        entries.reverse();
        entries
    }

    ///Adds a new segment and to the memory and returns its starting location as a Relocatable value.
    pub fn add_memory_segment(&mut self) -> Relocatable {
        self.segments.add()
    }

    pub fn get_ap(&self) -> Relocatable {
        self.run_context.get_ap()
    }

    pub fn get_fp(&self) -> Relocatable {
        self.run_context.get_fp()
    }

    pub fn get_pc(&self) -> Relocatable {
        self.run_context.get_pc()
    }

    ///Gets the integer value corresponding to the Relocatable address
    pub fn get_integer(&self, key: Relocatable) -> Result<Cow<Felt252>, MemoryError> {
        self.segments.memory.get_integer(key)
    }

    ///Gets the relocatable value corresponding to the Relocatable address
    pub fn get_relocatable(&self, key: Relocatable) -> Result<Relocatable, MemoryError> {
        self.segments.memory.get_relocatable(key)
    }

    ///Gets a MaybeRelocatable value from memory indicated by a generic address
    pub fn get_maybe<'a, 'b: 'a, K: 'a>(&'b self, key: &'a K) -> Option<MaybeRelocatable>
    where
        Relocatable: TryFrom<&'a K>,
    {
        self.segments.memory.get(key).map(|x| x.into_owned())
    }

    /// Returns a reference to the vector with all builtins present in the virtual machine
    pub fn get_builtin_runners(&self) -> &Vec<BuiltinRunner> {
        &self.builtin_runners
    }

    /// Returns a mutable reference to the vector with all builtins present in the virtual machine
    pub fn get_builtin_runners_as_mut(&mut self) -> &mut Vec<BuiltinRunner> {
        &mut self.builtin_runners
    }

    ///Inserts a value into a memory address given by a Relocatable value
    pub fn insert_value<T: Into<MaybeRelocatable>>(
        &mut self,
        key: Relocatable,
        val: T,
    ) -> Result<(), MemoryError> {
        self.segments.memory.insert_value(key, val)
    }

    ///Writes data into the memory from address ptr and returns the first address after the data.
    pub fn load_data(
        &mut self,
        ptr: Relocatable,
        data: &Vec<MaybeRelocatable>,
    ) -> Result<Relocatable, MemoryError> {
        if ptr.segment_index == 0 {
            self.instruction_cache.resize(data.len(), None);
        }
        self.segments.load_data(ptr, data)
    }

    /// Writes args into the memory from address ptr and returns the first address after the data.
    pub fn write_arg(
        &mut self,
        ptr: Relocatable,
        arg: &dyn Any,
    ) -> Result<MaybeRelocatable, MemoryError> {
        self.segments.write_arg(ptr, arg)
    }

    pub fn memcmp(&self, lhs: Relocatable, rhs: Relocatable, len: usize) -> (Ordering, usize) {
        self.segments.memory.memcmp(lhs, rhs, len)
    }

    pub fn mem_eq(&self, lhs: Relocatable, rhs: Relocatable, len: usize) -> bool {
        self.segments.memory.mem_eq(lhs, rhs, len)
    }

    ///Gets `n_ret` return values from memory
    pub fn get_return_values(&self, n_ret: usize) -> Result<Vec<MaybeRelocatable>, MemoryError> {
        let addr = (self.run_context.get_ap() - n_ret)
            .map_err(|_| MemoryError::FailedToGetReturnValues(Box::new((n_ret, self.get_ap()))))?;
        self.segments.memory.get_continuous_range(addr, n_ret)
    }

    ///Gets n elements from memory starting from addr (n being size)
    pub fn get_range(&self, addr: Relocatable, size: usize) -> Vec<Option<Cow<MaybeRelocatable>>> {
        self.segments.memory.get_range(addr, size)
    }

    ///Gets n elements from memory starting from addr (n being size)
    pub fn get_continuous_range(
        &self,
        addr: Relocatable,
        size: usize,
    ) -> Result<Vec<MaybeRelocatable>, MemoryError> {
        self.segments.memory.get_continuous_range(addr, size)
    }

    ///Gets n integer values from memory starting from addr (n being size),
    pub fn get_integer_range(
        &self,
        addr: Relocatable,
        size: usize,
    ) -> Result<Vec<Cow<Felt252>>, MemoryError> {
        self.segments.memory.get_integer_range(addr, size)
    }

    pub fn get_range_check_builtin(&self) -> Result<&RangeCheckBuiltinRunner, VirtualMachineError> {
        for builtin in &self.builtin_runners {
            if let BuiltinRunner::RangeCheck(range_check_builtin) = builtin {
                return Ok(range_check_builtin);
            };
        }
        Err(VirtualMachineError::NoRangeCheckBuiltin)
    }

    pub fn get_signature_builtin(
        &mut self,
    ) -> Result<&mut SignatureBuiltinRunner, VirtualMachineError> {
        for builtin in self.get_builtin_runners_as_mut() {
            if let BuiltinRunner::Signature(signature_builtin) = builtin {
                return Ok(signature_builtin);
            };
        }

        Err(VirtualMachineError::NoSignatureBuiltin)
    }

    /// Returns a mutable reference to the output builtin.
    ///
    /// Returns Err(VirtualMachineError::NoOutputBuiltin) if there is no output builtin
    /// configured.
    pub fn get_output_builtin(
        &mut self,
    ) -> Result<&mut OutputBuiltinRunner, VirtualMachineError> {
        for builtin in self.get_builtin_runners_as_mut() {
            if let BuiltinRunner::Output(output_builtin) = builtin {
                return Ok(output_builtin);
            }
        }
        Err(VirtualMachineError::NoOutputBuiltin)
    }
    pub fn disable_trace(&mut self) {
        self.trace = None
    }

    #[doc(hidden)]
    pub fn skip_next_instruction_execution(&mut self) {
        self.skip_instruction_execution = true;
    }

    #[doc(hidden)]
    pub fn set_ap(&mut self, ap: usize) {
        self.run_context.set_ap(ap)
    }

    #[doc(hidden)]
    pub fn set_fp(&mut self, fp: usize) {
        self.run_context.set_fp(fp)
    }

    #[doc(hidden)]
    pub fn set_pc(&mut self, pc: Relocatable) {
        self.run_context.set_pc(pc)
    }

    pub fn get_segment_used_size(&self, index: usize) -> Option<usize> {
        self.segments.get_segment_used_size(index)
    }

    pub fn get_segment_size(&self, index: usize) -> Option<usize> {
        self.segments.get_segment_size(index)
    }

    pub fn add_temporary_segment(&mut self) -> Relocatable {
        self.segments.add_temporary_segment()
    }

    /// Add a new relocation rule.
    ///
    /// Will return an error if any of the following conditions are not met:
    ///   - Source address's segment must be negative (temporary).
    ///   - Source address's offset must be zero.
    ///   - There shouldn't already be relocation at the source segment.
    pub fn add_relocation_rule(
        &mut self,
        src_ptr: Relocatable,
        dst_ptr: Relocatable,
    ) -> Result<(), MemoryError> {
        self.segments.memory.add_relocation_rule(src_ptr, dst_ptr)
    }

    pub fn gen_arg(&mut self, arg: &dyn Any) -> Result<MaybeRelocatable, MemoryError> {
        self.segments.gen_arg(arg)
    }

    /// Write the values hosted in the output builtin's segment.
    /// Does nothing if the output builtin is not present in the program.
    pub fn write_output(
        &mut self,
        writer: &mut impl core::fmt::Write,
    ) -> Result<(), VirtualMachineError> {
        let builtin = match self
            .builtin_runners
            .iter()
            .find(|b| b.name() == OUTPUT_BUILTIN_NAME)
        {
            Some(x) => x,
            _ => return Ok(()),
        };

        let segment_used_sizes = self.segments.compute_effective_sizes();
        let segment_index = builtin.base();
        #[allow(deprecated)]
        for i in 0..segment_used_sizes[segment_index] {
            let formatted_value = match self
                .segments
                .memory
                .get(&Relocatable::from((segment_index as isize, i)))
            {
                Some(val) => match val.as_ref() {
                    MaybeRelocatable::Int(num) => format!("{}", num.to_signed_felt()),
                    MaybeRelocatable::RelocatableValue(rel) => format!("{}", rel),
                },
                _ => "<missing>".to_string(),
            };
            writeln!(writer, "{formatted_value}")
                .map_err(|_| VirtualMachineError::FailedToWriteOutput)?;
        }

        Ok(())
    }

    ///Relocates the VM's trace, turning relocatable registers to numbered ones
    pub fn relocate_trace(&mut self, relocation_table: &[usize]) -> Result<(), TraceError> {
        if let Some(ref mut trace) = self.trace {
            if self.trace_relocated {
                return Err(TraceError::AlreadyRelocated);
            }
            let segment_1_base = relocation_table
                .get(1)
                .ok_or(TraceError::NoRelocationFound)?;

            trace.iter_mut().for_each(|entry| {
                entry.pc += 1;
                entry.ap += segment_1_base;
                entry.fp += segment_1_base;
            });
            self.trace_relocated = true;
        }
        Ok(())
    }

    pub fn get_relocated_trace(&self) -> Result<&Vec<TraceEntry>, TraceError> {
        if self.trace_relocated {
            self.trace.as_ref().ok_or(TraceError::TraceNotEnabled)
        } else {
            Err(TraceError::TraceNotRelocated)
        }
    }

    /// Returns a list of addresses of memory cells that constitute the public memory.
    pub fn get_public_memory_addresses(&self) -> Result<Vec<(usize, usize)>, VirtualMachineError> {
        if let Some(relocation_table) = &self.relocation_table {
            self.segments
                .get_public_memory_addresses(relocation_table)
                .map_err(VirtualMachineError::Memory)
        } else {
            Err(MemoryError::UnrelocatedMemory.into())
        }
    }

    pub fn get_memory_segment_addresses(
        &self,
    ) -> Result<HashMap<&'static str, (usize, usize)>, VirtualMachineError> {
        let relocation_table = self
            .relocation_table
            .as_ref()
            .ok_or(MemoryError::UnrelocatedMemory)?;

        let relocate = |segment: (usize, usize)| -> Result<(usize, usize), VirtualMachineError> {
            let (index, stop_ptr_offset) = segment;
            let base = relocation_table
                .get(index)
                .ok_or(VirtualMachineError::RelocationNotFound(index))?;
            Ok((*base, base + stop_ptr_offset))
        };

        self.builtin_runners
            .iter()
            .map(|builtin| -> Result<_, VirtualMachineError> {
                let addresses =
                    if let (base, Some(stop_ptr)) = builtin.get_memory_segment_addresses() {
                        (base, stop_ptr)
                    } else {
                        return Err(RunnerError::NoStopPointer(Box::new(builtin.name())).into());
                    };

                Ok((
                    builtin.name().strip_suffix("_builtin").unwrap_or_default(),
                    relocate(addresses)?,
                ))
            })
            .collect()
    }
}

pub struct VirtualMachineBuilder {
    pub(crate) run_context: RunContext,
    pub(crate) builtin_runners: Vec<BuiltinRunner>,
    pub(crate) segments: MemorySegmentManager,
    pub(crate) trace: Option<Vec<TraceEntry>>,
    pub(crate) current_step: usize,
    skip_instruction_execution: bool,
    run_finished: bool,
    #[cfg(feature = "hooks")]
    pub(crate) hooks: crate::vm::hooks::Hooks,
}

impl Default for VirtualMachineBuilder {
    fn default() -> Self {
        let run_context = RunContext {
            pc: Relocatable::from((0, 0)),
            ap: 0,
            fp: 0,
        };

        VirtualMachineBuilder {
            run_context,
            builtin_runners: Vec::new(),
            trace: None,
            current_step: 0,
            skip_instruction_execution: false,
            segments: MemorySegmentManager::new(),
            run_finished: false,
            #[cfg(feature = "hooks")]
            hooks: Default::default(),
        }
    }
}

impl VirtualMachineBuilder {
    pub fn run_context(mut self, run_context: RunContext) -> VirtualMachineBuilder {
        self.run_context = run_context;
        self
    }

    pub fn builtin_runners(mut self, builtin_runners: Vec<BuiltinRunner>) -> VirtualMachineBuilder {
        self.builtin_runners = builtin_runners;
        self
    }

    pub fn segments(mut self, segments: MemorySegmentManager) -> VirtualMachineBuilder {
        self.segments = segments;
        self
    }

    pub fn trace(mut self, trace: Option<Vec<TraceEntry>>) -> VirtualMachineBuilder {
        self.trace = trace;
        self
    }

    pub fn current_step(mut self, current_step: usize) -> VirtualMachineBuilder {
        self.current_step = current_step;
        self
    }

    pub fn skip_instruction_execution(
        mut self,
        skip_instruction_execution: bool,
    ) -> VirtualMachineBuilder {
        self.skip_instruction_execution = skip_instruction_execution;
        self
    }

    pub fn run_finished(mut self, run_finished: bool) -> VirtualMachineBuilder {
        self.run_finished = run_finished;
        self
    }

    #[cfg(feature = "hooks")]
    pub fn hooks(mut self, hooks: crate::vm::hooks::Hooks) -> VirtualMachineBuilder {
        self.hooks = hooks;
        self
    }

    pub fn build(self) -> VirtualMachine {
        VirtualMachine {
            run_context: self.run_context,
            builtin_runners: self.builtin_runners,
            trace: self.trace,
            current_step: self.current_step,
            skip_instruction_execution: self.skip_instruction_execution,
            segments: self.segments,
            rc_limits: None,
            run_finished: self.run_finished,
            trace_relocated: false,
            instruction_cache: Vec::new(),
            #[cfg(feature = "hooks")]
            hooks: self.hooks,
            relocation_table: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stdlib::collections::HashMap;
    use crate::types::program::Program;
    use crate::vm::runners::builtin_runner::{
        BITWISE_BUILTIN_NAME, EC_OP_BUILTIN_NAME, HASH_BUILTIN_NAME,
    };
    use crate::vm::vm_memory::memory::Memory;
    use crate::{
        any_box,
        hint_processor::builtin_hint_processor::builtin_hint_processor_definition::{
            BuiltinHintProcessor, HintProcessorData,
        },
        relocatable,
        types::{
            instance_definitions::{
                bitwise_instance_def::BitwiseInstanceDef, ec_op_instance_def::EcOpInstanceDef,
            },
            instruction::{Op1Addr, Register},
            relocatable::Relocatable,
        },
        utils::test_utils::*,
        vm::{
            errors::memory_errors::MemoryError,
            runners::{
                builtin_runner::{BitwiseBuiltinRunner, EcOpBuiltinRunner, HashBuiltinRunner},
                cairo_runner::CairoRunner,
            },
        },
    };
    use assert_matches::assert_matches;

    use felt::felt_str;

    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_fp_ap_plus2() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::APPlus2,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        run_context!(vm, 4, 5, 6);
        assert_matches!(
            vm.update_fp(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.fp, 7)
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_fp_dst() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Dst,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: mayberelocatable!(1, 6),
            res: Some(mayberelocatable!(8)),
            op0: mayberelocatable!(9),
            op1: mayberelocatable!(10),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_fp(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.fp, 6)
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_fp_regular() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_fp(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.fp, 0)
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_fp_dst_num() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Dst,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        run_context!(vm, 4, 5, 6);

        assert_matches!(
            vm.update_fp(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.fp, 11)
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_ap_add_with_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Add,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = VirtualMachine::new(false);
        vm.run_context.pc = Relocatable::from((0, 4));
        vm.run_context.ap = 5;
        vm.run_context.fp = 6;

        assert_matches!(
            vm.update_ap(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.ap, 13);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_ap_add_without_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Add,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: None,
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        vm.run_context.pc = Relocatable::from((0, 4));
        vm.run_context.ap = 5;
        vm.run_context.fp = 6;

        assert_matches!(
            vm.update_ap(&instruction, &operands),
            Err(VirtualMachineError::UnconstrainedResAdd)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_ap_add1() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Add1,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        vm.run_context.pc = Relocatable::from((0, 4));
        vm.run_context.ap = 5;
        vm.run_context.fp = 6;

        assert_matches!(
            vm.update_ap(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.ap, 6);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_ap_add2() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Add2,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        vm.run_context.pc = Relocatable::from((0, 4));
        vm.run_context.ap = 5;
        vm.run_context.fp = 6;

        assert_matches!(
            vm.update_ap(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.ap, 7);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_ap_regular() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        vm.run_context.pc = Relocatable::from((0, 4));
        vm.run_context.ap = 5;
        vm.run_context.fp = 6;

        assert_matches!(
            vm.update_ap(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.ap, 5);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_regular_instruction_no_imm() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 1)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_regular_instruction_has_imm() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::Imm,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 2)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_jump_with_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: mayberelocatable!(1, 11),
            res: Some(mayberelocatable!(0, 8)),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 8)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_jump_without_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: None,
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        vm.run_context.pc = Relocatable::from((0, 4));
        vm.run_context.ap = 5;
        vm.run_context.fp = 6;

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Err(VirtualMachineError::UnconstrainedResJump)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_jump_rel_with_int_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::JumpRel,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        run_context!(vm, 1, 1, 1);

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 9)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_jump_rel_without_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::JumpRel,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: None,
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Err(VirtualMachineError::UnconstrainedResJumpRel)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_jump_rel_with_non_int_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::JumpRel,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::from((1, 4))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Err::<(), VirtualMachineError>(VirtualMachineError::JumpRelNotInt)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_jnz_dst_is_zero() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jnz,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(0)),
            res: Some(MaybeRelocatable::Int(Felt252::new(0))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 1)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_pc_jnz_dst_is_not_zero() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jnz,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();

        assert_matches!(
            vm.update_pc(&instruction, &operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 10)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_registers_all_regular() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        vm.run_context.pc = Relocatable::from((0, 4));
        vm.run_context.ap = 5;
        vm.run_context.fp = 6;

        assert_matches!(
            vm.update_registers(&instruction, operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 5)));
        assert_eq!(vm.run_context.ap, 5);
        assert_eq!(vm.run_context.fp, 6);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn update_registers_mixed_types() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::JumpRel,
            ap_update: ApUpdate::Add2,
            fp_update: FpUpdate::Dst,
            opcode: Opcode::NOp,
        };

        let operands = Operands {
            dst: MaybeRelocatable::from((1, 11)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8))),
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let mut vm = vm!();
        run_context!(vm, 4, 5, 6);

        assert_matches!(
            vm.update_registers(&instruction, operands),
            Ok::<(), VirtualMachineError>(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 12)));
        assert_eq!(vm.run_context.ap, 7);
        assert_eq!(vm.run_context.fp, 11);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn is_zero_int_value() {
        let value = MaybeRelocatable::Int(Felt252::new(1));
        assert!(!VirtualMachine::is_zero(&value));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn is_zero_relocatable_value() {
        let value = MaybeRelocatable::from((1, 2));
        assert!(!VirtualMachine::is_zero(&value));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op0_opcode_call() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::Call,
        };

        let vm = vm!();

        assert_matches!(
            vm.deduce_op0(&instruction, None, None),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                Some(x),
                None
            )) if x == MaybeRelocatable::from((0, 1))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op0_opcode_assert_eq_res_add_with_optionals() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(3));
        let op1 = MaybeRelocatable::Int(Felt252::new(2));

        assert_matches!(
            vm.deduce_op0(&instruction, Some(&dst), Some(&op1)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                x,
                y
            )) if x == Some(MaybeRelocatable::Int(Felt252::new(1))) &&
                    y == Some(MaybeRelocatable::Int(Felt252::new(3)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op0_opcode_assert_eq_res_add_without_optionals() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        assert_matches!(
            vm.deduce_op0(&instruction, None, None),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op0_opcode_assert_eq_res_mul_non_zero_op1() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Mul,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(4));
        let op1 = MaybeRelocatable::Int(Felt252::new(2));

        assert_matches!(
            vm.deduce_op0(&instruction, Some(&dst), Some(&op1)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                Some(x),
                Some(y)
            )) if x == MaybeRelocatable::Int(Felt252::new(2)) &&
                    y == MaybeRelocatable::Int(Felt252::new(4))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op0_opcode_assert_eq_res_mul_zero_op1() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Mul,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(4));
        let op1 = MaybeRelocatable::Int(Felt252::new(0));
        assert_matches!(
            vm.deduce_op0(&instruction, Some(&dst), Some(&op1)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op0_opcode_assert_eq_res_op1() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Op1,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(4));
        let op1 = MaybeRelocatable::Int(Felt252::new(0));
        assert_matches!(
            vm.deduce_op0(&instruction, Some(&dst), Some(&op1)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op0_opcode_ret() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Mul,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::Ret,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(4));
        let op1 = MaybeRelocatable::Int(Felt252::new(0));

        assert_matches!(
            vm.deduce_op0(&instruction, Some(&dst), Some(&op1)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op1_opcode_call() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::Call,
        };

        let vm = vm!();

        assert_matches!(
            vm.deduce_op1(&instruction, None, None),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op1_opcode_assert_eq_res_add_with_optionals() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(3));
        let op0 = MaybeRelocatable::Int(Felt252::new(2));
        assert_matches!(
            vm.deduce_op1(&instruction, Some(&dst), Some(op0)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                x,
                y
            )) if x == Some(MaybeRelocatable::Int(Felt252::new(1))) &&
                    y == Some(MaybeRelocatable::Int(Felt252::new(3)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op1_opcode_assert_eq_res_add_without_optionals() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();
        assert_matches!(
            vm.deduce_op1(&instruction, None, None),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op1_opcode_assert_eq_res_mul_non_zero_op0() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Mul,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(4));
        let op0 = MaybeRelocatable::Int(Felt252::new(2));
        assert_matches!(
            vm.deduce_op1(&instruction, Some(&dst), Some(op0)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                x,
                y
            )) if x == Some(MaybeRelocatable::Int(Felt252::new(2))) &&
                    y == Some(MaybeRelocatable::Int(Felt252::new(4)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op1_opcode_assert_eq_res_mul_zero_op0() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Mul,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(4));
        let op0 = MaybeRelocatable::Int(Felt252::new(0));
        assert_matches!(
            vm.deduce_op1(&instruction, Some(&dst), Some(op0)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op1_opcode_assert_eq_res_op1_without_dst() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Op1,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let op0 = MaybeRelocatable::Int(Felt252::new(0));
        assert_matches!(
            vm.deduce_op1(&instruction, None, Some(op0)),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                None, None
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_op1_opcode_assert_eq_res_op1_with_dst() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Op1,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let dst = MaybeRelocatable::Int(Felt252::new(7));
        assert_matches!(
            vm.deduce_op1(&instruction, Some(&dst), None),
            Ok::<(Option<MaybeRelocatable>, Option<MaybeRelocatable>), VirtualMachineError>((
                x,
                y
            )) if x == Some(MaybeRelocatable::Int(Felt252::new(7))) &&
                    y == Some(MaybeRelocatable::Int(Felt252::new(7)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_res_op1() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Op1,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let op1 = MaybeRelocatable::Int(Felt252::new(7));
        let op0 = MaybeRelocatable::Int(Felt252::new(9));
        assert_matches!(
            vm.compute_res(&instruction, &op0, &op1),
            Ok::<Option<MaybeRelocatable>, VirtualMachineError>(Some(MaybeRelocatable::Int(
                x
            ))) if x == Felt252::new(7)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_res_add() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let op1 = MaybeRelocatable::Int(Felt252::new(7));
        let op0 = MaybeRelocatable::Int(Felt252::new(9));
        assert_matches!(
            vm.compute_res(&instruction, &op0, &op1),
            Ok::<Option<MaybeRelocatable>, VirtualMachineError>(Some(MaybeRelocatable::Int(
                x
            ))) if x == Felt252::new(16)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_res_mul_int_operands() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Mul,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let op1 = MaybeRelocatable::Int(Felt252::new(7));
        let op0 = MaybeRelocatable::Int(Felt252::new(9));
        assert_matches!(
            vm.compute_res(&instruction, &op0, &op1),
            Ok::<Option<MaybeRelocatable>, VirtualMachineError>(Some(MaybeRelocatable::Int(
                x
            ))) if x == Felt252::new(63)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_res_mul_relocatable_values() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Mul,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let op1 = MaybeRelocatable::from((2, 3));
        let op0 = MaybeRelocatable::from((2, 6));
        assert_matches!(
            vm.compute_res(&instruction, &op0, &op1),
            Err(VirtualMachineError::ComputeResRelocatableMul(bx)) if *bx == (op0, op1)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_res_unconstrained() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Unconstrained,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let op1 = MaybeRelocatable::Int(Felt252::new(7));
        let op0 = MaybeRelocatable::Int(Felt252::new(9));
        assert_matches!(
            vm.compute_res(&instruction, &op0, &op1),
            Ok::<Option<MaybeRelocatable>, VirtualMachineError>(None)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_dst_opcode_assert_eq_with_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Unconstrained,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        let res = MaybeRelocatable::Int(Felt252::new(7));
        assert_eq!(
            MaybeRelocatable::Int(Felt252::new(7)),
            vm.deduce_dst(&instruction, &Some(res)).unwrap()
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_dst_opcode_assert_eq_without_res() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Unconstrained,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let vm = vm!();

        assert!(vm.deduce_dst(&instruction, &None).is_err());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_dst_opcode_call() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Unconstrained,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::Call,
        };

        let vm = vm!();

        assert_eq!(
            MaybeRelocatable::from((1, 0)),
            vm.deduce_dst(&instruction, &None).unwrap()
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_dst_opcode_ret() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Unconstrained,
            pc_update: PcUpdate::Jump,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::Ret,
        };

        let vm = vm!();

        assert!(vm.deduce_dst(&instruction, &None).is_err());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_operands_add_ap() {
        let inst = Instruction {
            off0: 0,
            off1: 1,
            off2: 2,
            dst_register: Register::AP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let mut vm = vm!();
        for _ in 0..2 {
            vm.segments.add();
        }

        vm.segments.memory.data.push(Vec::new());
        let dst_addr = Relocatable::from((1, 0));
        let dst_addr_value = MaybeRelocatable::Int(Felt252::new(5));
        let op0_addr = Relocatable::from((1, 1));
        let op0_addr_value = MaybeRelocatable::Int(Felt252::new(2));
        let op1_addr = Relocatable::from((1, 2));
        let op1_addr_value = MaybeRelocatable::Int(Felt252::new(3));
        vm.segments
            .memory
            .insert(dst_addr, &dst_addr_value)
            .unwrap();
        vm.segments
            .memory
            .insert(op0_addr, &op0_addr_value)
            .unwrap();
        vm.segments
            .memory
            .insert(op1_addr, &op1_addr_value)
            .unwrap();

        let expected_operands = Operands {
            dst: dst_addr_value.clone(),
            res: Some(dst_addr_value.clone()),
            op0: op0_addr_value.clone(),
            op1: op1_addr_value.clone(),
        };

        let expected_addresses = OperandsAddresses {
            dst_addr,
            op0_addr,
            op1_addr,
        };

        let (operands, addresses, _) = vm.compute_operands(&inst).unwrap();
        assert!(operands == expected_operands);
        assert!(addresses == expected_addresses);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_operands_mul_fp() {
        let inst = Instruction {
            off0: 0,
            off1: 1,
            off2: 2,
            dst_register: Register::FP,
            op0_register: Register::FP,
            op1_addr: Op1Addr::FP,
            res: Res::Mul,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };
        let mut vm = vm!();
        //Create program and execution segments
        for _ in 0..2 {
            vm.segments.add();
        }
        vm.segments.memory.data.push(Vec::new());
        let dst_addr = relocatable!(1, 0);
        let dst_addr_value = mayberelocatable!(6);
        let op0_addr = relocatable!(1, 1);
        let op0_addr_value = mayberelocatable!(2);
        let op1_addr = relocatable!(1, 2);
        let op1_addr_value = mayberelocatable!(3);
        vm.segments
            .memory
            .insert(dst_addr, &dst_addr_value)
            .unwrap();
        vm.segments
            .memory
            .insert(op0_addr, &op0_addr_value)
            .unwrap();
        vm.segments
            .memory
            .insert(op1_addr, &op1_addr_value)
            .unwrap();

        let expected_operands = Operands {
            dst: dst_addr_value.clone(),
            res: Some(dst_addr_value.clone()),
            op0: op0_addr_value.clone(),
            op1: op1_addr_value.clone(),
        };

        let expected_addresses = OperandsAddresses {
            dst_addr,
            op0_addr,
            op1_addr,
        };

        let (operands, addresses, _) = vm.compute_operands(&inst).unwrap();
        assert!(operands == expected_operands);
        assert!(addresses == expected_addresses);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_jnz() {
        let instruction = Instruction {
            off0: 1,
            off1: 1,
            off2: 1,
            dst_register: Register::AP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::Imm,
            res: Res::Unconstrained,
            pc_update: PcUpdate::Jnz,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let mut vm = vm!();
        vm.segments = segments![
            ((0, 0), 0x206800180018001_i64),
            ((1, 1), 0x4),
            ((0, 1), 0x4)
        ];

        let expected_operands = Operands {
            dst: mayberelocatable!(4),
            res: None,
            op0: mayberelocatable!(4),
            op1: mayberelocatable!(4),
        };

        let expected_addresses = OperandsAddresses {
            dst_addr: relocatable!(1, 1),
            op0_addr: relocatable!(1, 1),
            op1_addr: relocatable!(0, 1),
        };

        let (operands, addresses, _) = vm.compute_operands(&instruction).unwrap();
        assert!(operands == expected_operands);
        assert!(addresses == expected_addresses);
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            vm.step(
                &mut hint_processor,
                exec_scopes_ref!(),
                &Vec::new(),
                &HashMap::new(),
            ),
            Ok(())
        );
        assert_eq!(vm.run_context.pc, relocatable!(0, 4));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_operands_deduce_dst_none() {
        let instruction = Instruction {
            off0: 2,
            off1: 0,
            off2: 0,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Unconstrained,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::NOp,
        };

        let mut vm = vm!();

        vm.segments = segments!(((1, 0), 145944781867024385_i64));

        let error = vm.compute_operands(&instruction).unwrap_err();
        assert_matches!(error, VirtualMachineError::NoDst);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn opcode_assertions_res_unconstrained() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::APPlus2,
            opcode: Opcode::AssertEq,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(8)),
            res: None,
            op0: MaybeRelocatable::Int(Felt252::new(9)),
            op1: MaybeRelocatable::Int(Felt252::new(10)),
        };

        let vm = vm!();

        let error = vm.opcode_assertions(&instruction, &operands);
        assert_matches!(error, Err(VirtualMachineError::UnconstrainedResAssertEq));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn opcode_assertions_instruction_failed() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::APPlus2,
            opcode: Opcode::AssertEq,
        };

        let operands = Operands {
            dst: MaybeRelocatable::Int(Felt252::new(9_i32)),
            res: Some(MaybeRelocatable::Int(Felt252::new(8_i32))),
            op0: MaybeRelocatable::Int(Felt252::new(9_i32)),
            op1: MaybeRelocatable::Int(Felt252::new(10_i32)),
        };

        let vm = vm!();

        assert_matches!(
            vm.opcode_assertions(&instruction, &operands),
            Err(VirtualMachineError::DiffAssertValues(bx))
            if *bx == (MaybeRelocatable::Int(Felt252::new(9_i32)),
                 MaybeRelocatable::Int(Felt252::new(8_i32)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn opcode_assertions_instruction_failed_relocatables() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::APPlus2,
            opcode: Opcode::AssertEq,
        };

        let operands = Operands {
            dst: MaybeRelocatable::from((1, 1)),
            res: Some(MaybeRelocatable::from((1, 2))),
            op0: MaybeRelocatable::Int(Felt252::new(9_i32)),
            op1: MaybeRelocatable::Int(Felt252::new(10_i32)),
        };

        let vm = vm!();

        assert_matches!(
            vm.opcode_assertions(&instruction, &operands),
            Err(VirtualMachineError::DiffAssertValues(bx)) if *bx == (MaybeRelocatable::from((1, 1)), MaybeRelocatable::from((1, 2)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn opcode_assertions_inconsistent_op0() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::APPlus2,
            opcode: Opcode::Call,
        };

        let operands = Operands {
            dst: mayberelocatable!(0, 8),
            res: Some(mayberelocatable!(8)),
            op0: mayberelocatable!(9),
            op1: mayberelocatable!(10),
        };

        let mut vm = vm!();
        vm.run_context.pc = relocatable!(0, 4);

        assert_matches!(
            vm.opcode_assertions(&instruction, &operands),
            Err(VirtualMachineError::CantWriteReturnPc(bx)) if *bx == (mayberelocatable!(9), mayberelocatable!(0, 5))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn opcode_assertions_inconsistent_dst() {
        let instruction = Instruction {
            off0: 1,
            off1: 2,
            off2: 3,
            dst_register: Register::FP,
            op0_register: Register::AP,
            op1_addr: Op1Addr::AP,
            res: Res::Add,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Regular,
            fp_update: FpUpdate::APPlus2,
            opcode: Opcode::Call,
        };

        let operands = Operands {
            dst: mayberelocatable!(8),
            res: Some(mayberelocatable!(8)),
            op0: mayberelocatable!(0, 1),
            op1: mayberelocatable!(10),
        };
        let mut vm = vm!();
        vm.run_context.fp = 6;

        assert_matches!(
            vm.opcode_assertions(&instruction, &operands),
            Err(VirtualMachineError::CantWriteReturnFp(bx)) if *bx == (mayberelocatable!(8), mayberelocatable!(1, 6))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /// Test for a simple program execution
    /// Used program code:
    /// func main():
    ///     let a = 1
    ///     let b = 2
    ///     let c = a + b
    ///     return()
    /// end
    /// Memory taken from original vm
    /// {RelocatableValue(segment_index=0, offset=0): 2345108766317314046,
    ///  RelocatableValue(segment_index=1, offset=0): RelocatableValue(segment_index=2, offset=0),
    ///  RelocatableValue(segment_index=1, offset=1): RelocatableValue(segment_index=3, offset=0)}
    /// Current register values:
    /// AP 1:2
    /// FP 1:2
    /// PC 0:0
    fn test_step_for_preset_memory() {
        let mut vm = vm!(true);

        let mut hint_processor = BuiltinHintProcessor::new_empty();

        run_context!(vm, 0, 2, 2);

        vm.segments = segments![
            ((0, 0), 2345108766317314046_u64),
            ((1, 0), (2, 0)),
            ((1, 1), (3, 0))
        ];

        assert_matches!(
            vm.step(
                &mut hint_processor,
                exec_scopes_ref!(),
                &Vec::new(),
                &HashMap::new()
            ),
            Ok(())
        );
        let trace = vm.trace.unwrap();
        trace_check(&trace, &[(0, 2, 2)]);

        assert_eq!(vm.run_context.pc, Relocatable::from((3, 0)));
        assert_eq!(vm.run_context.ap, 2);
        assert_eq!(vm.run_context.fp, 0);

        //Check that the following addresses have been accessed:
        // Addresses have been copied from python execution:
        let mem = vm.segments.memory.data;
        assert!(mem[1][0].as_ref().unwrap().is_accessed());
        assert!(mem[1][1].as_ref().unwrap().is_accessed());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /*
    Test for a simple program execution
    Used program code:
        func myfunc(a: felt) -> (r: felt):
            let b = a * 2
            return(b)
        end
        func main():
            let a = 1
            let b = myfunc(a)
            return()
        end
    Memory taken from original vm:
    {RelocatableValue(segment_index=0, offset=0): 5207990763031199744,
    RelocatableValue(segment_index=0, offset=1): 2,
    RelocatableValue(segment_index=0, offset=2): 2345108766317314046,
    RelocatableValue(segment_index=0, offset=3): 5189976364521848832,
    RelocatableValue(segment_index=0, offset=4): 1,
    RelocatableValue(segment_index=0, offset=5): 1226245742482522112,
    RelocatableValue(segment_index=0, offset=6): 3618502788666131213697322783095070105623107215331596699973092056135872020476,
    RelocatableValue(segment_index=0, offset=7): 2345108766317314046,
    RelocatableValue(segment_index=1, offset=0): RelocatableValue(segment_index=2, offset=0),
    RelocatableValue(segment_index=1, offset=1): RelocatableValue(segment_index=3, offset=0)}
    Current register values:
    AP 1:2
    FP 1:2
    PC 0:3
    Final Pc (not executed): 3:0
    This program consists of 5 steps
    */
    fn test_step_for_preset_memory_function_call() {
        let mut vm = vm!(true);

        run_context!(vm, 3, 2, 2);

        //Insert values into memory
        vm.segments.memory =
            memory![
            ((0, 0), 5207990763031199744_i64),
            ((0, 1), 2),
            ((0, 2), 2345108766317314046_i64),
            ((0, 3), 5189976364521848832_i64),
            ((0, 4), 1),
            ((0, 5), 1226245742482522112_i64),
            (
                (0, 6),
                ("3618502788666131213697322783095070105623107215331596699973092056135872020476",10)
            ),
            ((0, 7), 2345108766317314046_i64),
            ((1, 0), (2, 0)),
            ((1, 1), (3, 0))
        ];

        let final_pc = Relocatable::from((3, 0));
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        //Run steps
        while vm.run_context.pc != final_pc {
            assert_matches!(
                vm.step(
                    &mut hint_processor,
                    exec_scopes_ref!(),
                    &Vec::new(),
                    &HashMap::new()
                ),
                Ok(())
            );
        }

        //Check final register values
        assert_eq!(vm.run_context.pc, Relocatable::from((3, 0)));

        assert_eq!(vm.run_context.ap, 6);

        assert_eq!(vm.run_context.fp, 0);
        //Check each TraceEntry in trace
        let trace = vm.trace.unwrap();
        assert_eq!(trace.len(), 5);
        trace_check(
            &trace,
            &[(3, 2, 2), (5, 3, 2), (0, 5, 5), (2, 6, 5), (7, 6, 2)],
        );
        //Check that the following addresses have been accessed:
        // Addresses have been copied from python execution:
        let mem = &vm.segments.memory.data;
        assert!(mem[0][1].as_ref().unwrap().is_accessed());
        assert!(mem[0][4].as_ref().unwrap().is_accessed());
        assert!(mem[0][6].as_ref().unwrap().is_accessed());
        assert!(mem[1][0].as_ref().unwrap().is_accessed());
        assert!(mem[1][1].as_ref().unwrap().is_accessed());
        assert!(mem[1][2].as_ref().unwrap().is_accessed());
        assert!(mem[1][3].as_ref().unwrap().is_accessed());
        assert!(mem[1][4].as_ref().unwrap().is_accessed());
        assert!(mem[1][5].as_ref().unwrap().is_accessed());
        assert_eq!(
            vm.segments
                .memory
                .get_amount_of_accessed_addresses_for_segment(0),
            Some(3)
        );
        assert_eq!(
            vm.segments
                .memory
                .get_amount_of_accessed_addresses_for_segment(1),
            Some(6)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /// Test the following program:
    /// ...
    /// [ap] = 4
    /// ap += 1
    /// [ap] = 5; ap++
    /// [ap] = [ap - 1] * [ap - 2]
    /// ...
    /// Original vm memory:
    /// RelocatableValue(segment_index=0, offset=0): '0x400680017fff8000',
    /// RelocatableValue(segment_index=0, offset=1): '0x4',
    /// RelocatableValue(segment_index=0, offset=2): '0x40780017fff7fff',
    /// RelocatableValue(segment_index=0, offset=3): '0x1',
    /// RelocatableValue(segment_index=0, offset=4): '0x480680017fff8000',
    /// RelocatableValue(segment_index=0, offset=5): '0x5',
    /// RelocatableValue(segment_index=0, offset=6): '0x40507ffe7fff8000',
    /// RelocatableValue(segment_index=0, offset=7): '0x208b7fff7fff7ffe',
    /// RelocatableValue(segment_index=1, offset=0): RelocatableValue(segment_index=2, offset=0),
    /// RelocatableValue(segment_index=1, offset=1): RelocatableValue(segment_index=3, offset=0),
    /// RelocatableValue(segment_index=1, offset=2): '0x4',
    /// RelocatableValue(segment_index=1, offset=3): '0x5',
    /// RelocatableValue(segment_index=1, offset=4): '0x14'
    fn multiplication_and_different_ap_increase() {
        let mut vm = vm!();
        vm.segments = segments![
            ((0, 0), 0x400680017fff8000_i64),
            ((0, 1), 0x4),
            ((0, 2), 0x40780017fff7fff_i64),
            ((0, 3), 0x1),
            ((0, 4), 0x480680017fff8000_i64),
            ((0, 5), 0x5),
            ((0, 6), 0x40507ffe7fff8000_i64),
            ((0, 7), 0x208b7fff7fff7ffe_i64),
            ((1, 0), (2, 0)),
            ((1, 1), (3, 0)),
            ((1, 2), 0x4),
            ((1, 3), 0x5),
            ((1, 4), 0x14)
        ];

        run_context!(vm, 0, 2, 2);

        assert_eq!(vm.run_context.pc, Relocatable::from((0, 0)));
        assert_eq!(vm.run_context.ap, 2);
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            vm.step(
                &mut hint_processor,
                exec_scopes_ref!(),
                &Vec::new(),
                &HashMap::new()
            ),
            Ok(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 2)));
        assert_eq!(vm.run_context.ap, 2);

        assert_eq!(
            vm.segments
                .memory
                .get(&vm.run_context.get_ap())
                .unwrap()
                .as_ref(),
            &MaybeRelocatable::Int(Felt252::new(0x4)),
        );
        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            vm.step(
                &mut hint_processor,
                exec_scopes_ref!(),
                &Vec::new(),
                &HashMap::new()
            ),
            Ok(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 4)));
        assert_eq!(vm.run_context.ap, 3);

        assert_eq!(
            vm.segments
                .memory
                .get(&vm.run_context.get_ap())
                .unwrap()
                .as_ref(),
            &MaybeRelocatable::Int(Felt252::new(0x5))
        );

        let mut hint_processor = BuiltinHintProcessor::new_empty();
        assert_matches!(
            vm.step(
                &mut hint_processor,
                exec_scopes_ref!(),
                &Vec::new(),
                &HashMap::new()
            ),
            Ok(())
        );
        assert_eq!(vm.run_context.pc, Relocatable::from((0, 6)));
        assert_eq!(vm.run_context.ap, 4);

        assert_eq!(
            vm.segments
                .memory
                .get(&vm.run_context.get_ap())
                .unwrap()
                .as_ref(),
            &MaybeRelocatable::Int(Felt252::new(0x14)),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_memory_cell_no_pedersen_builtin() {
        let vm = vm!();
        assert_matches!(vm.deduce_memory_cell(Relocatable::from((0, 0))), Ok(None));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_memory_cell_pedersen_builtin_valid() {
        let mut vm = vm!();
        let builtin = HashBuiltinRunner::new(Some(8), true);
        vm.builtin_runners.push(builtin.into());
        vm.segments = segments![((0, 3), 32), ((0, 4), 72), ((0, 5), 0)];
        assert_matches!(
            vm.deduce_memory_cell(Relocatable::from((0, 5))),
            Ok(i) if i == Some(MaybeRelocatable::from(felt::felt_str!(
                "3270867057177188607814717243084834301278723532952411121381966378910183338911"
            )))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /* Program used:
    %builtins output pedersen
    from starkware.cairo.common.cairo_builtins import HashBuiltin
    from starkware.cairo.common.hash import hash2
    from starkware.cairo.common.serialize import serialize_word

    func foo(hash_ptr : HashBuiltin*) -> (
        hash_ptr : HashBuiltin*, z
    ):
        # Use a with-statement, since 'hash_ptr' is not an
        # implicit argument.
        with hash_ptr:
            let (z) = hash2(32, 72)
        end
        return (hash_ptr=hash_ptr, z=z)
    end

    func main{output_ptr: felt*, pedersen_ptr: HashBuiltin*}():
        let (pedersen_ptr, a) = foo(pedersen_ptr)
        serialize_word(a)
        return()
    end
     */
    fn compute_operands_pedersen() {
        let instruction = Instruction {
            off0: 0,
            off1: -5,
            off2: 2,
            dst_register: Register::AP,
            op0_register: Register::FP,
            op1_addr: Op1Addr::Op0,
            res: Res::Op1,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Add1,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };
        let mut builtin = HashBuiltinRunner::new(Some(8), true);
        builtin.base = 3;
        let mut vm = vm!();
        vm.builtin_runners.push(builtin.into());
        run_context!(vm, 0, 13, 12);

        //Insert values into memory (excluding those from the program segment (instructions))
        vm.segments = segments![
            ((3, 0), 32),
            ((3, 1), 72),
            ((1, 0), (2, 0)),
            ((1, 1), (3, 0)),
            ((1, 2), (4, 0)),
            ((1, 3), (5, 0)),
            ((1, 4), (3, 0)),
            ((1, 5), (1, 4)),
            ((1, 6), (0, 21)),
            ((1, 7), (3, 0)),
            ((1, 8), 32),
            ((1, 9), 72),
            ((1, 10), (1, 7)),
            ((1, 11), (0, 17)),
            ((1, 12), (3, 3))
        ];

        let expected_operands = Operands {
            dst: MaybeRelocatable::from(felt_str!(
                "3270867057177188607814717243084834301278723532952411121381966378910183338911"
            )),
            res: Some(MaybeRelocatable::from(felt_str!(
                "3270867057177188607814717243084834301278723532952411121381966378910183338911"
            ))),
            op0: MaybeRelocatable::from((3, 0)),
            op1: MaybeRelocatable::from(felt_str!(
                "3270867057177188607814717243084834301278723532952411121381966378910183338911"
            )),
        };
        let expected_operands_mem_addresses = OperandsAddresses {
            dst_addr: Relocatable::from((1, 13)),
            op0_addr: Relocatable::from((1, 7)),
            op1_addr: Relocatable::from((3, 2)),
        };
        let (operands, operands_mem_address, _) = vm.compute_operands(&instruction).unwrap();
        assert_eq!(operands, expected_operands);
        assert_eq!(operands_mem_address, expected_operands_mem_addresses);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_memory_cell_bitwise_builtin_valid_and() {
        let mut vm = vm!();
        let builtin = BitwiseBuiltinRunner::new(&BitwiseInstanceDef::default(), true);
        vm.builtin_runners.push(builtin.into());
        vm.segments = segments![((0, 5), 10), ((0, 6), 12), ((0, 7), 0)];
        assert_matches!(
            vm.deduce_memory_cell(Relocatable::from((0, 7))),
            Ok(i) if i == Some(MaybeRelocatable::from(Felt252::new(8_i32)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /* Program used:
    %builtins bitwise
    from starkware.cairo.common.bitwise import bitwise_and
    from starkware.cairo.common.cairo_builtins import BitwiseBuiltin


    func main{bitwise_ptr: BitwiseBuiltin*}():
        let (result) = bitwise_and(12, 10)  # Binary (1100, 1010).
        assert result = 8  # Binary 1000.
        return()
    end
    */
    fn compute_operands_bitwise() {
        let instruction = Instruction {
            off0: 0,
            off1: -5,
            off2: 2,
            dst_register: Register::AP,
            op0_register: Register::FP,
            op1_addr: Op1Addr::Op0,
            res: Res::Op1,
            pc_update: PcUpdate::Regular,
            ap_update: ApUpdate::Add1,
            fp_update: FpUpdate::Regular,
            opcode: Opcode::AssertEq,
        };

        let mut builtin = BitwiseBuiltinRunner::new(&BitwiseInstanceDef::default(), true);
        builtin.base = 2;
        let mut vm = vm!();

        vm.builtin_runners.push(builtin.into());
        run_context!(vm, 0, 9, 8);

        //Insert values into memory (excluding those from the program segment (instructions))
        vm.segments = segments![
            ((2, 0), 12),
            ((2, 1), 10),
            ((1, 0), (2, 0)),
            ((1, 1), (3, 0)),
            ((1, 2), (4, 0)),
            ((1, 3), (2, 0)),
            ((1, 4), 12),
            ((1, 5), 10),
            ((1, 6), (1, 3)),
            ((1, 7), (0, 13))
        ];

        let expected_operands = Operands {
            dst: MaybeRelocatable::from(Felt252::new(8_i32)),
            res: Some(MaybeRelocatable::from(Felt252::new(8_i32))),
            op0: MaybeRelocatable::from((2, 0)),
            op1: MaybeRelocatable::from(Felt252::new(8_i32)),
        };
        let expected_operands_mem_addresses = OperandsAddresses {
            dst_addr: Relocatable::from((1, 9)),
            op0_addr: Relocatable::from((1, 3)),
            op1_addr: Relocatable::from((2, 2)),
        };
        let (operands, operands_mem_address, _) = vm.compute_operands(&instruction).unwrap();
        assert_eq!(operands, expected_operands);
        assert_eq!(operands_mem_address, expected_operands_mem_addresses);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn deduce_memory_cell_ec_op_builtin_valid() {
        let mut vm = vm!();
        let builtin = EcOpBuiltinRunner::new(&EcOpInstanceDef::default(), true);
        vm.builtin_runners.push(builtin.into());

        vm.segments = segments![
            (
                (0, 0),
                (
                    "2962412995502985605007699495352191122971573493113767820301112397466445942584",
                    10
                )
            ),
            (
                (0, 1),
                (
                    "214950771763870898744428659242275426967582168179217139798831865603966154129",
                    10
                )
            ),
            (
                (0, 2),
                (
                    "874739451078007766457464989774322083649278607533249481151382481072868806602",
                    10
                )
            ),
            (
                (0, 3),
                (
                    "152666792071518830868575557812948353041420400780739481342941381225525861407",
                    10
                )
            ),
            ((0, 4), 34),
            (
                (0, 5),
                (
                    "2778063437308421278851140253538604815869848682781135193774472480292420096757",
                    10
                )
            )
        ];

        assert_matches!(
            vm.deduce_memory_cell(Relocatable::from((0, 6))),
            Ok(i) if i == Some(MaybeRelocatable::from(felt_str!(
                "3598390311618116577316045819420613574162151407434885460365915347732568210029"
            )))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /* Data taken from this program execution:
       %builtins output ec_op
       from starkware.cairo.common.cairo_builtins import EcOpBuiltin
       from starkware.cairo.common.serialize import serialize_word
       from starkware.cairo.common.ec_point import EcPoint
       from starkware.cairo.common.ec import ec_op

       func main{output_ptr: felt*, ec_op_ptr: EcOpBuiltin*}():
           let x: EcPoint = EcPoint(2089986280348253421170679821480865132823066470938446095505822317253594081284, 1713931329540660377023406109199410414810705867260802078187082345529207694986)

           let y: EcPoint = EcPoint(874739451078007766457464989774322083649278607533249481151382481072868806602,152666792071518830868575557812948353041420400780739481342941381225525861407)
           let z: EcPoint = ec_op(x,34, y)
           serialize_word(z.x)
           return()
           end
    */
    fn verify_auto_deductions_for_ec_op_builtin_valid() {
        let mut builtin = EcOpBuiltinRunner::new(&EcOpInstanceDef::default(), true);
        builtin.base = 3;
        let mut vm = vm!();
        vm.builtin_runners.push(builtin.into());
        vm.segments = segments![
            (
                (3, 0),
                (
                    "2962412995502985605007699495352191122971573493113767820301112397466445942584",
                    10
                )
            ),
            (
                (3, 1),
                (
                    "214950771763870898744428659242275426967582168179217139798831865603966154129",
                    10
                )
            ),
            (
                (3, 2),
                (
                    "874739451078007766457464989774322083649278607533249481151382481072868806602",
                    10
                )
            ),
            (
                (3, 3),
                (
                    "152666792071518830868575557812948353041420400780739481342941381225525861407",
                    10
                )
            ),
            ((3, 4), 34),
            (
                (3, 5),
                (
                    "2778063437308421278851140253538604815869848682781135193774472480292420096757",
                    10
                )
            )
        ];
        assert_matches!(vm.verify_auto_deductions(), Ok(()));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn verify_auto_deductions_for_ec_op_builtin_valid_points_invalid_result() {
        let mut builtin = EcOpBuiltinRunner::new(&EcOpInstanceDef::default(), true);
        builtin.base = 3;
        let mut vm = vm!();
        vm.builtin_runners.push(builtin.into());
        vm.segments = segments![
            (
                (3, 0),
                (
                    "2962412995502985605007699495352191122971573493113767820301112397466445942584",
                    10
                )
            ),
            (
                (3, 1),
                (
                    "214950771763870898744428659242275426967582168179217139798831865603966154129",
                    10
                )
            ),
            (
                (3, 2),
                (
                    "2089986280348253421170679821480865132823066470938446095505822317253594081284",
                    10
                )
            ),
            (
                (3, 3),
                (
                    "1713931329540660377023406109199410414810705867260802078187082345529207694986",
                    10
                )
            ),
            ((3, 4), 34),
            (
                (3, 5),
                (
                    "2778063437308421278851140253538604815869848682781135193774472480292420096757",
                    10
                )
            )
        ];
        let error = vm.verify_auto_deductions();
        assert_eq!(error.as_ref().unwrap_err().to_string(), "Inconsistent auto-deduction for builtin ec_op_builtin, expected 2739017437753868763038285897969098325279422804143820990343394856167768859289, got Some(Int(2778063437308421278851140253538604815869848682781135193774472480292420096757))");
        assert_matches!(
            error,
            Err(VirtualMachineError::InconsistentAutoDeduction(bx))
            if *bx == (EC_OP_BUILTIN_NAME,
                    MaybeRelocatable::Int(felt_str!(
                        "2739017437753868763038285897969098325279422804143820990343394856167768859289"
                    )),
                    Some(MaybeRelocatable::Int(felt_str!(
                        "2778063437308421278851140253538604815869848682781135193774472480292420096757"
                    ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /* Program used:
    %builtins bitwise
    from starkware.cairo.common.bitwise import bitwise_and
    from starkware.cairo.common.cairo_builtins import BitwiseBuiltin


    func main{bitwise_ptr: BitwiseBuiltin*}():
        let (result) = bitwise_and(12, 10)  # Binary (1100, 1010).
        assert result = 8  # Binary 1000.
        return()
    end
    */
    fn verify_auto_deductions_bitwise() {
        let mut builtin = BitwiseBuiltinRunner::new(&BitwiseInstanceDef::default(), true);
        builtin.base = 2;
        let mut vm = vm!();
        vm.builtin_runners.push(builtin.into());
        vm.segments = segments![((2, 0), 12), ((2, 1), 10)];
        assert_matches!(vm.verify_auto_deductions(), Ok(()));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /* Program used:
    %builtins bitwise
    from starkware.cairo.common.bitwise import bitwise_and
    from starkware.cairo.common.cairo_builtins import BitwiseBuiltin


    func main{bitwise_ptr: BitwiseBuiltin*}():
        let (result) = bitwise_and(12, 10)  # Binary (1100, 1010).
        assert result = 8  # Binary 1000.
        return()
    end
    */
    fn verify_auto_deductions_for_addr_bitwise() {
        let mut builtin = BitwiseBuiltinRunner::new(&BitwiseInstanceDef::default(), true);
        builtin.base = 2;
        let builtin: BuiltinRunner = builtin.into();
        let mut vm = vm!();
        vm.segments = segments![((2, 0), 12), ((2, 1), 10)];
        assert_matches!(
            vm.verify_auto_deductions_for_addr(relocatable!(2, 0), &builtin),
            Ok(())
        );
        assert_matches!(
            vm.verify_auto_deductions_for_addr(relocatable!(2, 1), &builtin),
            Ok(())
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    /* Program used:
    %builtins output pedersen
    from starkware.cairo.common.cairo_builtins import HashBuiltin
    from starkware.cairo.common.hash import hash2
    from starkware.cairo.common.serialize import serialize_word

    func foo(hash_ptr : HashBuiltin*) -> (
        hash_ptr : HashBuiltin*, z
    ):
        # Use a with-statement, since 'hash_ptr' is not an
        # implicit argument.
        with hash_ptr:
            let (z) = hash2(32, 72)
        end
        return (hash_ptr=hash_ptr, z=z)
    end

    func main{output_ptr: felt*, pedersen_ptr: HashBuiltin*}():
        let (pedersen_ptr, a) = foo(pedersen_ptr)
        serialize_word(a)
        return()
    end
     */
    fn verify_auto_deductions_pedersen() {
        let mut builtin = HashBuiltinRunner::new(Some(8), true);
        builtin.base = 3;
        let mut vm = vm!();
        vm.builtin_runners.push(builtin.into());
        vm.segments = segments![((3, 0), 32), ((3, 1), 72)];
        assert_matches!(vm.verify_auto_deductions(), Ok(()));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn can_get_return_values() {
        let mut vm = vm!();
        vm.set_ap(4);
        vm.segments = segments![((1, 0), 1), ((1, 1), 2), ((1, 2), 3), ((1, 3), 4)];
        let expected = vec![
            MaybeRelocatable::Int(Felt252::new(1_i32)),
            MaybeRelocatable::Int(Felt252::new(2_i32)),
            MaybeRelocatable::Int(Felt252::new(3_i32)),
            MaybeRelocatable::Int(Felt252::new(4_i32)),
        ];
        assert_eq!(vm.get_return_values(4).unwrap(), expected);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_return_values_fails_when_ap_is_0() {
        let mut vm = vm!();
        vm.segments = segments![((1, 0), 1), ((1, 1), 2), ((1, 2), 3), ((1, 3), 4)];
        assert_matches!(vm.get_return_values(3),
            Err(MemoryError::FailedToGetReturnValues(bx))
            if *bx == (3, Relocatable::from((1,0))));
    }

    /*
    Program used for this test:
    from starkware.cairo.common.alloc import alloc
    func main{}():
        let vec: felt* = alloc()
        assert vec[0] = 1
        return()
    end
    Memory: {RelocatableValue(segment_index=0, offset=0): 290341444919459839,
        RelocatableValue(segment_index=0, offset=1): 1,
        RelocatableValue(segment_index=0, offset=2): 2345108766317314046,
        RelocatableValue(segment_index=0, offset=3): 1226245742482522112,
        RelocatableValue(segment_index=0, offset=4): 3618502788666131213697322783095070105623107215331596699973092056135872020478,
        RelocatableValue(segment_index=0, offset=5): 5189976364521848832,
        RelocatableValue(segment_index=0, offset=6): 1,
        RelocatableValue(segment_index=0, offset=7): 4611826758063128575,
        RelocatableValue(segment_index=0, offset=8): 2345108766317314046,
        RelocatableValue(segment_index=1, offset=0): RelocatableValue(segment_index=2, offset=0),
        RelocatableValue(segment_index=1, offset=1): RelocatableValue(segment_index=3, offset=0)}
     */

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_step_for_preset_memory_with_alloc_hint() {
        let mut vm = vm!(true);
        let hint_data = vec![any_box!(HintProcessorData::new_default(
            "memory[ap] = segments.add()".to_string(),
            HashMap::new(),
        ))];

        //Initialzie registers
        run_context!(vm, 3, 2, 2);

        //Create program and execution segments
        for _ in 0..2 {
            vm.segments.add();
        }
        //Initialize memory

        let mut hint_processor = BuiltinHintProcessor::new_empty();

        vm.segments = segments![
            ((0, 0), 290341444919459839_i64),
            ((0, 1), 1),
            ((0, 2), 2345108766317314046_i64),
            ((0, 3), 1226245742482522112_i64),
            (
                (0, 4),
                (
                    "3618502788666131213697322783095070105623107215331596699973092056135872020478",
                    10
                )
            ),
            ((0, 5), 5189976364521848832_i64),
            ((0, 6), 1),
            ((0, 7), 4611826758063128575_i64),
            ((0, 8), 2345108766317314046_i64),
            ((1, 0), (2, 0)),
            ((1, 1), (3, 0))
        ];

        //Run Steps
        for _ in 0..6 {
            let hint_data = if vm.run_context.pc == (0, 0).into() {
                &hint_data[0..]
            } else {
                &hint_data[0..0]
            };
            assert_matches!(
                vm.step(
                    &mut hint_processor,
                    exec_scopes_ref!(),
                    hint_data,
                    &HashMap::new()
                ),
                Ok(())
            );
        }
        //Compare trace
        let trace = vm.trace.unwrap();
        trace_check(
            &trace,
            &[
                (3, 2, 2),
                (0, 4, 4),
                (2, 5, 4),
                (5, 5, 2),
                (7, 6, 2),
                (8, 6, 2),
            ],
        );

        //Compare final register values
        assert_eq!(vm.run_context.pc, Relocatable::from((3, 0)));
        assert_eq!(vm.run_context.ap, 6);
        assert_eq!(vm.run_context.fp, 0);

        //Check that the array created through alloc contains the element we inserted
        //As there are no builtins present, the next segment crated will have the index 2
        check_memory!(vm.segments.memory, ((2, 0), 1));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_get_builtin_runners() {
        let mut vm = vm!();
        let hash_builtin = HashBuiltinRunner::new(Some(8), true);
        let bitwise_builtin = BitwiseBuiltinRunner::new(&BitwiseInstanceDef::default(), true);
        vm.builtin_runners.push(hash_builtin.into());
        vm.builtin_runners.push(bitwise_builtin.into());

        let builtins = vm.get_builtin_runners();

        assert_eq!(builtins[0].name(), HASH_BUILTIN_NAME);
        assert_eq!(builtins[1].name(), BITWISE_BUILTIN_NAME);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn disable_trace() {
        let mut vm = VirtualMachine::new(true);
        assert!(vm.trace.is_some());
        vm.disable_trace();
        assert!(vm.trace.is_none());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_for_continuous_memory() {
        let mut vm = vm!();
        vm.segments = segments![((1, 0), 2), ((1, 1), 3), ((1, 2), 4)];

        let value1 = MaybeRelocatable::from(Felt252::new(2_i32));
        let value2 = MaybeRelocatable::from(Felt252::new(3_i32));
        let value3 = MaybeRelocatable::from(Felt252::new(4_i32));

        let expected_vec = vec![
            Some(Cow::Borrowed(&value1)),
            Some(Cow::Borrowed(&value2)),
            Some(Cow::Borrowed(&value3)),
        ];
        assert_eq!(vm.get_range(Relocatable::from((1, 0)), 3), expected_vec);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_for_non_continuous_memory() {
        let mut vm = vm!();
        vm.segments = segments![((1, 0), 2), ((1, 1), 3), ((1, 3), 4)];

        let value1 = MaybeRelocatable::from(Felt252::new(2_i32));
        let value2 = MaybeRelocatable::from(Felt252::new(3_i32));
        let value3 = MaybeRelocatable::from(Felt252::new(4_i32));

        let expected_vec = vec![
            Some(Cow::Borrowed(&value1)),
            Some(Cow::Borrowed(&value2)),
            None,
            Some(Cow::Borrowed(&value3)),
        ];
        assert_eq!(vm.get_range(Relocatable::from((1, 0)), 4), expected_vec);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_continuous_range_for_continuous_memory() {
        let mut vm = vm!();
        vm.segments = segments![((1, 0), 2), ((1, 1), 3), ((1, 2), 4)];

        let value1 = MaybeRelocatable::from(Felt252::new(2_i32));
        let value2 = MaybeRelocatable::from(Felt252::new(3_i32));
        let value3 = MaybeRelocatable::from(Felt252::new(4_i32));

        let expected_vec = vec![value1, value2, value3];
        assert_eq!(
            vm.get_continuous_range(Relocatable::from((1, 0)), 3),
            Ok(expected_vec)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_continuous_range_for_non_continuous_memory() {
        let mut vm = vm!();
        vm.segments = segments![((1, 0), 2), ((1, 1), 3), ((1, 3), 4)];

        assert_eq!(
            vm.get_continuous_range(Relocatable::from((1, 0)), 3),
            Err(MemoryError::GetRangeMemoryGap(Box::new(((1, 0).into(), 3))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_segment_used_size_after_computing_used() {
        let mut vm = vm!();
        vm.segments = segments![
            ((0, 2), 1),
            ((0, 5), 1),
            ((0, 7), 1),
            ((1, 1), 1),
            ((2, 2), 1),
            ((2, 4), 1),
            ((2, 7), 1)
        ];
        vm.segments.compute_effective_sizes();
        assert_eq!(Some(8), vm.get_segment_used_size(2));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_segment_size_before_computing_used() {
        let vm = vm!();
        assert_eq!(None, vm.get_segment_size(2));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_segment_size_before_computing_used_set_size() {
        let mut vm = vm!();
        vm.segments.segment_sizes.insert(2, 2);
        assert_eq!(Some(2), vm.get_segment_size(2));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_segment_size_after_computing_used() {
        let mut vm = vm!();
        vm.segments = segments![
            ((0, 2), 1),
            ((0, 5), 1),
            ((0, 7), 1),
            ((1, 1), 1),
            ((2, 2), 1),
            ((2, 4), 1),
            ((2, 7), 1)
        ];
        vm.segments.compute_effective_sizes();
        assert_eq!(Some(8), vm.get_segment_size(2));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_segment_used_size_before_computing_used() {
        let vm = vm!();
        assert_eq!(None, vm.get_segment_used_size(2));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_and_set_pc() {
        let mut vm = vm!();
        vm.set_pc(Relocatable {
            segment_index: 3,
            offset: 4,
        });
        assert_eq!(
            vm.get_pc(),
            Relocatable {
                segment_index: 3,
                offset: 4
            }
        )
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_and_set_fp() {
        let mut vm = vm!();
        vm.set_fp(3);
        assert_eq!(
            vm.get_fp(),
            Relocatable {
                segment_index: 1,
                offset: 3
            }
        )
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_maybe_key_not_in_memory() {
        let vm = vm!();
        assert_eq!(
            vm.get_maybe(&Relocatable {
                segment_index: 5,
                offset: 2
            }),
            None
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_maybe_error() {
        let vm = vm!();
        assert_eq!(
            vm.get_maybe(&MaybeRelocatable::Int(Felt252::new(0_i32))),
            None,
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn end_run_error() {
        let mut vm = vm!();
        let scopes = exec_scopes_ref!();
        scopes.enter_scope(HashMap::new());

        assert_matches!(
            vm.end_run(scopes),
            Err(VirtualMachineError::MainScopeError(
                ExecScopeError::NoScopeError
            ))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn add_temporary_segments() {
        let mut vm = vm!();
        let mut _base = vm.add_temporary_segment();
        assert_eq!(
            _base,
            Relocatable {
                segment_index: -1,
                offset: 0
            }
        );
        let mut _base = vm.add_temporary_segment();
        assert_eq!(
            _base,
            Relocatable {
                segment_index: -2,
                offset: 0
            }
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn decode_current_instruction_invalid_encoding() {
        let mut vm = vm!();
        vm.segments = segments![((0, 0), ("112233445566778899", 16))];
        assert_matches!(
            vm.decode_current_instruction(),
            Err(VirtualMachineError::InvalidInstructionEncoding)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn add_relocation_rule_test() {
        let mut vm = vm!();

        assert_eq!(
            vm.add_relocation_rule((-1, 0).into(), (1, 2).into()),
            Ok(()),
        );
        assert_eq!(
            vm.add_relocation_rule((-2, 0).into(), (-1, 1).into()),
            Ok(()),
        );
        assert_eq!(
            vm.add_relocation_rule((5, 0).into(), (0, 0).into()),
            Err(MemoryError::AddressNotInTemporarySegment(5)),
        );
        assert_eq!(
            vm.add_relocation_rule((-3, 6).into(), (0, 0).into()),
            Err(MemoryError::NonZeroOffset(6)),
        );
        assert_eq!(
            vm.add_relocation_rule((-1, 0).into(), (0, 0).into()),
            Err(MemoryError::DuplicatedRelocation(-1)),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn gen_arg_relocatable() {
        let mut vm = vm!();

        assert_matches!(
            vm.gen_arg(&mayberelocatable!(0, 0)),
            Ok(x) if x == mayberelocatable!(0, 0)
        );
    }

    /// Test that the call to .gen_arg() with a bigint and no prime number just
    /// passes the value through.
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn gen_arg_bigint() {
        let mut vm = vm!();

        assert_matches!(
            vm.gen_arg(&mayberelocatable!(1234)),
            Ok(x) if x == mayberelocatable!(1234)
        );
    }

    /// Test that the call to .gen_arg() with a bigint and a prime number passes
    /// the value through after applying the modulo.
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn gen_arg_bigint_prime() {
        let mut vm = vm!();
        let prime = felt_str!(felt::PRIME_STR[2..], 16);
        let prime_maybe = MaybeRelocatable::from(prime);

        assert_matches!(vm.gen_arg(&prime_maybe), Ok(x) if x == mayberelocatable!(0));
    }

    /// Test that the call to .gen_arg() with a Vec<MaybeRelocatable> writes its
    /// contents into a new segment and returns a pointer to it.
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn gen_arg_vec() {
        let mut vm = vm!();

        assert_matches!(
            vm.gen_arg(&vec![
                mayberelocatable!(0),
                mayberelocatable!(1),
                mayberelocatable!(2),
                mayberelocatable!(3),
                mayberelocatable!(0, 0),
                mayberelocatable!(0, 1),
                mayberelocatable!(0, 2),
                mayberelocatable!(0, 3),
            ]),
            Ok(x) if x == mayberelocatable!(0, 0)
        );
    }

    /// Test that compute_effective_sizes() works as intended.
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_effective_sizes() {
        let mut vm = vm!();

        let segment = vm.segments.add();
        vm.load_data(
            segment,
            &vec![
                mayberelocatable!(1),
                mayberelocatable!(2),
                mayberelocatable!(3),
                mayberelocatable!(4),
            ],
        )
        .expect("Could not load data into memory.");

        assert_eq!(vm.segments.compute_effective_sizes(), &vec![4]);
    }

    /// Test that compute_segment_effective_sizes() works as intended.
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn compute_segment_effective_sizes() {
        let mut vm = vm!();

        let segment = vm.segments.add();
        vm.load_data(
            segment,
            &vec![
                mayberelocatable!(1),
                mayberelocatable!(2),
                mayberelocatable!(3),
                mayberelocatable!(4),
            ],
        )
        .expect("Could not load data into memory.");

        assert_eq!(vm.segments.compute_effective_sizes(), &vec![4]);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn mark_as_accessed() {
        let mut vm = vm!();
        vm.run_finished = true;
        vm.segments.memory = memory![
            ((0, 0), 0),
            ((0, 1), 0),
            ((0, 2), 1),
            ((0, 10), 10),
            ((1, 1), 1)
        ];
        vm.mark_address_range_as_accessed((0, 0).into(), 3).unwrap();
        vm.mark_address_range_as_accessed((0, 10).into(), 2)
            .unwrap();
        vm.mark_address_range_as_accessed((1, 1).into(), 1).unwrap();
        //Check that the following addresses have been accessed:
        // Addresses have been copied from python execution:
        let mem = &vm.segments.memory.data;
        assert!(mem[0][0].as_ref().unwrap().is_accessed());
        assert!(mem[0][1].as_ref().unwrap().is_accessed());
        assert!(mem[0][2].as_ref().unwrap().is_accessed());
        assert!(mem[0][10].as_ref().unwrap().is_accessed());
        assert!(mem[1][1].as_ref().unwrap().is_accessed());
        assert_eq!(
            vm.segments
                .memory
                .get_amount_of_accessed_addresses_for_segment(0),
            Some(4)
        );
        assert_eq!(
            vm.segments
                .memory
                .get_amount_of_accessed_addresses_for_segment(1),
            Some(1)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn mark_as_accessed_run_not_finished() {
        let mut vm = vm!();
        assert_matches!(
            vm.mark_address_range_as_accessed((0, 0).into(), 3),
            Err(VirtualMachineError::RunNotFinished)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn mark_as_accessed_missing_accessed_addresses() {
        let mut vm = vm!();
        assert_matches!(
            vm.mark_address_range_as_accessed((0, 0).into(), 3),
            Err(VirtualMachineError::RunNotFinished)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_traceback_entries_bad_usort() {
        let program = Program::from_bytes(
            include_bytes!("../../../cairo_programs/bad_programs/bad_usort.json"),
            Some("main"),
        )
        .unwrap();

        let mut hint_processor = BuiltinHintProcessor::new_empty();
        let mut cairo_runner = cairo_runner!(program, "all_cairo", false);
        let mut vm = vm!();

        let end = cairo_runner.initialize(&mut vm).unwrap();
        assert!(cairo_runner
            .run_until_pc(end, &mut vm, &mut hint_processor)
            .is_err());
        let expected_traceback = vec![
            (Relocatable::from((1, 3)), Relocatable::from((0, 97))),
            (Relocatable::from((1, 14)), Relocatable::from((0, 30))),
            (Relocatable::from((1, 26)), Relocatable::from((0, 60))),
        ];
        assert_eq!(vm.get_traceback_entries(), expected_traceback);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_traceback_entries_bad_dict_update() {
        let program = Program::from_bytes(
            include_bytes!("../../../cairo_programs/bad_programs/bad_dict_update.json"),
            Some("main"),
        )
        .unwrap();

        let mut hint_processor = BuiltinHintProcessor::new_empty();
        let mut cairo_runner = cairo_runner!(program, "all_cairo", false);
        let mut vm = vm!();

        let end = cairo_runner.initialize(&mut vm).unwrap();
        assert!(cairo_runner
            .run_until_pc(end, &mut vm, &mut hint_processor)
            .is_err());
        let expected_traceback = vec![(Relocatable::from((1, 2)), Relocatable::from((0, 34)))];
        assert_eq!(vm.get_traceback_entries(), expected_traceback);
    }

    #[test]
    fn builder_test() {
        let virtual_machine_builder: VirtualMachineBuilder = VirtualMachineBuilder::default()
            .run_finished(true)
            .current_step(12)
            .builtin_runners(vec![BuiltinRunner::from(HashBuiltinRunner::new(
                Some(12),
                true,
            ))])
            .run_context(RunContext {
                pc: Relocatable::from((0, 0)),
                ap: 18,
                fp: 0,
            })
            .segments(MemorySegmentManager {
                segment_sizes: HashMap::new(),
                segment_used_sizes: Some(vec![1]),
                public_memory_offsets: HashMap::new(),
                memory: Memory::new(),
            })
            .skip_instruction_execution(true)
            .trace(Some(vec![TraceEntry {
                pc: 1,
                ap: 1,
                fp: 1,
            }]));

        #[cfg(feature = "hooks")]
        fn before_first_step_hook(
            _vm: &mut VirtualMachine,
            _runner: &mut CairoRunner,
            _hint_data: &[Box<dyn Any>],
        ) -> Result<(), VirtualMachineError> {
            Err(VirtualMachineError::Unexpected)
        }
        #[cfg(feature = "hooks")]
        let virtual_machine_builder = virtual_machine_builder.hooks(crate::vm::hooks::Hooks::new(
            Some(std::sync::Arc::new(before_first_step_hook)),
            None,
            None,
        ));

        #[allow(unused_mut)]
        let mut virtual_machine_from_builder = virtual_machine_builder.build();

        assert!(virtual_machine_from_builder.run_finished);
        assert_eq!(virtual_machine_from_builder.current_step, 12);
        assert_eq!(
            virtual_machine_from_builder
                .builtin_runners
                .get(0)
                .unwrap()
                .name(),
            "pedersen_builtin"
        );
        assert_eq!(virtual_machine_from_builder.run_context.ap, 18,);
        assert_eq!(
            virtual_machine_from_builder.segments.segment_used_sizes,
            Some(vec![1])
        );
        assert!(virtual_machine_from_builder.skip_instruction_execution,);
        assert_eq!(
            virtual_machine_from_builder.trace,
            Some(vec![TraceEntry {
                pc: 1,
                ap: 1,
                fp: 1,
            }])
        );
        #[cfg(feature = "hooks")]
        {
            let program = crate::types::program::Program::from_bytes(
                include_bytes!("../../../cairo_programs/sqrt.json"),
                Some("main"),
            )
            .expect("Call to `Program::from_file()` failed.");
            let mut hint_processor = BuiltinHintProcessor::new_empty();
            let mut cairo_runner = cairo_runner!(program);
            let end = cairo_runner
                .initialize(&mut virtual_machine_from_builder)
                .unwrap();

            assert!(cairo_runner
                .run_until_pc(end, &mut virtual_machine_from_builder, &mut hint_processor)
                .is_err());
        }
    }
}
