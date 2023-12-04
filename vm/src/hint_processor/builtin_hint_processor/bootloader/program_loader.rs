use crate::hint_processor::builtin_hint_processor::bootloader::types::BootloaderVersion;
use crate::serde::deserialize_program::BuiltinName;
use crate::types::program::Program;
use crate::types::relocatable::Relocatable;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::errors::memory_errors::MemoryError;
use crate::vm::vm_memory::memory::Memory;
use felt::Felt252;

#[derive(thiserror_no_std::Error, Debug)]
pub enum ProgramLoaderError {
    #[error(transparent)]
    Memory(#[from] MemoryError),

    #[error("Program has no entrypoint")]
    NoEntrypoint,
}

impl Into<HintError> for ProgramLoaderError {
    fn into(self) -> HintError {
        match self {
            ProgramLoaderError::Memory(e) => HintError::Memory(e),
            _ => HintError::CustomHint(self.to_string().into_boxed_str()),
        }
    }
}

/// Creates an instance of `Felt252` from a builtin name.
///
/// Converts the builtin name to bytes then attempts to create a felt from
/// these bytes. This function will fail if the builtin name is over 31 characters.
fn builtin_to_felt(builtin: &BuiltinName) -> Result<Felt252, ProgramLoaderError> {
    // The Python implementation uses the builtin name without suffix
    let builtin_name = builtin
        .name()
        .strip_suffix("_builtin")
        .unwrap_or(builtin.name());

    Ok(Felt252::from_bytes_be(builtin_name.as_bytes()))
}

pub struct LoadedProgram {
    /// Start of the program code in the VM memory.
    pub code_address: Relocatable,
    /// Total size of the program in memory, header included.
    pub size: usize,
}

/// Loads a Cairo program in the VM memory.
pub struct ProgramLoader<'vm> {
    /// Memory accessor.
    memory: &'vm mut Memory,
    /// Offset of the builtin list array in the Cairo VM memory.
    builtins_offset: usize,
}

impl<'vm> ProgramLoader<'vm> {
    pub fn new(memory: &'vm mut Memory, builtins_offset: usize) -> Self {
        Self {
            memory,
            builtins_offset,
        }
    }

    fn load_builtins(
        &mut self,
        builtin_list_ptr: &Relocatable,
        builtins: &[BuiltinName],
    ) -> Result<(), ProgramLoaderError> {
        for (index, builtin) in builtins.iter().enumerate() {
            let builtin_felt = builtin_to_felt(&builtin)?;
            self.memory
                .insert_value(builtin_list_ptr + index, builtin_felt)?;
        }

        Ok(())
    }

    fn load_header(
        &mut self,
        base_address: &Relocatable,
        program: &Program,
        bootloader_version: Option<BootloaderVersion>,
    ) -> Result<usize, ProgramLoaderError> {
        // Map the header struct as memory addresses
        let data_length_ptr = base_address.clone();
        let bootloader_version_ptr = base_address + 1;
        let program_main_ptr = base_address + 2;
        let n_builtins_ptr = base_address + 3;
        let builtin_list_ptr = base_address + 4;

        let program_data = &program.shared_program_data.data;

        let builtins = &program.builtins;
        let n_builtins = builtins.len();
        let header_size = self.builtins_offset + n_builtins;

        // data_length does not include the data_length header field in the calculation.
        let data_length = header_size - 1 + program_data.len();
        let program_main = program
            .shared_program_data
            .main
            .ok_or(ProgramLoaderError::NoEntrypoint)?;

        let bootloader_version = bootloader_version.unwrap_or(0);

        self.memory
            .insert_value(data_length_ptr, data_length.clone())?;
        self.memory.insert_value(
            bootloader_version_ptr,
            Felt252::from(bootloader_version.clone()),
        )?;
        self.memory
            .insert_value(program_main_ptr, program_main.clone())?;
        self.memory
            .insert_value(n_builtins_ptr, n_builtins.clone())?;

        self.load_builtins(&builtin_list_ptr, builtins)?;

        Ok(header_size)
    }

    fn load_code(
        &mut self,
        base_address: &Relocatable,
        program: &Program,
    ) -> Result<(), ProgramLoaderError> {
        for (index, opcode) in program.shared_program_data.data.iter().enumerate() {
            self.memory.insert_value(base_address + index, opcode)?;
        }

        Ok(())
    }

    // builtins = task.get_program().builtins
    // n_builtins = len(builtins)
    // program_data = task.get_program().data
    //
    // # Fill in the program header.
    // header_address = program_header.address_
    // # The program header ends with a list of builtins used by the program.
    // header_size = builtins_offset + n_builtins
    // # data_length does not include the data_length header field in the calculation.
    // program_header.data_length = (header_size - 1) + len(program_data)
    // program_header.program_main = task.get_program().main
    // program_header.n_builtins = n_builtins
    // # Fill in the builtin list in memory.
    // # TODO(ilya, 18/12/2021): Use addr_of(ids.program_header.builtin_list) when available.
    // builtins_address = header_address + builtins_offset
    // for index, builtin in enumerate(builtins):
    //     assert isinstance(builtin, str)
    //     memory[builtins_address + index] = from_bytes(builtin.encode("ascii"))
    //
    // # Fill in the program code in memory.
    // program_address = header_address + header_size
    // for index, opcode in enumerate(program_data):
    //     memory[program_address + index] = opcode
    //
    // return program_address, header_size + len(program_data)
    pub fn load_program(
        &mut self,
        base_address: &Relocatable,
        program: &Program,
        bootloader_version: Option<BootloaderVersion>,
    ) -> Result<LoadedProgram, ProgramLoaderError> {
        let header_size = self.load_header(base_address, program, bootloader_version)?;

        let program_address = base_address + header_size;
        self.load_code(&program_address, program)?;

        Ok(LoadedProgram {
            code_address: program_address,
            size: header_size + program.shared_program_data.data.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::vm_memory::memory_segments::MemorySegmentManager;
    use rstest::{fixture, rstest};

    fn check_loaded_builtins(memory: &Memory, builtins: &[&str], builtin_list_ptr: Relocatable) {
        let builtin_felts = memory
            .get_integer_range(builtin_list_ptr, builtins.len())
            .expect("Builtins not loaded properly in memory");
        for (builtin, felt) in std::iter::zip(vec!["bitwise", "output", "pedersen"], builtin_felts)
        {
            let builtin_from_felt = String::from_utf8(felt.into_owned().to_bytes_be()).expect(
                format!(
                    "Could not decode builtin from memory (expected {})",
                    builtin
                )
                .as_ref(),
            );
            assert_eq!(builtin, builtin_from_felt);
        }
    }

    #[test]
    fn test_load_builtins() {
        let builtins = vec![
            BuiltinName::bitwise,
            BuiltinName::output,
            BuiltinName::pedersen,
        ];

        let mut segments = MemorySegmentManager::new();
        let builtin_list_ptr = segments.add();

        let builtins_offset = 4;
        let mut program_loader = ProgramLoader::new(&mut segments.memory, builtins_offset);

        program_loader
            .load_builtins(&builtin_list_ptr, &builtins)
            .expect("Failed to load builtins in memory");

        check_loaded_builtins(
            &segments.memory,
            &vec!["bitwise", "output", "pedersen"],
            builtin_list_ptr,
        );
    }

    #[fixture]
    fn fibonacci() -> Program {
        let program_content =
            include_bytes!("../../../../../cairo_programs/fibonacci.json").to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    fn check_loaded_header(
        memory: &Memory,
        header_address: Relocatable,
        program: &Program,
        bootloader_version: BootloaderVersion,
    ) {
        let header_felts = memory.get_integer_range(header_address, 4).unwrap();
        let expected_data_length = program.shared_program_data.data.len() + 3;
        let program_main = program.shared_program_data.main.unwrap();
        let n_builtins = program.builtins.len();

        assert_eq!(
            header_felts[0].clone().into_owned(),
            Felt252::from(expected_data_length)
        );
        assert_eq!(
            header_felts[1].clone().into_owned(),
            Felt252::from(bootloader_version)
        );
        assert_eq!(
            header_felts[2].clone().into_owned(),
            Felt252::from(program_main)
        );
        assert_eq!(
            header_felts[3].clone().into_owned(),
            Felt252::from(n_builtins)
        );
    }

    #[rstest]
    fn test_load_header(fibonacci: Program) {
        let mut segments = MemorySegmentManager::new();
        let base_address = segments.add();

        let builtins_offset = 4;
        let mut program_loader = ProgramLoader::new(&mut segments.memory, builtins_offset);

        let bootloader_version: BootloaderVersion = 0;
        program_loader
            .load_header(&base_address, &fibonacci, Some(bootloader_version))
            .expect("Failed to load program header in memory");

        check_loaded_header(
            &segments.memory,
            base_address.clone(),
            &fibonacci,
            bootloader_version,
        );

        let builtin_list_ptr = &base_address + builtins_offset;
        check_loaded_builtins(&segments.memory, &vec![], builtin_list_ptr);
    }

    fn check_loaded_program(memory: &Memory, code_address: Relocatable, program: &Program) {
        let loaded_opcodes = memory
            .get_continuous_range(code_address, program.shared_program_data.data.len())
            .expect("Program not loaded properly in memory");

        for (loaded, original) in std::iter::zip(loaded_opcodes, &program.shared_program_data.data)
        {
            assert_eq!(loaded, *original);
        }
    }

    #[rstest]
    fn test_load_program(fibonacci: Program) {
        let mut segments = MemorySegmentManager::new();
        let base_address = segments.add();

        let builtins_offset = 4;
        let mut program_loader = ProgramLoader::new(&mut segments.memory, builtins_offset);

        let bootloader_version: BootloaderVersion = 0;
        let loaded_program = program_loader
            .load_program(&base_address, &fibonacci, Some(bootloader_version))
            .expect("Failed to load program in memory");

        let header_size = builtins_offset + fibonacci.builtins.len();
        assert_eq!(loaded_program.code_address, &base_address + header_size);

        assert_eq!(
            loaded_program.size,
            header_size + fibonacci.shared_program_data.data.len()
        );

        check_loaded_program(&segments.memory, loaded_program.code_address, &fibonacci);

        check_loaded_header(
            &segments.memory,
            base_address.clone(),
            &fibonacci,
            bootloader_version,
        );

        let builtin_list_ptr = &base_address + builtins_offset;
        check_loaded_builtins(&segments.memory, &vec![], builtin_list_ptr);
    }
}
