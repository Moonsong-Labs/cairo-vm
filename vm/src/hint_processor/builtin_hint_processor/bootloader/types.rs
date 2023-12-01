use felt::Felt252;
use serde::Deserialize;
use std::path::PathBuf;

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
pub struct Task {}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct TaskSpec {
    pub task: Task,
}

impl TaskSpec {
    pub fn load_task(&self) -> &Task {
        &self.task
    }
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct SimpleBootloaderInput {
    pub fact_topologies_path: Option<PathBuf>,
    pub single_page: bool,
    pub tasks: Vec<TaskSpec>,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct BootloaderInput {
    pub simple_bootloader_input: SimpleBootloaderInput,
    pub bootloader_config: BootloaderConfig,
    pub packed_outputs: Vec<PackedOutput>,
}
