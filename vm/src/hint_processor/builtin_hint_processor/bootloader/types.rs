use std::path::PathBuf;

use serde::{de, Deserialize, Deserializer};

use felt::Felt252;

use crate::serde::deserialize_program::deserialize_and_parse_program;
use crate::types::program::Program;

pub type BootloaderVersion = u64;

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
pub struct Task {
    #[serde(deserialize_with = "deserialize_program")]
    pub program: Program,
}

fn deserialize_program<'de, D>(deserializer: D) -> Result<Program, D::Error>
where
    D: Deserializer<'de>,
{
    let obj_raw: &str = Deserialize::deserialize(deserializer)?;
    deserialize_and_parse_program(obj_raw.as_bytes(), Some("main")).map_err(de::Error::custom)
}

impl Task {
    pub fn get_program(&self) -> &Program {
        &self.program
    }
}

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
