use crate::hint_processor::builtin_hint_processor::bootloader::types::PackedOutput;
use crate::types::errors::math_errors::MathError;
use crate::types::relocatable::Relocatable;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::errors::runner_errors::RunnerError;
use crate::vm::runners::builtin_runner::OutputBuiltinRunner;
use felt::Felt252;
use serde::Serialize;
use std::fs::File;
use std::path::Path;

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct FactTopology {
    #[allow(dead_code)]
    pub tree_structure: Vec<Felt252>,
    pub page_sizes: Vec<usize>,
}

#[derive(Serialize)]
struct FactTopologyFile<'a> {
    fact_topologies: Vec<&'a FactTopology>,
}

impl AsRef<FactTopology> for FactTopology {
    fn as_ref(&self) -> &FactTopology {
        self
    }
}

#[derive(Debug, thiserror_no_std::Error)]
pub enum FactTopologyError {
    #[error("Expected {0} fact topologies but got {1}")]
    WrongNumberOfFactTopologies(usize, usize),

    #[error("Composite packed outputs are not supported yet")]
    CompositePackedOutputNotSupported(PackedOutput),

    #[error("Could not add page to output: {0}")]
    FailedToAddOutputPage(#[from] RunnerError),

    #[error(transparent)]
    Math(#[from] MathError),
}

impl Into<HintError> for FactTopologyError {
    fn into(self) -> HintError {
        match self {
            FactTopologyError::WrongNumberOfFactTopologies(_, _) => {
                HintError::AssertionFailed(self.to_string().into_boxed_str())
            }
            FactTopologyError::CompositePackedOutputNotSupported(_) => HintError::CustomHint(
                "Cannot compute fact topologies for composite packed outputs (yet)"
                    .to_string()
                    .into_boxed_str(),
            ),
            FactTopologyError::FailedToAddOutputPage(e) => HintError::CustomHint(
                format!("Cannot add output page to output segment: {}", e).into_boxed_str(),
            ),
            FactTopologyError::Math(e) => HintError::Math(e),
        }
    }
}

#[derive(thiserror_no_std::Error, Debug)]
pub enum WriteFactTopologiesError {
    #[error("Failed to create fact topology file: {0}")]
    Io(#[from] std::io::Error),
    #[error("Failed to serialize fact topologies: {0}")]
    Serialization(#[from] serde_json::Error),
}

impl Into<HintError> for WriteFactTopologiesError {
    fn into(self) -> HintError {
        HintError::CustomHint(self.to_string().into_boxed_str())
    }
}

/// Flattens and extracts the fact topologies from packed outputs.
///
/// Note that `packed_outputs` and `fact_topologies` must have the same length.
///
/// * `packed_outputs`: Packed outputs.
/// * `fact_topologies`: Fact topologies.
pub fn compute_fact_topologies<'a>(
    packed_outputs: &Vec<PackedOutput>,
    fact_topologies: &'a Vec<FactTopology>,
) -> Result<Vec<&'a FactTopology>, FactTopologyError> {
    if packed_outputs.len() != fact_topologies.len() {
        return Err(FactTopologyError::WrongNumberOfFactTopologies(
            packed_outputs.len(),
            fact_topologies.len(),
        ));
    }

    let mut plain_fact_topologies = vec![];

    for (packed_output, fact_topology) in std::iter::zip(packed_outputs, fact_topologies) {
        match packed_output {
            PackedOutput::Plain(_) => {
                plain_fact_topologies.push(fact_topology);
            }
            PackedOutput::Composite(_) => {
                return Err(FactTopologyError::CompositePackedOutputNotSupported(
                    packed_output.clone(),
                ));
            }
        }
    }

    Ok(plain_fact_topologies)
}

/// Adds page to the output builtin for the specified fact topology.
///
/// * `fact_topology`: Fact topology.
/// * `output_builtin`: Output builtin of the VM.
/// * `current_page_id`: First page ID to use.
/// * `output_start`: Start of the output range for this fact topology.
///
/// Reimplements the following Python code:
///     offset = 0
///     for i, page_size in enumerate(fact_topology.page_sizes):
///         output_builtin.add_page(
///             page_id=cur_page_id + i, page_start=output_start + offset, page_size=page_size
///         )
///         offset += page_size
///
///     return len(fact_topology.page_sizes)
fn add_consecutive_output_pages(
    fact_topology: &FactTopology,
    output_builtin: &mut OutputBuiltinRunner,
    current_page_id: usize,
    output_start: &Relocatable,
) -> Result<usize, FactTopologyError> {
    let mut offset = 0;

    for (i, page_size) in fact_topology.page_sizes.iter().copied().enumerate() {
        let page_id = current_page_id + i;
        let page_start = output_start + offset;
        output_builtin.add_page(page_id, page_start, page_size)?;
        offset += page_size;
    }

    Ok(fact_topology.page_sizes.len())
}

/// Given the fact_topologies of the tasks that were run by bootloader, configure the
/// corresponding pages in the output builtin.
///
/// Assumes that the bootloader output 2 words per task.
///
/// * `plain_fact_topologies`: Fact topologies.
/// * `output_start`: Start of the bootloader output.
/// * `output_builtin`: Output builtin of the VM.
///
/// Reimplements the following Python code:
/// cur_page_id = 1
/// for fact_topology in fact_topologies:
///     # Skip bootloader output for each task.
///     output_start += 2
///     cur_page_id += add_consecutive_output_pages(
///         fact_topology=fact_topology,
///         output_builtin=output_builtin,
///         cur_page_id=cur_page_id,
///         output_start=output_start,
///     )
///     output_start += sum(fact_topology.page_sizes)

pub fn configure_fact_topologies<FT: AsRef<FactTopology>>(
    plain_fact_topologies: &[FT],
    output_start: &mut Relocatable,
    output_builtin: &mut OutputBuiltinRunner,
) -> Result<(), FactTopologyError> {
    // Each task may use a few memory pages. Start from page 1 (as page 0 is reserved for the
    // bootloader program and arguments).
    let mut current_page_id: usize = 1;
    for fact_topology in plain_fact_topologies {
        // Skip bootloader output for each task
        *output_start = (*output_start + 2usize)?;

        current_page_id += add_consecutive_output_pages(
            fact_topology.as_ref(),
            output_builtin,
            current_page_id,
            output_start,
        )?;
        let total_page_sizes: usize = fact_topology.as_ref().page_sizes.iter().sum();
        *output_start = (*output_start + total_page_sizes)?;
    }

    Ok(())
}

/// Writes fact topologies to a file, as JSON.
///
/// * `path`: File path.
/// * `fact_topologies`: Fact topologies to write.
pub fn write_to_fact_topologies_file<FT: AsRef<FactTopology>>(
    path: &Path,
    fact_topologies: &Vec<FT>,
) -> Result<(), WriteFactTopologiesError> {
    let mut file = File::create(path)?;
    let fact_topology_file = FactTopologyFile {
        fact_topologies: fact_topologies.iter().map(|ft| ft.as_ref()).collect(),
    };
    serde_json::to_writer(&mut file, &fact_topology_file)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hint_processor::builtin_hint_processor::bootloader::types::PackedOutput;
    use crate::vm::runners::cairo_pie::PublicMemoryPage;
    use rstest::{fixture, rstest};
    use std::collections::HashMap;

    #[fixture]
    fn packed_outputs() -> Vec<PackedOutput> {
        vec![
            PackedOutput::Plain(vec![]),
            PackedOutput::Plain(vec![]),
            PackedOutput::Plain(vec![]),
        ]
    }

    #[fixture]
    fn fact_topologies() -> Vec<FactTopology> {
        vec![
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![1usize],
            },
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![1usize, 2usize],
            },
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![3usize],
            },
        ]
    }

    #[rstest]
    fn test_compute_fact_topologies(
        packed_outputs: Vec<PackedOutput>,
        fact_topologies: Vec<FactTopology>,
    ) {
        let plain_fact_topologies = compute_fact_topologies(&packed_outputs, &fact_topologies)
            .expect("Failed to compute fact topologies");
        for (topology, plain_topology) in std::iter::zip(&fact_topologies, plain_fact_topologies) {
            assert_eq!(topology, plain_topology);
        }
    }

    #[test]
    /// Composite outputs are not supported (yet).
    fn test_compute_fact_topologies_composite_output() {
        let packed_outputs = vec![PackedOutput::Composite(vec![])];
        let fact_topologies = vec![FactTopology {
            tree_structure: vec![],
            page_sizes: vec![],
        }];
        let result = compute_fact_topologies(&packed_outputs, &fact_topologies);
        assert!(matches!(
            result,
            Err(FactTopologyError::CompositePackedOutputNotSupported(_))
        ));
    }

    #[test]
    /// Both arguments to `compute_fact_topologies` must have the same length.
    fn test_compute_fact_topologies_arg_len_mismatch() {
        let packed_outputs = vec![PackedOutput::Plain(vec![])];
        let fact_topologies = vec![];

        let result = compute_fact_topologies(&packed_outputs, &fact_topologies);
        assert!(
            matches!(result, Err(FactTopologyError::WrongNumberOfFactTopologies(n_outputs, n_topologies)) if n_outputs == packed_outputs.len() && n_topologies == fact_topologies.len())
        )
    }

    #[rstest]
    fn test_add_consecutive_output_pages() {
        let fact_topology = FactTopology {
            tree_structure: vec![],
            page_sizes: vec![1usize, 2usize, 1usize],
        };
        let mut output_builtin = OutputBuiltinRunner::new(true);
        let page_id = 1;
        let output_start = Relocatable {
            segment_index: 0,
            offset: 10,
        };

        let result = add_consecutive_output_pages(
            &fact_topology,
            &mut output_builtin,
            page_id,
            &output_start,
        )
        .expect("Adding consecutive output pages failed unexpectedly");
        assert_eq!(result, fact_topology.page_sizes.len());

        assert_eq!(
            output_builtin.pages,
            HashMap::from([
                (1, PublicMemoryPage { start: 10, size: 1 }),
                (2, PublicMemoryPage { start: 11, size: 2 }),
                (3, PublicMemoryPage { start: 13, size: 1 })
            ])
        );
    }

    #[rstest]
    fn test_configure_fact_topologies(fact_topologies: Vec<FactTopology>) {
        let mut output_builtin = OutputBuiltinRunner::new(true);
        let mut output_start = Relocatable {
            segment_index: output_builtin.base() as isize,
            offset: 10,
        };

        let result =
            configure_fact_topologies(&fact_topologies, &mut output_start, &mut output_builtin)
                .expect("Configuring fact topologies failed unexpectedly");

        assert_eq!(result, ());

        // We expect the offset to 2 + sum(page_sizes) for each fact topology
        let expected_offset: usize = fact_topologies.iter().flat_map(|ft| &ft.page_sizes).sum();
        let expected_offset = expected_offset + fact_topologies.len() * 2;
        assert_eq!(output_start.segment_index, output_builtin.base() as isize);
        assert_eq!(output_start.offset, 10 + expected_offset);

        assert_eq!(
            output_builtin.pages,
            HashMap::from([
                (1, PublicMemoryPage { start: 12, size: 1 }),
                (2, PublicMemoryPage { start: 15, size: 1 }),
                (3, PublicMemoryPage { start: 16, size: 2 }),
                (4, PublicMemoryPage { start: 20, size: 3 })
            ])
        );
    }
}
