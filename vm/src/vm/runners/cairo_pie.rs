use num_bigint::BigUint;
use num_integer::Integer;
use std::io::{Read, Seek};
#[cfg(feature = "std")]
use std::path::Path;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use zip::read::ZipFile;

use super::cairo_runner::ExecutionResources;
use crate::serde::deserialize_utils::deserialize_biguint_from_number;
use crate::types::errors::cairo_pie_error::{CairoPieError, DeserializeMemoryError};
use crate::{
    felt::Felt252,
    serde::deserialize_program::BuiltinName,
    stdlib::{collections::HashMap, prelude::*},
    types::relocatable::{MaybeRelocatable, Relocatable},
};

pub const CAIRO_PIE_VERSION: &str = "1.1";

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct SegmentInfo {
    pub index: isize,
    pub size: usize,
}

impl From<(isize, usize)> for SegmentInfo {
    fn from(value: (isize, usize)) -> Self {
        SegmentInfo {
            index: value.0,
            size: value.1,
        }
    }
}

// A simplified version of Memory, without any additional data besides its elements
// Contains all addr-value pairs, ordered by index and offset
// Allows practical serialization + conversion between CairoPieMemory & Memory
pub type CairoPieMemory = Vec<((usize, usize), MaybeRelocatable)>;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct PublicMemoryPage {
    pub start: usize,
    pub size: usize,
}

// HashMap value based on starknet/core/os/output.cairo usage
pub type Attributes = HashMap<String, Vec<usize>>;
pub type Pages = HashMap<usize, PublicMemoryPage>;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct OutputBuiltinAdditionalData {
    #[serde(skip)]
    pub base: usize,
    pub pages: Pages,
    pub attributes: Attributes,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
#[serde(untagged)]
pub enum BuiltinAdditionalData {
    // Contains verified addresses as contiguous index, value pairs
    Hash(Vec<Relocatable>),
    Output(OutputBuiltinAdditionalData),
    // Signatures are composed of (r, s) tuples
    Signature(HashMap<Relocatable, (Felt252, Felt252)>),
    None,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPie {
    pub metadata: CairoPieMetadata,
    #[serde(serialize_with = "serde_impl::serialize_memory")]
    pub memory: CairoPieMemory,
    pub execution_resources: ExecutionResources,
    pub additional_data: HashMap<String, BuiltinAdditionalData>,
    pub version: CairoPieVersion,
}

fn parse_zip_file<T: DeserializeOwned>(mut zip_file: ZipFile) -> Result<T, CairoPieError> {
    let mut buf = vec![];
    zip_file.read_to_end(&mut buf)?;
    serde_json::from_slice(&buf).map_err(|e| e.into())
}

const N_SEGMENT_BITS: usize = 16;
const N_OFFSET_BITS: usize = 47;
const SEGMENT_MASK: u64 = ((1 << N_SEGMENT_BITS) - 1) << N_OFFSET_BITS;
const OFFSET_MASK: u64 = (1 << N_OFFSET_BITS) - 1;

fn maybe_relocatable_from_le_bytes(bytes: &[u8]) -> MaybeRelocatable {
    // Little-endian -> the relocatable bit is in the last element
    let is_relocatable = (bytes[bytes.len() - 1] & 0x80) != 0;

    if !is_relocatable {
        let felt = Felt252::from_bytes_le(bytes);
        return MaybeRelocatable::Int(felt);
    }

    // Relocatable values are guaranteed to fit in a u64
    let value = {
        let mut value = 0;
        for (index, byte) in bytes[..8].iter().enumerate() {
            value += u64::from(*byte) << (index * 8);
        }
        value
    };

    let segment = (value & SEGMENT_MASK) >> N_OFFSET_BITS;
    let offset = value & OFFSET_MASK;
    MaybeRelocatable::RelocatableValue(Relocatable::from((segment as isize, offset as usize)))
}

fn read_memory_file<R: Read>(
    mut reader: R,
    addr_size: usize,
    felt_size: usize,
) -> Result<CairoPieMemory, DeserializeMemoryError> {
    let memory_cell_size = addr_size + felt_size;
    let mut memory = CairoPieMemory::new();
    let mut pos: usize = 0;

    loop {
        let mut element = vec![0; memory_cell_size];
        match reader.read(&mut element) {
            Ok(n) => {
                if n == 0 {
                    break;
                }
                if n != memory_cell_size {
                    return Err(DeserializeMemoryError::UnexpectedEof);
                }
            }
            Err(e) => return Err(e.into()),
        }
        let (address_bytes, value_bytes) = element.split_at(addr_size);
        let address = maybe_relocatable_from_le_bytes(address_bytes.clone());
        let value = maybe_relocatable_from_le_bytes(value_bytes);

        match address {
            MaybeRelocatable::RelocatableValue(relocatable) => {
                memory.push((
                    (relocatable.segment_index as usize, relocatable.offset),
                    value,
                ));
            }
            MaybeRelocatable::Int(_value) => {
                return Err(DeserializeMemoryError::AddressIsNotRelocatable(pos));
            }
        }
        pos += memory_cell_size;
    }

    Ok(memory)
}

impl CairoPie {
    #[cfg(feature = "std")]

    pub fn from_zip_archive<R: Read + Seek>(
        mut zip: zip::ZipArchive<R>,
    ) -> Result<CairoPie, CairoPieError> {
        let metadata: CairoPieMetadata = parse_zip_file(zip.by_name("metadata.json")?)?;
        let execution_resources: ExecutionResources =
            parse_zip_file(zip.by_name("execution_resources.json")?)?;
        let additional_data: HashMap<String, BuiltinAdditionalData> =
            parse_zip_file(zip.by_name("additional_data.json")?)?;
        let version: CairoPieVersion = parse_zip_file(zip.by_name("version.json")?)?;

        let addr_size: usize = 8;
        let felt_bytes = {
            let (mut n_bytes, remainder) = metadata.program.prime.bits().div_rem(&8u64);
            if remainder != 0 {
                n_bytes += 1;
            }
            n_bytes as usize
        };
        let memory = read_memory_file(zip.by_name("memory.bin")?, addr_size, felt_bytes)?;

        Ok(CairoPie {
            metadata,
            memory,
            execution_resources,
            additional_data,
            version,
        })
    }

    #[cfg(feature = "std")]
    pub fn from_file(path: &Path) -> Result<CairoPie, CairoPieError> {
        let file = std::fs::File::open(path)?;
        let zip = zip::ZipArchive::new(file)?;

        CairoPie::from_zip_archive(zip)
    }
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieMetadata {
    pub program: StrippedProgram,
    pub program_segment: SegmentInfo,
    pub execution_segment: SegmentInfo,
    pub ret_fp_segment: SegmentInfo,
    pub ret_pc_segment: SegmentInfo,
    pub builtin_segments: HashMap<String, SegmentInfo>,
    pub extra_segments: Vec<SegmentInfo>,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct StrippedProgram {
    #[serde(serialize_with = "serde_impl::serialize_program_data")]
    #[serde(deserialize_with = "serde_impl::deserialize_array_of_felts")]
    pub data: Vec<MaybeRelocatable>,
    pub builtins: Vec<BuiltinName>,
    pub main: usize,
    #[serde(deserialize_with = "deserialize_biguint_from_number")]
    pub prime: BigUint,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieVersion {
    pub cairo_pie: String,
}

mod serde_impl {
    use num_bigint::BigUint;
    use num_traits::Num;
    use serde::de::SeqAccess;
    use serde::{de, ser::SerializeSeq, Deserializer, Serialize, Serializer};
    use serde_json::Number;
    use std::fmt;

    use crate::serde::deserialize_utils::felt_from_number;
    use felt::Felt252;

    use crate::types::relocatable::MaybeRelocatable;

    pub const ADDR_BYTE_LEN: usize = 8;
    pub const FIELD_BYTE_LEN: usize = 32;
    pub const ADDR_BASE: u64 = 0x8000000000000000; // 2 ** (8 * ADDR_BYTE_LEN - 1)
    pub const OFFSET_BASE: u64 = 0x800000000000; // 2 ** OFFSET_BIT_LEN
    pub const RELOCATE_BASE: &str =
        "8000000000000000000000000000000000000000000000000000000000000000"; // 2 ** (8 * FIELD_BYTE_LEN - 1)

    struct Felt252Wrapper<'a>(&'a Felt252);

    impl<'a> Serialize for Felt252Wrapper<'a> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            #[cfg(any(target_arch = "wasm32", no_std, not(feature = "std")))]
            use crate::alloc::string::ToString;

            // Note: This uses an API intended only for testing.
            serde_json::Number::from_string_unchecked(self.0.to_string()).serialize(serializer)
        }
    }

    pub fn serialize_program_data<S>(
        values: &[MaybeRelocatable],
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq_serializer = serializer.serialize_seq(Some(values.len()))?;

        for value in values {
            match value {
                MaybeRelocatable::RelocatableValue(_) => todo!(),
                MaybeRelocatable::Int(x) => {
                    seq_serializer.serialize_element(&Felt252Wrapper(x))?;
                }
            };
        }

        seq_serializer.end()
    }

    pub fn serialize_memory<S>(
        values: &[((usize, usize), MaybeRelocatable)],
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[cfg(any(target_arch = "wasm32", no_std, not(feature = "std")))]
        use alloc::string::String;
        #[cfg(any(target_arch = "wasm32", no_std, not(feature = "std")))]
        use alloc::vec::Vec;

        // Missing segment and memory holes can be ignored
        // as they can be inferred by the address on the prover side
        let mem_cap = values.len() * ADDR_BYTE_LEN + values.len() * FIELD_BYTE_LEN;
        let mut res = Vec::with_capacity(mem_cap);

        for ((segment, offset), value) in values.iter() {
            match value {
                // Serializes RelocatableValue(little endian):
                // 1bit |   SEGMENT_BITS |   OFFSET_BITS
                // 1    |     segment    |   offset
                MaybeRelocatable::RelocatableValue(rel_val) => {
                    let mem_addr = ADDR_BASE + *segment as u64 * OFFSET_BASE + *offset as u64;

                    let reloc_base = BigUint::from_str_radix(RELOCATE_BASE, 16)
                        .map_err(|_| serde::ser::Error::custom("invalid relocation base str"))?;
                    let reloc_value = reloc_base
                        + BigUint::from(rel_val.segment_index as usize)
                            * BigUint::from(OFFSET_BASE)
                        + BigUint::from(rel_val.offset);
                    res.extend_from_slice(mem_addr.to_le_bytes().as_ref());
                    res.extend_from_slice(reloc_value.to_bytes_le().as_ref());
                }
                // Serializes Int(little endian):
                // 1bit | Num
                // 0    | num
                MaybeRelocatable::Int(data_val) => {
                    let mem_addr = ADDR_BASE + *segment as u64 * OFFSET_BASE + *offset as u64;
                    res.extend_from_slice(mem_addr.to_le_bytes().as_ref());
                    res.extend_from_slice(data_val.to_le_bytes().as_ref());
                }
            };
        }

        serializer.serialize_str(
            res.iter()
                .map(|b| format!("{:02x}", b))
                .collect::<String>()
                .as_str(),
        )
    }

    pub(crate) struct MaybeRelocatableNumberVisitor;

    impl<'de> de::Visitor<'de> for MaybeRelocatableNumberVisitor {
        type Value = Vec<MaybeRelocatable>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("Could not deserialize array of hexadecimal")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut data: Vec<MaybeRelocatable> = vec![];

            while let Some(n) = seq.next_element::<Number>()? {
                match Felt252::parse_bytes(n.to_string().as_bytes(), 10) {
                    None => {}
                    Some(_) => {}
                }
                let felt = felt_from_number(n.clone()).ok_or(de::Error::custom(format!(
                    "Failed to parse number as felt: {n}"
                )))?;
                data.push(MaybeRelocatable::Int(felt));
            }
            Ok(data)
        }
    }

    pub fn deserialize_array_of_felts<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<Vec<MaybeRelocatable>, D::Error> {
        d.deserialize_seq(MaybeRelocatableNumberVisitor)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rstest::rstest;
    use std::fs::File;

    #[test]
    fn serialize_cairo_pie_memory() {
        #[derive(Serialize)]
        struct MemoryWrapper(
            #[serde(serialize_with = "serde_impl::serialize_memory")] CairoPieMemory,
        );

        let addrs = [
            ((1, 0), "0000000000800080"),
            ((1, 1), "0100000000800080"),
            ((1, 4), "0400000000800080"),
            ((1, 8), "0800000000800080"),
            ((2, 0), "0000000000000180"),
            ((5, 8), "0800000000800280"),
        ];

        let memory = MemoryWrapper(vec![
            (addrs[0].0, MaybeRelocatable::Int(1234.into())),
            (addrs[1].0, MaybeRelocatable::Int(11.into())),
            (addrs[2].0, MaybeRelocatable::Int(12.into())),
            (
                addrs[3].0,
                MaybeRelocatable::RelocatableValue((1, 2).into()),
            ),
            (
                addrs[4].0,
                MaybeRelocatable::RelocatableValue((3, 4).into()),
            ),
            (
                addrs[5].0,
                MaybeRelocatable::RelocatableValue((5, 6).into()),
            ),
        ]);

        let mem = serde_json::to_value(memory).unwrap();
        let mem_str = mem.as_str().unwrap();
        let shift_len = (serde_impl::ADDR_BYTE_LEN + serde_impl::FIELD_BYTE_LEN) * 2;
        let shift_field = serde_impl::FIELD_BYTE_LEN * 2;
        let shift_addr = serde_impl::ADDR_BYTE_LEN * 2;

        // Serializes Address 8 Byte(little endian):
        for (i, expected_addr) in addrs.into_iter().enumerate() {
            let shift = shift_len * i;
            assert_eq!(
                &mem_str[shift..shift + shift_addr],
                expected_addr.1,
                "addr mismatch({i}): {mem_str:?}",
            );
        }

        // Serializes Int(little endian):
        // 1bit | Num
        // 0    | num
        assert_eq!(
            &mem_str[shift_addr..shift_addr + shift_field],
            "d204000000000000000000000000000000000000000000000000000000000000",
            "value mismatch: {mem_str:?}",
        );
        // Serializes RelocatableValue(little endian):
        // 1bit |   SEGMENT_BITS |   OFFSET_BITS
        // 1    |     segment    |   offset
        let shift_first_relocatable = shift_len * 3 + shift_addr;
        assert_eq!(
            &mem_str[shift_first_relocatable..shift_first_relocatable + shift_field],
            "0200000000800000000000000000000000000000000000000000000000000080",
            "value mismatch: {mem_str:?}",
        );
    }

    #[rstest]
    #[case(0x8000_0000_0000_0000u64, 0, 0)]
    #[case(0x8010_0000_0000_1000u64, 32, 0x1000)]
    fn test_memory_deserialize_relocatable(
        #[case] value: u64,
        #[case] expected_segment: isize,
        #[case] expected_offset: usize,
    ) {
        let bytes: [u8; 8] = value.to_le_bytes();
        let maybe_relocatable = maybe_relocatable_from_le_bytes(&bytes);

        assert_eq!(
            maybe_relocatable,
            MaybeRelocatable::RelocatableValue(Relocatable {
                segment_index: expected_segment,
                offset: expected_offset
            })
        );
    }

    #[rstest]
    #[case([0, 0, 0, 0, 0, 0, 0], 0)]
    #[case([0, 1, 2, 3, 4, 5, 6], 0x6050403020100)]
    fn test_memory_deserialize_integer(#[case] bytes: [u8; 7], #[case] expected_value: u64) {
        let maybe_relocatable = maybe_relocatable_from_le_bytes(&bytes);

        assert_eq!(
            maybe_relocatable,
            MaybeRelocatable::Int(Felt252::from(expected_value))
        );
    }

    #[test]
    fn test_read_memory_file() {
        let path = Path::new("../cairo_programs/manually_compiled/fibonacci_cairo_pie/memory.bin");
        let file = File::open(path).unwrap();

        let memory = read_memory_file(file, 8, 32).expect("Could not read memory file");
        assert_eq!(memory.len(), 88);
    }

    #[test]
    fn test_cairo_pie_from_file() {
        let path =
            Path::new("../cairo_programs/manually_compiled/fibonacci_cairo_pie/fibonacci_pie.zip");

        let cairo_pie = CairoPie::from_file(path).expect("Could not read CairoPie zip file");
        assert_eq!(cairo_pie.metadata.program.prime, Felt252::prime());
        assert_eq!(
            cairo_pie.metadata.program.builtins,
            vec![BuiltinName::output]
        );
        assert_eq!(
            cairo_pie.metadata.program_segment,
            SegmentInfo::from((0, 25))
        );
        assert_eq!(
            cairo_pie.metadata.execution_segment,
            SegmentInfo::from((1, 61))
        );
        assert_eq!(cairo_pie.metadata.ret_fp_segment, SegmentInfo::from((3, 0)));
        assert_eq!(cairo_pie.metadata.ret_pc_segment, SegmentInfo::from((4, 0)));
        assert_eq!(
            cairo_pie.metadata.builtin_segments,
            HashMap::from([("output".to_string(), SegmentInfo::from((2, 2)))])
        );
        assert_eq!(cairo_pie.metadata.extra_segments, vec![]);

        assert_eq!(cairo_pie.execution_resources.n_steps, 72);
        assert_eq!(cairo_pie.execution_resources.n_memory_holes, 0);
        assert_eq!(
            cairo_pie.execution_resources.builtin_instance_counter,
            HashMap::from([("output_builtin".to_string(), 2)])
        );

        assert_eq!(cairo_pie.memory.len(), 88);
        // Check a few values
        assert_eq!(
            cairo_pie.memory[0],
            (
                (0usize, 0usize),
                MaybeRelocatable::Int(Felt252::from(290341444919459839u64))
            )
        );
        assert_eq!(
            cairo_pie.memory[cairo_pie.memory.len() - 1],
            (
                (1usize, 60usize),
                MaybeRelocatable::RelocatableValue(Relocatable::from((2, 2)))
            )
        );

        assert_eq!(
            cairo_pie.additional_data,
            HashMap::from([(
                "output_builtin".to_string(),
                BuiltinAdditionalData::Output(OutputBuiltinAdditionalData {
                    base: 0,
                    pages: Default::default(),
                    attributes: Default::default(),
                })
            )])
        );

        assert_eq!(cairo_pie.version.cairo_pie, CAIRO_PIE_VERSION);
    }
}
