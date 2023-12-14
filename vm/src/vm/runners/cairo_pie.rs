use super::cairo_runner::ExecutionResources;
use crate::{
    felt::Felt252,
    serde::deserialize_program::BuiltinName,
    stdlib::{collections::HashMap, prelude::*},
    types::relocatable::{MaybeRelocatable, Relocatable},
};
use serde::{Deserialize, Serialize};

const CAIRO_PIE_VERSION: &str = "1.1";

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
    #[serde(skip_serializing)]
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
    pub data: Vec<MaybeRelocatable>,
    pub builtins: Vec<BuiltinName>,
    pub main: usize,

    // Dummy field for serialization only.
    #[serde(serialize_with = "serde_impl::serialize_prime")]
    pub prime: (),
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieVersion {
    // Dummy field for serialization only.
    #[serde(serialize_with = "serde_impl::serialize_version")]
    pub cairo_pie: (),
}

mod serde_impl {
    use super::CAIRO_PIE_VERSION;
    use crate::{types::relocatable::MaybeRelocatable, utils::CAIRO_PRIME};
    use felt::Felt252;
    use num_bigint::BigUint;
    use num_traits::Num;
    use serde::{ser::SerializeSeq, Serialize, Serializer};

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

    pub fn serialize_prime<S>(_value: &(), serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[cfg(any(target_arch = "wasm32", no_std, not(feature = "std")))]
        use crate::alloc::string::ToString;

        // Note: This uses an API intended only for testing.
        serde_json::Number::from_string_unchecked(CAIRO_PRIME.to_string()).serialize(serializer)
    }

    pub fn serialize_version<S>(_value: &(), serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(CAIRO_PIE_VERSION)
    }
}

#[cfg(test)]
mod test {
    use super::*;

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
}
