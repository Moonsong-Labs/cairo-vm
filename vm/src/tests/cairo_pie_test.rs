use crate::{
    cairo_run::{cairo_run, CairoRunConfig},
    hint_processor::builtin_hint_processor::builtin_hint_processor_definition::BuiltinHintProcessor,
    stdlib::{collections::HashMap, prelude::*},
    types::relocatable::Relocatable,
    vm::runners::{
        builtin_runner::{
            HASH_BUILTIN_NAME, OUTPUT_BUILTIN_NAME, RANGE_CHECK_BUILTIN_NAME,
            SIGNATURE_BUILTIN_NAME,
        },
        cairo_pie::{
            BuiltinAdditionalData, CairoPieMemory, OutputBuiltinAdditionalData, SegmentInfo,
        },
        cairo_runner::ExecutionResources,
    },
};
use felt::felt_str;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::{
    string::{String, ToString},
    vec::Vec,
};

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn pedersen_test() {
    // Run the program
    let program_content = include_bytes!("../../../cairo_programs/pedersen_test.json");
    let mut hint_processor = BuiltinHintProcessor::new_empty();
    let result = cairo_run(
        program_content,
        &CairoRunConfig {
            layout: "all_cairo",
            ..Default::default()
        },
        &mut hint_processor,
    );
    assert!(result.is_ok());
    let (runner, vm) = result.unwrap();
    // Obtain the pie
    let result = runner.get_cairo_pie(&vm);
    assert!(result.is_ok());
    let cairo_pie = result.unwrap();
    // Check pie values
    // CairoPieMedatada
    let pie_metadata = cairo_pie.metadata;
    // ret_pc_segment
    assert_eq!(pie_metadata.ret_pc_segment, SegmentInfo::from((6, 0)));
    // builtin_segments
    let expected_builtin_segments = HashMap::from([
        (String::from("output"), SegmentInfo::from((2, 1))),
        (String::from("pedersen"), SegmentInfo::from((3, 3))),
        (String::from("range_check"), SegmentInfo::from((4, 0))),
    ]);
    assert_eq!(pie_metadata.builtin_segments, expected_builtin_segments);
    // program_segment
    assert_eq!(pie_metadata.program_segment, SegmentInfo::from((0, 19)));
    // ret_fp_segment
    assert_eq!(pie_metadata.ret_fp_segment, SegmentInfo::from((5, 0)));
    //program
    assert_eq!(pie_metadata.program.main, 6);
    assert_eq!(pie_metadata.program.builtins, runner.program.builtins);
    assert_eq!(
        pie_metadata.program.data,
        runner.program.shared_program_data.data
    );
    // execution_segment
    assert_eq!(pie_metadata.execution_segment, SegmentInfo::from((1, 15)));
    // extra_segments
    assert!(pie_metadata.extra_segments.is_empty());

    // execution_resources
    let expected_execution_resources = ExecutionResources {
        n_steps: 14,
        n_memory_holes: 0,
        builtin_instance_counter: HashMap::from([
            (RANGE_CHECK_BUILTIN_NAME.to_string(), 0),
            (OUTPUT_BUILTIN_NAME.to_string(), 1),
            (HASH_BUILTIN_NAME.to_string(), 1),
        ]),
    };
    assert_eq!(cairo_pie.execution_resources, expected_execution_resources);
    // additional_data
    let expected_additional_data = HashMap::from([
        (
            OUTPUT_BUILTIN_NAME.to_string(),
            BuiltinAdditionalData::Output(OutputBuiltinAdditionalData {
                base: 2,
                pages: HashMap::new(),
                attributes: HashMap::new(),
            }),
        ),
        (
            HASH_BUILTIN_NAME.to_string(),
            BuiltinAdditionalData::Hash(vec![Relocatable::from((3, 2))]),
        ),
        (
            RANGE_CHECK_BUILTIN_NAME.to_string(),
            BuiltinAdditionalData::None,
        ),
    ]);
    assert_eq!(cairo_pie.additional_data, expected_additional_data);
    // memory
    assert_eq!(
        cairo_pie.memory,
        Into::<CairoPieMemory>::into(&vm.segments.memory)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn common_signature() {
    // Run the program
    let program_content = include_bytes!("../../../cairo_programs/common_signature.json");
    let mut hint_processor = BuiltinHintProcessor::new_empty();
    let result = cairo_run(
        program_content,
        &CairoRunConfig {
            layout: "all_cairo",
            ..Default::default()
        },
        &mut hint_processor,
    );
    assert!(result.is_ok());
    let (runner, vm) = result.unwrap();
    // Obtain the pie
    let result = runner.get_cairo_pie(&vm);
    assert!(result.is_ok());
    let cairo_pie = result.unwrap();
    // Check pie values
    // CairoPieMedatada
    let pie_metadata = cairo_pie.metadata;
    // ret_pc_segment
    assert_eq!(pie_metadata.ret_pc_segment, SegmentInfo::from((4, 0)));
    // builtin_segments
    let expected_builtin_segments =
        HashMap::from([(String::from("ecdsa"), SegmentInfo::from((2, 2)))]);
    assert_eq!(pie_metadata.builtin_segments, expected_builtin_segments);
    // program_segment
    assert_eq!(pie_metadata.program_segment, SegmentInfo::from((0, 21)));
    // ret_fp_segment
    assert_eq!(pie_metadata.ret_fp_segment, SegmentInfo::from((3, 0)));
    //program
    assert_eq!(pie_metadata.program.main, 9);
    assert_eq!(pie_metadata.program.builtins, runner.program.builtins);
    assert_eq!(
        pie_metadata.program.data,
        runner.program.shared_program_data.data
    );
    // execution_segment
    assert_eq!(pie_metadata.execution_segment, SegmentInfo::from((1, 11)));
    // extra_segments
    assert!(pie_metadata.extra_segments.is_empty());

    // execution_resources
    let expected_execution_resources = ExecutionResources {
        n_steps: 11,
        n_memory_holes: 0,
        builtin_instance_counter: HashMap::from([(SIGNATURE_BUILTIN_NAME.to_string(), 1)]),
    };
    assert_eq!(cairo_pie.execution_resources, expected_execution_resources);
    // additional_data
    let expected_additional_data = HashMap::from([(
        SIGNATURE_BUILTIN_NAME.to_string(),
        BuiltinAdditionalData::Signature(HashMap::from([(
            Relocatable::from((2, 0)),
            (
                felt_str!(
                    "3086480810278599376317923499561306189851900463386393948998357832163236918254"
                ),
                felt_str!(
                    "598673427589502599949712887611119751108407514580626464031881322743364689811"
                ),
            ),
        )])),
    )]);
    assert_eq!(cairo_pie.additional_data, expected_additional_data);
    // memory
    assert_eq!(
        cairo_pie.memory,
        Into::<CairoPieMemory>::into(&vm.segments.memory)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn relocate_segments() {
    // Run the program
    let program_content = include_bytes!("../../../cairo_programs/relocate_segments.json");
    let mut hint_processor = BuiltinHintProcessor::new_empty();
    let result = cairo_run(
        program_content,
        &CairoRunConfig {
            layout: "all_cairo",
            ..Default::default()
        },
        &mut hint_processor,
    );
    assert!(result.is_ok());
    let (runner, vm) = result.unwrap();
    // Obtain the pie
    let result = runner.get_cairo_pie(&vm);
    assert!(result.is_ok());
    let cairo_pie = result.unwrap();
    // Check pie values
    // CairoPieMedatada
    let pie_metadata = cairo_pie.metadata;
    // ret_pc_segment
    assert_eq!(pie_metadata.ret_pc_segment, SegmentInfo::from((3, 0)));
    // builtin_segments
    assert!(pie_metadata.builtin_segments.is_empty());
    // program_segment
    assert_eq!(pie_metadata.program_segment, SegmentInfo::from((0, 32)));
    // ret_fp_segment
    assert_eq!(pie_metadata.ret_fp_segment, SegmentInfo::from((2, 0)));
    //program
    assert_eq!(pie_metadata.program.main, 5);
    assert!(pie_metadata.program.builtins.is_empty());
    assert_eq!(
        pie_metadata.program.data,
        runner.program.shared_program_data.data
    );
    // execution_segment
    assert_eq!(pie_metadata.execution_segment, SegmentInfo::from((1, 16)));
    // extra_segments
    assert_eq!(pie_metadata.extra_segments, vec![SegmentInfo::from((4, 3))]);

    // execution_resources
    let expected_execution_resources = ExecutionResources {
        n_steps: 22,
        n_memory_holes: 0,
        builtin_instance_counter: HashMap::default(),
    };
    assert_eq!(cairo_pie.execution_resources, expected_execution_resources);
    // additional_data
    assert!(cairo_pie.additional_data.is_empty());
    // memory
    assert_eq!(
        cairo_pie.memory,
        Into::<CairoPieMemory>::into(&vm.segments.memory)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn serialize_cairo_pie() {
    // Run the program
    let program_content = include_bytes!("../../../cairo_programs/print.json");
    let mut hint_processor = BuiltinHintProcessor::new_empty();
    let result = cairo_run(
        program_content,
        &CairoRunConfig {
            layout: "small",
            ..Default::default()
        },
        &mut hint_processor,
    );
    assert!(result.is_ok());
    let (runner, vm) = result.unwrap();
    // Obtain the pie
    let result = runner.get_cairo_pie(&vm);
    assert!(result.is_ok());
    let cairo_pie = result.unwrap();

    assert_eq!(
        serde_json::to_value(cairo_pie).unwrap(),
        serde_json::from_str::<serde_json::Value>(include_str!("cairo_pie_test_output.json"))
            .unwrap(),
    );
}
