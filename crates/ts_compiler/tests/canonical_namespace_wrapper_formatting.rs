use ts_ast::{NodeData, NodeRef};
use ts_compiler::{CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn identifier(program: &Program, path: &str, name: &str) -> NodeRef {
    let source = program.source_file(path).unwrap();
    source
        .parse
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == name)
                .then(|| source.node_ref(node).unwrap())
        })
        .max_by_key(|node| source.parse.arena.get(node.node).unwrap().range.start)
        .unwrap()
}

#[test]
fn nodenext_namespace_artifacts_keep_wrapped_and_bare_names_on_replay() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        ("/project/producer.cts", "export const value: number = 1;"),
        (
            "/project/consumer.mts",
            "import * as ns from './producer.cjs'; export type Copy = typeof ns; export const copied = ns;",
        ),
        (
            "/project/consumer.cts",
            "import * as bare from './producer.cjs'; export type Copy = typeof bare; export const copied = bare;",
        ),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &[
            "producer.cts".to_owned(),
            "consumer.mts".to_owned(),
            "consumer.cts".to_owned(),
        ],
        CompilerOptions {
            module: ModuleKind::NodeNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::NodeNext,
            lib: Some(vec!["es5".to_owned()]),
            skip_lib_check: true,
            no_emit: true,
            ..CompilerOptions::default()
        },
        |program, queries| {
            let cases = [
                ("/project/consumer.mts", "ns", "typeof ns"),
                ("/project/consumer.cts", "bare", "typeof bare"),
            ];
            let locations = cases.map(|(path, name, _)| identifier(program, path, name));
            let types = locations.map(|location| queries.get_type_at_location(location).unwrap());
            assert_ne!(types[0], types[1]);
            let cold = queries.cold_diagnostic_snapshot();
            let store = queries.semantic_store_id();
            for replay in [false, true] {
                if replay {
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                    assert_eq!(queries.semantic_store_id(), store);
                }
                for ((_, _, expected), (location, type_)) in
                    cases.iter().zip(locations.into_iter().zip(types))
                {
                    assert_eq!(queries.get_type_at_location(location).unwrap(), type_);
                    assert_eq!(
                        queries
                            .type_to_string_at_location_with_flags(
                                type_,
                                location,
                                CanonicalTypeFormatFlags::NO_TRUNCATION,
                            )
                            .unwrap(),
                        *expected,
                    );
                }
            }
        },
    )
    .unwrap();
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    result.expect("canonical checker ran");
}
