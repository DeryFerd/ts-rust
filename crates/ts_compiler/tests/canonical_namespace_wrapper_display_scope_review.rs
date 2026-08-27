use ts_ast::NodeData;
use ts_compiler::{CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn namespace_wrapper_display_does_not_name_a_shadowing_local() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/producer.cts", "export const value: number = 1;")
        .unwrap();
    filesystem
        .write_file(
            "/project/consumer.mts",
            concat!(
                "import * as ns from './producer.cjs';\n",
                "export const copied = ns;\n",
                "function shadow(ns: number): number { copied; return ns; }\n",
            ),
        )
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["producer.cts".to_owned(), "consumer.mts".to_owned()],
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
            let source = program.source_file("/project/consumer.mts").unwrap();
            let latest_identifier = |name: &str| {
                source
                    .parse
                    .arena
                    .iter()
                    .filter_map(|(id, record)| {
                        matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == name)
                            .then(|| source.node_ref(id).unwrap())
                    })
                    .max_by_key(|node| source.parse.arena.get(node.node).unwrap().range.start)
                    .unwrap()
            };
            let copied = latest_identifier("copied");
            let local = latest_identifier("ns");
            let namespace = queries.get_type_at_location(copied).unwrap();
            let number = queries.get_type_at_location(local).unwrap();
            assert_eq!(queries.type_to_string(number).unwrap(), "number");
            assert_ne!(namespace, number);
            for replay in [false, true] {
                if replay {
                    assert!(queries.replay_sources().unwrap().is_empty());
                }
                assert_eq!(queries.get_type_at_location(copied).unwrap(), namespace);
                assert_eq!(
                    queries
                        .type_to_string_at_location_with_flags(
                            namespace,
                            copied,
                            CanonicalTypeFormatFlags::NO_TRUNCATION,
                        )
                        .unwrap(),
                    "typeof import(\"./producer.cjs\")",
                );
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
