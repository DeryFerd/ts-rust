use ts_ast::{NodeData, NodeRef};
use ts_compiler::{CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn initializer(program: &Program, path: &str, name: &str) -> NodeRef {
    let source = program.source_file(path).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &source.parse.arena.get(variable.name)?.data
            else {
                return None;
            };
            (identifier.text == name)
                .then(|| source.node_ref(variable.initializer.unwrap()).unwrap())
        })
        .unwrap()
}

#[test]
fn namespace_wrapper_cross_source_display_keeps_wrapped_and_bare_views() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, source) in [
        ("/project/producer.cts", "export const value: number = 1;"),
        (
            "/project/origin.mts",
            "import * as ns from './producer.cjs'; export const copied = ns; export const defaultValue = ns.default;",
        ),
        (
            "/project/nested/context.cts",
            "import * as bare from '../producer.cjs'; export const copied = bare;",
        ),
    ] {
        filesystem.write_file(path, source).unwrap();
    }
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &[
            "producer.cts".to_owned(),
            "origin.mts".to_owned(),
            "nested/context.cts".to_owned(),
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
            let origin = initializer(program, "/project/origin.mts", "copied");
            let default = initializer(program, "/project/origin.mts", "defaultValue");
            let context = initializer(program, "/project/nested/context.cts", "copied");
            let wrapped = queries.get_type_at_location(origin).unwrap();
            let bare = queries.get_type_at_location(context).unwrap();
            assert_ne!(wrapped, bare);
            assert_eq!(queries.get_type_at_location(default).unwrap(), bare);
            let plain = queries.type_to_string(wrapped).unwrap();
            let store = queries.semantic_store_id();
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty());
            let mut displays = Vec::new();
            for replay in [false, true] {
                if replay {
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                }
                assert_eq!(queries.semantic_store_id(), store);
                assert_eq!(queries.get_type_at_location(origin).unwrap(), wrapped);
                assert_eq!(queries.get_type_at_location(context).unwrap(), bare);
                assert_eq!(queries.get_type_at_location(default).unwrap(), bare);
                assert_eq!(queries.type_to_string(wrapped).unwrap(), plain);
                for (type_, location, expected) in [
                    (wrapped, origin, "typeof ns"),
                    (bare, context, "typeof bare"),
                ] {
                    assert_eq!(
                        queries
                            .type_to_string_at_location_with_flags(
                                type_,
                                location,
                                CanonicalTypeFormatFlags::NO_TRUNCATION,
                            )
                            .unwrap(),
                        expected,
                    );
                }
                displays.push((
                    replay,
                    queries
                        .type_to_string_at_location_with_flags(
                            wrapped,
                            context,
                            CanonicalTypeFormatFlags::NO_TRUNCATION,
                        )
                        .unwrap(),
                ));
            }
            displays
        },
    )
    .unwrap();
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert_eq!(
        result.expect("canonical checker ran"),
        [false, true]
            .map(|replay| (replay, "typeof import(\"../producer.cjs\")".to_owned()))
            .to_vec(),
    );
}
