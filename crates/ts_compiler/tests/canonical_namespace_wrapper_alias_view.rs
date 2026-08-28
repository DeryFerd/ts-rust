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
#[allow(clippy::too_many_lines)] // Alias display and replay checks share the same wrapped owner.
fn namespace_display_uses_a_renamed_import_of_the_same_wrapped_owner() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, source) in [
        ("/project/producer.cts", "export const value: number = 1;"),
        (
            "/project/origin.mts",
            "import * as ns from './producer.cjs'; export { ns }; export const copied = ns; export const defaultValue = ns.default;",
        ),
        (
            "/project/nested/renamed.mts",
            "import { ns as routed } from '../origin.mjs'; export const copied = routed;",
        ),
        (
            "/project/nested/renamed-with-direct.mts",
            "import * as other from '../producer.cjs'; import { ns as routed } from '../origin.mjs'; export const copied = routed; export const otherCopy = other;",
        ),
    ] {
        filesystem.write_file(path, source).unwrap();
    }
    let roots = [
        "producer.cts",
        "origin.mts",
        "nested/renamed.mts",
        "nested/renamed-with-direct.mts",
    ]
    .map(str::to_owned);
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &roots,
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
            let contexts = [
                "/project/nested/renamed.mts",
                "/project/nested/renamed-with-direct.mts",
            ]
            .map(|path| initializer(program, path, "copied"));
            let other = initializer(
                program,
                "/project/nested/renamed-with-direct.mts",
                "otherCopy",
            );
            let wrapped = queries.get_type_at_location(origin).unwrap();
            let bare = queries.get_type_at_location(default).unwrap();
            let distinct = queries.get_type_at_location(other).unwrap();
            assert_ne!(wrapped, bare);
            assert_ne!(wrapped, distinct);
            for context in contexts {
                assert_eq!(queries.get_type_at_location(context).unwrap(), wrapped);
            }
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
                assert_eq!(queries.get_type_at_location(default).unwrap(), bare);
                assert_eq!(queries.get_type_at_location(other).unwrap(), distinct);
                assert_eq!(
                    queries
                        .type_to_string_at_location_with_flags(
                            distinct,
                            other,
                            CanonicalTypeFormatFlags::NO_TRUNCATION,
                        )
                        .unwrap(),
                    "typeof other",
                );
                for context in contexts {
                    assert_eq!(queries.get_type_at_location(context).unwrap(), wrapped);
                    displays.push(
                        queries
                            .type_to_string_at_location_with_flags(
                                wrapped,
                                context,
                                CanonicalTypeFormatFlags::NO_TRUNCATION,
                            )
                            .map_err(|error| error.to_string()),
                    );
                }
            }
            displays
        },
    )
    .unwrap();
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics(),
    );
    assert_eq!(
        result.expect("canonical checker ran"),
        vec![Ok("typeof routed".to_owned()); 4],
    );
}
