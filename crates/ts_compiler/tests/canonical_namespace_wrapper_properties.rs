use ts_ast::{NodeData, NodeRef};
use ts_compiler::{CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn variable(program: &Program, file: &str, name: &str) -> (NodeRef, NodeRef) {
    let source = program.source_file(file).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &source.parse.arena.get(variable.name)?.data
            else {
                return None;
            };
            (identifier.text == name).then(|| {
                (
                    source.node_ref(node).unwrap(),
                    source.node_ref(variable.initializer.unwrap()).unwrap(),
                )
            })
        })
        .unwrap()
}

#[test]
fn nodenext_namespace_wrapper_properties_retain_public_types_and_symbols() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        ("/project/producer.cts", "export const value: number = 1;"),
        (
            "/project/consumer.mts",
            "import * as ns from './producer.cjs'; export const nested = ns.default.value; export const bare = ns.default; export const direct = ns.value;",
        ),
        (
            "/project/consumer.cts",
            "import * as ns from './producer.cjs'; export const copied = ns; export const direct = ns.value;",
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
            let producer = variable(program, "/project/producer.cts", "value").0;
            let value = queries.get_symbol_at_location(producer).unwrap().unwrap();
            let direct = variable(program, "/project/consumer.mts", "direct").1;
            let nested = variable(program, "/project/consumer.mts", "nested").1;
            let bare = variable(program, "/project/consumer.mts", "bare").1;
            let copied = variable(program, "/project/consumer.cts", "copied").1;
            let commonjs_direct = variable(program, "/project/consumer.cts", "direct").1;
            let number = queries.get_type_at_location(direct).unwrap();
            assert_eq!(queries.type_to_string(number).unwrap(), "number");
            for access in [direct, nested, commonjs_direct] {
                assert_eq!(queries.get_type_at_location(access), Ok(number));
                assert_eq!(queries.get_symbol_at_location(access), Ok(Some(value)));
            }
            assert_eq!(
                queries.get_type_at_location(bare).unwrap(),
                queries.get_type_at_location(copied).unwrap()
            );
            let default = queries.get_symbol_at_location(bare).unwrap().unwrap();
            assert_ne!(default, value);
            assert!(queries.get_symbol_declarations(default).unwrap().is_empty());
            let before = [direct, nested, bare, copied, commonjs_direct].map(|node| {
                let type_ = queries.get_type_at_location(node).unwrap();
                let expected = if node == bare {
                    "typeof import(\"./producer.cjs\")"
                } else if node == copied {
                    "typeof ns"
                } else {
                    "number"
                };
                let display = queries
                    .type_to_string_at_location_with_flags(
                        type_,
                        node,
                        CanonicalTypeFormatFlags::NO_TRUNCATION,
                    )
                    .unwrap();
                assert_eq!(display, expected);
                (
                    node,
                    type_,
                    queries.get_symbol_at_location(node).unwrap(),
                    display,
                )
            });
            assert!(queries.replay_sources().unwrap().is_empty());
            for (node, type_, symbol, display) in before {
                assert_eq!(queries.get_type_at_location(node), Ok(type_));
                assert_eq!(queries.get_symbol_at_location(node), Ok(symbol));
                assert_eq!(
                    queries
                        .type_to_string_at_location_with_flags(
                            type_,
                            node,
                            CanonicalTypeFormatFlags::NO_TRUNCATION,
                        )
                        .unwrap(),
                    display,
                );
            }
        },
    )
    .unwrap();
    assert_eq!(result, Some(()));
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}
