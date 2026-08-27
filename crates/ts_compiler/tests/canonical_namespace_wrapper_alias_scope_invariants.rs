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
fn renamed_namespace_alias_obeys_value_scope_without_changing_owners() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, source) in [
        ("/project/producer.cts", "export const value: number = 1;"),
        (
            "/project/origin.mts",
            concat!(
                "import * as ns from './producer.cjs'; export { ns };\n",
                "export const copied = ns; export const defaultValue = ns.default;\n",
            ),
        ),
        (
            "/project/nested/consumer.mts",
            concat!(
                "import * as ns from '../producer.cjs';\n",
                "import { ns as routed } from '../origin.mjs';\n",
                "export const copied = routed; export const otherCopy = ns;\n",
                "export const otherDefault = ns.default;\n",
                "function hidden(routed: number): number { copied; return routed; }\n",
                "function typeOnly<routed>(value: routed): routed { copied; return value; }\n",
            ),
        ),
    ] {
        filesystem.write_file(path, source).unwrap();
    }
    let roots = ["producer.cts", "origin.mts", "nested/consumer.mts"].map(str::to_owned);
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
            let copied = initializer(program, "/project/nested/consumer.mts", "copied");
            let other = initializer(program, "/project/nested/consumer.mts", "otherCopy");
            let other_default =
                initializer(program, "/project/nested/consumer.mts", "otherDefault");
            let source = program.source_file("/project/nested/consumer.mts").unwrap();
            let [hidden, type_only] = ["hidden", "typeOnly"].map(|name| {
                source
                    .parse
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::FunctionDeclaration(function) = &record.data else {
                            return None;
                        };
                        let NodeData::Identifier(identifier) =
                            &source.parse.arena.get(function.name?)?.data
                        else {
                            return None;
                        };
                        (identifier.text == name)
                            .then(|| source.node_ref(function.body.unwrap()).unwrap())
                    })
                    .unwrap()
            });
            let reads = [origin, default, copied, other, other_default];
            let types = reads.map(|node| queries.get_type_at_location(node).unwrap());
            let [wrapped, bare, copied_type, distinct, other_bare] = types;
            assert_ne!(wrapped, bare);
            assert_ne!(wrapped, distinct);
            assert_ne!(distinct, bare);
            assert_eq!(copied_type, wrapped);
            assert_eq!(other_bare, bare);
            let plain = types.map(|type_| queries.type_to_string(type_).unwrap());
            let store = queries.semantic_store_id();
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty());
            for replay in [false, true] {
                if replay {
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                }
                for (extra, fallback) in [
                    (
                        CanonicalTypeFormatFlags::NONE,
                        "typeof import(\"../producer.cjs\")",
                    ),
                    (
                        CanonicalTypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE,
                        "typeof import('../producer.cjs')",
                    ),
                    (
                        CanonicalTypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
                        "typeof import(\"../producer.cjs\")",
                    ),
                    (
                        CanonicalTypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE
                            | CanonicalTypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE,
                        "typeof import('../producer.cjs')",
                    ),
                ] {
                    let flags = CanonicalTypeFormatFlags::NO_TRUNCATION | extra;
                    for (type_, location, expected) in [
                        (wrapped, origin, "typeof ns"),
                        (wrapped, copied, "typeof routed"),
                        (wrapped, type_only, "typeof routed"),
                        (wrapped, hidden, fallback),
                        (distinct, copied, "typeof ns"),
                        (distinct, hidden, "typeof ns"),
                    ] {
                        assert_eq!(
                            queries
                                .type_to_string_at_location_with_flags(type_, location, flags)
                                .unwrap(),
                            expected,
                            "replay={replay}, flags={flags:?}, location={location:?}",
                        );
                    }
                }
                assert_eq!(queries.semantic_store_id(), store);
                assert_eq!(
                    reads.map(|node| queries.get_type_at_location(node).unwrap()),
                    types
                );
                assert_eq!(
                    types.map(|type_| queries.type_to_string(type_).unwrap()),
                    plain
                );
                assert_eq!(queries.cold_diagnostic_snapshot(), cold);
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
