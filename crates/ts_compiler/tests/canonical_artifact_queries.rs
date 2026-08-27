use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_checker::semantic::{SymbolDisplayError, TypeDisplayUnavailable};
use ts_compiler::{CanonicalArtifactQueryError, CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn canonical_options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        ..CompilerOptions::default()
    }
}

fn identifiers(program: &Program, file_name: &str, name: &str) -> Vec<NodeRef> {
    let source = program.source_file(file_name).expect("program source");
    let mut result = source
        .parse
        .arena
        .iter()
        .filter_map(|(node, record)| match &record.data {
            NodeData::Identifier(identifier) if identifier.text == name => source.node_ref(node),
            _ => None,
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|node| source.parse.arena.get(node.node).unwrap().range.start);
    result
}

fn transitive_package_type(filesystem: &MemoryFileSystem, target: &str, package: &str) -> String {
    filesystem
        .write_file(
            "/project/re-export.d.ts",
            &format!("export type {{ Item }} from '{package}';"),
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/input.d.ts",
            "import {} from './re-export'; export {};",
        )
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        filesystem,
        "/project",
        &["input.d.ts".to_owned()],
        CompilerOptions {
            skip_lib_check: true,
            ..canonical_options()
        },
        |program, queries| {
            let declaration = identifiers(program, target, "Item")[0];
            let source = program.source_file("/project/input.d.ts").unwrap();
            let location = source.node_ref(source.parse.source_file).unwrap();
            let type_ = queries.get_type_at_location(declaration).unwrap();
            let cold = queries
                .type_to_string_at_location_with_flags(
                    type_,
                    location,
                    CanonicalTypeFormatFlags::NO_TRUNCATION,
                )
                .unwrap();
            assert_eq!(
                queries
                    .type_to_string_at_location_with_flags(
                        type_,
                        location,
                        CanonicalTypeFormatFlags::NO_TRUNCATION
                    )
                    .unwrap(),
                cold
            );
            cold
        },
    )
    .unwrap();
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    result.expect("canonical checker ran")
}

#[test]
fn canonical_program_exposes_original_type_and_symbol_queries() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.ts",
            "const value: string = 'ok';\nconst copy: string = value;\n",
        )
        .unwrap();

    let (program, artifacts) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        canonical_options(),
        |program, queries| {
            let locations = identifiers(program, "/project/input.ts", "value");
            let [declaration, reference] = locations.as_slice() else {
                panic!("expected the declaration and reference to value");
            };
            let store = queries.semantic_store_id();
            let declaration_type = queries.get_type_at_location(*declaration).unwrap();
            let reference_type = queries.get_type_at_location(*reference).unwrap();
            assert_eq!(declaration_type, reference_type);
            assert_eq!(queries.type_to_string(declaration_type).unwrap(), "string");
            assert_eq!(
                queries
                    .type_to_string_with_flags(
                        declaration_type,
                        CanonicalTypeFormatFlags::NO_TRUNCATION,
                    )
                    .unwrap(),
                "string"
            );
            let declaration_symbol = queries
                .get_symbol_at_location(*declaration)
                .unwrap()
                .expect("declaration symbol");
            let reference_symbol = queries
                .get_symbol_at_location(*reference)
                .unwrap()
                .expect("reference symbol");
            assert_eq!(declaration_symbol, reference_symbol);
            assert_eq!(
                queries.symbol_to_string(declaration_symbol).unwrap(),
                "value"
            );
            let declarations = queries
                .get_symbol_declarations(declaration_symbol)
                .unwrap()
                .to_vec();
            assert_eq!(declarations.len(), 1);
            assert_eq!(
                program.node(declarations[0]).unwrap().kind,
                SyntaxKind::VariableDeclaration
            );
            assert_eq!(queries.semantic_store_id(), store);
            (
                queries.type_to_string(reference_type).unwrap(),
                declarations,
            )
        },
    )
    .unwrap();

    let (type_name, declarations) = artifacts.expect("canonical checker ran");
    assert_eq!(type_name, "string");
    assert!(program.diagnostics().is_empty());
    assert!(program.node(declarations[0]).is_some());
}

#[test]
fn canonical_queries_display_shared_module_types_through_the_local_alias() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/model.d.ts",
            "export function foo(): number; export function bar(): string;",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/input.ts",
            "import { default as Local } from './model'; Local.bar();",
        )
        .unwrap();
    let options = CompilerOptions {
        allow_synthetic_default_imports: true,
        module: ModuleKind::CommonJs,
        module_resolution: ModuleResolutionKind::Node10,
        ..canonical_options()
    };
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        options,
        |program, queries| {
            let local = identifiers(program, "/project/input.ts", "Local");
            let default = identifiers(program, "/project/input.ts", "default")[0];
            let type_ = queries.get_type_at_location(default).unwrap();
            let cold = queries.cold_diagnostic_snapshot();
            let store = queries.semantic_store_id();
            for location in [default, local[0], local[1]] {
                for replay in [false, true] {
                    if replay {
                        assert_eq!(queries.replay_sources().unwrap(), cold);
                        assert_eq!(queries.semantic_store_id(), store);
                    }
                    assert_eq!(queries.get_type_at_location(location).unwrap(), type_);
                    assert_eq!(
                        queries
                            .type_to_string_at_location_with_flags(
                                type_,
                                location,
                                CanonicalTypeFormatFlags::NO_TRUNCATION
                            )
                            .unwrap(),
                        "typeof Local"
                    );
                    let symbol = queries.get_symbol_at_location(location).unwrap().unwrap();
                    assert_eq!(
                        queries
                            .symbol_to_string_at_location(symbol, location)
                            .unwrap(),
                        "Local"
                    );
                }
            }
            let bar = identifiers(program, "/project/input.ts", "bar")[0];
            let symbol = queries.get_symbol_at_location(bar).unwrap().unwrap();
            assert_eq!(
                queries.symbol_to_string_at_location(symbol, bar).unwrap(),
                "Local.bar"
            );
            assert_eq!(queries.symbol_to_string(symbol).unwrap(), "bar");
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

#[test]
fn canonical_queries_name_an_anonymous_expando_owner_from_its_variable() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.ts",
            "const foo = () => {}; foo.bar = 42; export {};",
        )
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        canonical_options(),
        |program, queries| {
            let location = identifiers(program, "/project/input.ts", "bar")[0];
            let symbol = queries.get_symbol_at_location(location).unwrap().unwrap();
            assert_eq!(
                queries
                    .symbol_to_string_at_location(symbol, location)
                    .unwrap(),
                "foo.bar"
            );
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

#[test]
fn canonical_queries_use_package_exports_for_types_from_a_transitive_module() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, source) in [
        (
            "/packages/items/package.json",
            r#"{"name":"item-api","exports":{".":"./index.js"}}"#,
        ),
        (
            "/packages/items/index.d.ts",
            "export interface Item { value: number; }",
        ),
        ("/packages/items/index.js", "export {};"),
    ] {
        filesystem.write_file(path, source).unwrap();
    }
    filesystem.add_directory_link("/packages/items", "/project/node_modules/item-api");
    assert_eq!(
        transitive_package_type(&filesystem, "/packages/items/index.d.ts", "item-api"),
        "import(\"item-api\").Item"
    );
}

#[test]
fn package_json_file_links_do_not_move_the_export_base() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/metadata/item-api.json",
            r#"{"name":"item-api","exports":{".":"./index.js"}}"#,
        )
        .unwrap();
    filesystem
        .write_file(
            "/types/item-api.d.ts",
            "export interface Item { value: number; }",
        )
        .unwrap();
    filesystem.add_file_link(
        "/metadata/item-api.json",
        "/project/node_modules/item-api/package.json",
    );
    filesystem.add_file_link(
        "/types/item-api.d.ts",
        "/project/node_modules/item-api/index.d.ts",
    );
    assert_eq!(
        transitive_package_type(&filesystem, "/types/item-api.d.ts", "item-api"),
        "import(\"item-api\").Item"
    );
}

#[test]
fn package_display_uses_the_installed_alias_instead_of_manifest_name() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/node_modules/alias-package/package.json",
            r#"{"name":"real-package","exports":{".":"./index.js"}}"#,
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/node_modules/alias-package/index.d.ts",
            "export interface Item { value: number; }",
        )
        .unwrap();
    assert_eq!(
        transitive_package_type(
            &filesystem,
            "/project/node_modules/alias-package/index.d.ts",
            "alias-package"
        ),
        "import(\"alias-package\").Item"
    );
}

#[test]
fn package_display_keeps_the_first_matching_export_route() {
    for (package_json, expected) in [
        (
            r#"{"name":"item-api","exports":{".":"./index.js","./alternate":"./index.js"}}"#,
            "import(\"item-api\").Item",
        ),
        (
            r#"{"name":"item-api","exports":{"./alternate":"./index.js",".":"./index.js"}}"#,
            "import(\"item-api/alternate\").Item",
        ),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file("/project/node_modules/item-api/package.json", package_json)
            .unwrap();
        filesystem
            .write_file(
                "/project/node_modules/item-api/index.d.ts",
                "export interface Item { value: number; }",
            )
            .unwrap();
        assert_eq!(
            transitive_package_type(
                &filesystem,
                "/project/node_modules/item-api/index.d.ts",
                "item-api"
            ),
            expected
        );
    }
}

#[test]
fn package_display_selects_an_alias_that_resolves_from_each_containing_file() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/shared/package.json",
            r#"{"name":"real-package","exports":{".":"./index.js"}}"#,
        )
        .unwrap();
    filesystem
        .write_file(
            "/shared/index.d.ts",
            "export interface Item { value: number; }",
        )
        .unwrap();
    for (directory, alias) in [("/one", "alias-one"), ("/two", "alias-two")] {
        filesystem.add_directory_link("/shared", &format!("{directory}/node_modules/{alias}"));
        filesystem
            .write_file(
                &format!("{directory}/bridge.d.ts"),
                &format!("export type {{ Item }} from '{alias}';"),
            )
            .unwrap();
        filesystem
            .write_file(
                &format!("{directory}/use.d.ts"),
                "import {} from './bridge'; export {};",
            )
            .unwrap();
    }
    filesystem
        .write_file(
            "/outside/use.d.ts",
            "import {} from '../one/bridge'; export {};",
        )
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/",
        &[
            "/one/use.d.ts".to_owned(),
            "/two/use.d.ts".to_owned(),
            "/outside/use.d.ts".to_owned(),
        ],
        CompilerOptions {
            skip_lib_check: true,
            ..canonical_options()
        },
        |program, queries| {
            let declaration = identifiers(program, "/shared/index.d.ts", "Item")[0];
            let type_ = queries.get_type_at_location(declaration).unwrap();
            for (file, expected) in [
                ("/one/use.d.ts", "import(\"alias-one\").Item"),
                ("/two/use.d.ts", "import(\"alias-two\").Item"),
                ("/one/use.d.ts", "import(\"alias-one\").Item"),
                ("/two/use.d.ts", "import(\"alias-two\").Item"),
            ] {
                let source = program.source_file(file).unwrap();
                let location = source.node_ref(source.parse.source_file).unwrap();
                assert_eq!(
                    queries
                        .type_to_string_at_location_with_flags(
                            type_,
                            location,
                            CanonicalTypeFormatFlags::NO_TRUNCATION
                        )
                        .unwrap(),
                    expected
                );
            }
            let outside = program.source_file("/outside/use.d.ts").unwrap();
            let outside = outside.node_ref(outside.parse.source_file).unwrap();
            for _ in 0..2 {
                assert!(matches!(
                    queries.type_to_string_at_location_with_flags(
                        type_,
                        outside,
                        CanonicalTypeFormatFlags::NO_TRUNCATION
                    ),
                    Err(TypeDisplayUnavailable::SymbolDisplay(
                        SymbolDisplayError::MissingModuleSpecifier(_)
                    ))
                ));
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

#[test]
fn canonical_queries_preserve_cross_file_identity_and_reject_foreign_nodes() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/importer.ts",
            "import { value } from './target';\nexport const copy: string = value;\n",
        )
        .unwrap();
    filesystem
        .write_file("/project/target.ts", "export const value: string = 'ok';\n")
        .unwrap();
    let foreign = Program::new_with_options(
        &filesystem,
        "/project",
        &["target.ts".to_owned()],
        CompilerOptions {
            no_check: true,
            no_lib: true,
            ..CompilerOptions::default()
        },
    );
    let foreign_node = identifiers(&foreign, "/project/target.ts", "value")[0];

    let (_, artifacts) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["importer.ts".to_owned()],
        canonical_options(),
        |program, queries| {
            let imported = identifiers(program, "/project/importer.ts", "value");
            let target = identifiers(program, "/project/target.ts", "value")[0];
            let alias = queries
                .get_symbol_at_location(imported[0])
                .unwrap()
                .expect("import symbol");
            let target_symbol = queries
                .get_symbol_at_location(target)
                .unwrap()
                .expect("target symbol");
            assert_ne!(alias, target_symbol);
            assert_eq!(
                queries
                    .get_symbol_at_location(imported[1])
                    .unwrap()
                    .expect("import reference"),
                alias
            );
            let imported_type = queries.get_type_at_location(imported[1]).unwrap();
            assert_eq!(queries.type_to_string(imported_type).unwrap(), "string");
            assert!(matches!(
                queries.get_type_at_location(foreign_node),
                Err(CanonicalArtifactQueryError::ForeignNode(node)) if node == foreign_node
            ));
            queries
                .get_symbol_declarations(target_symbol)
                .unwrap()
                .to_vec()
        },
    )
    .unwrap();

    let declarations = artifacts.expect("canonical checker ran");
    assert_eq!(declarations.len(), 1);
}

fn merged_export_assignment_files() -> MemoryFileSystem {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/definition.ts",
            concat!(
                "export type Shape = { text: string };\n",
                "export namespace Names { export interface Entry { count: number } }\n",
                "export = { value: 1, label: 'ok' };\n",
            ),
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/use.ts",
            concat!(
                "import api = require('./definition');\n",
                "const n = api.value;\n",
                "const s = api.label;\n",
                "let first: api.Shape = { text: 'x' };\n",
                "let second: api.Names.Entry = { count: 2 };\n",
            ),
        )
        .unwrap();
    filesystem
}

#[test]
fn merged_export_assignment_symbols_keep_source_and_import_names() {
    let filesystem = merged_export_assignment_files();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["use.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::CommonJs,
            module_resolution: ModuleResolutionKind::Node10,
            ..canonical_options()
        },
        |program, queries| {
            let mut actual = Vec::new();
            let mut expected = Vec::new();
            for (file, name, display) in [
                ("/project/use.ts", "api", "api"),
                ("/project/use.ts", "value", "value"),
                ("/project/use.ts", "Shape", "api.Shape"),
                ("/project/use.ts", "Names", "api.Names"),
                ("/project/use.ts", "Entry", "api.Names.Entry"),
                ("/project/definition.ts", "Shape", "Shape"),
                ("/project/definition.ts", "Names", "Names"),
                ("/project/definition.ts", "Entry", "Entry"),
                ("/project/definition.ts", "value", "value"),
            ] {
                let location = identifiers(program, file, name)[0];
                let parent = program.node(location).unwrap().parent.unwrap();
                let parent = NodeRef::new(location.arena, location.file, parent);
                actual.push(queries.get_symbol_at_location(location).and_then(|symbol| {
                    symbol
                        .map(|symbol| queries.symbol_to_string_at_location(symbol, parent))
                        .transpose()
                }));
                expected.push(Ok(Some(display.to_owned())));
            }
            assert_eq!(actual, expected);
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

#[test]
#[allow(clippy::too_many_lines)] // Check value, declared-type, and qualifier identities across replay.
fn merged_export_assignment_type_queries_keep_value_and_namespace_roles() {
    let filesystem = merged_export_assignment_files();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["use.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::CommonJs,
            module_resolution: ModuleResolutionKind::Node10,
            ..canonical_options()
        },
        |program, queries| {
            let aliases = identifiers(program, "/project/use.ts", "api");
            assert_eq!(aliases.len(), 5);
            let mut actual = Vec::new();
            for location in &aliases {
                actual.push(
                    queries
                        .get_type_at_location(*location)
                        .map(|type_| queries.type_to_string(type_).unwrap()),
                );
            }
            let namespace = identifiers(program, "/project/use.ts", "Names")[0];
            actual.push(
                queries
                    .get_type_at_location(namespace)
                    .map(|type_| queries.type_to_string(type_).unwrap()),
            );
            assert_eq!(
                actual,
                [
                    "{ value: number; label: string; }",
                    "{ value: number; label: string; }",
                    "{ value: number; label: string; }",
                    "any",
                    "any",
                    "any",
                ]
                .map(|text| Ok(text.to_owned())),
            );
            let alias = queries.get_symbol_at_location(aliases[0]).unwrap().unwrap();
            for reference in &aliases[1..] {
                assert_eq!(
                    queries.get_symbol_at_location(*reference).unwrap(),
                    Some(alias)
                );
            }
            let value = queries.get_type_at_location(aliases[0]).unwrap();
            for reference in &aliases[1..3] {
                assert_eq!(queries.get_type_at_location(*reference).unwrap(), value);
            }
            let qualifier = queries.get_type_at_location(aliases[3]).unwrap();
            assert_ne!(value, qualifier);
            assert_eq!(queries.get_type_at_location(namespace).unwrap(), qualifier);
            let source = identifiers(program, "/project/definition.ts", "Shape")[0];
            let named = identifiers(program, "/project/use.ts", "first")[0];
            let declared = queries.get_type_at_location(source).unwrap();
            assert_eq!(queries.get_type_at_location(named).unwrap(), declared);
            assert_ne!(declared, value);
            assert_ne!(declared, qualifier);
            let diagnostics = queries.cold_diagnostic_snapshot();
            assert_eq!(queries.replay_sources().unwrap(), diagnostics);
            assert_eq!(queries.get_type_at_location(aliases[0]).unwrap(), value);
            assert_eq!(queries.get_type_at_location(aliases[3]).unwrap(), qualifier);
            assert_eq!(queries.get_type_at_location(named).unwrap(), declared);
            assert_eq!(
                queries.get_symbol_at_location(aliases[4]).unwrap(),
                Some(alias)
            );
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

#[test]
fn no_check_does_not_construct_or_query_a_canonical_graph() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/input.ts", "const value = 1;")
        .unwrap();
    let mut called = false;

    let (program, artifacts) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            no_check: true,
            no_lib: true,
            ..CompilerOptions::default()
        },
        |_, _| {
            called = true;
        },
    )
    .unwrap();

    assert!(!called);
    assert_eq!(artifacts, None);
    assert!(program.source_file("/project/input.ts").is_some());
}
