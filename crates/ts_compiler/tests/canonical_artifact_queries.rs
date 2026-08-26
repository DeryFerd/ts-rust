use ts_ast::{NodeData, NodeRef, SyntaxKind};
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
            let location = identifiers(program, "/project/input.ts", "Local")[1];
            let type_ = queries.get_type_at_location(location).unwrap();
            for _ in 0..2 {
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
        (
            "/project/re-export.d.ts",
            "export type { Item } from 'item-api';",
        ),
        (
            "/project/input.d.ts",
            "import {} from './re-export'; export {};",
        ),
    ] {
        filesystem.write_file(path, source).unwrap();
    }
    filesystem.add_directory_link("/packages/items", "/project/node_modules/item-api");
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.d.ts".to_owned()],
        CompilerOptions {
            skip_lib_check: true,
            ..canonical_options()
        },
        |program, queries| {
            let declaration = identifiers(program, "/packages/items/index.d.ts", "Item")[0];
            let source = program.source_file("/project/input.d.ts").unwrap();
            let location = source.node_ref(source.parse.source_file).unwrap();
            let type_ = queries.get_type_at_location(declaration).unwrap();
            for _ in 0..2 {
                assert_eq!(
                    queries
                        .type_to_string_at_location_with_flags(
                            type_,
                            location,
                            CanonicalTypeFormatFlags::NO_TRUNCATION
                        )
                        .unwrap(),
                    "import(\"item-api\").Item"
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
