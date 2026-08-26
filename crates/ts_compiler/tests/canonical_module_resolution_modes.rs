use ts_ast::{NodeData, NodeRef};
use ts_checker::semantic::CanonicalModuleResolutionMode;
use ts_compiler::{CanonicalModuleResolutionLookup, CanonicalProgramQueries, Program};
use ts_options::{CompilerOptions, JsxEmit, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

const IMPORT_TARGET: &str = "/project/node_modules/pkg/index.d.mts";
const REQUIRE_TARGET: &str = "/project/node_modules/pkg/index.d.cts";

fn options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::NodeNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::NodeNext,
        lib: Some(vec!["es5".to_owned()]),
        skip_lib_check: true,
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn package_filesystem(exports: &str) -> MemoryFileSystem {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        ("/project/node_modules/pkg/package.json", exports),
        (
            IMPORT_TARGET,
            "export declare const value: number; export interface Value { value: number; }",
        ),
        (
            REQUIRE_TARGET,
            "export declare const value: string; export interface Value { value: string; }",
        ),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    filesystem
}

fn specifiers(program: &Program, file_name: &str) -> Vec<NodeRef> {
    let source = program.source_file(file_name).unwrap();
    let mut nodes = source
        .parse
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(&record.data, NodeData::StringLiteral(text) if text.text == "pkg")
                .then_some((record.range.start, source.node_ref(node).unwrap()))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn variable(program: &Program, file_name: &str, name: &str) -> NodeRef {
    let source = program.source_file(file_name).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(declaration) = &record.data else {
                return None;
            };
            matches!(
                &source.parse.arena.get(declaration.name)?.data,
                NodeData::Identifier(identifier) if identifier.text == name
            )
            .then(|| source.node_ref(node).unwrap())
        })
        .unwrap()
}

fn assert_target(
    program: &Program,
    queries: &CanonicalProgramQueries<'_>,
    specifier: NodeRef,
    file_name: &str,
    expected_mode: CanonicalModuleResolutionMode,
) {
    let CanonicalModuleResolutionLookup::Resolved(resolved) = queries.module_resolution(specifier)
    else {
        panic!("missing resolution for {specifier:?}");
    };
    let target = program.source_file(file_name).unwrap();
    assert_eq!(resolved.target_file(), target.id);
    assert_eq!(resolved.usage_mode(), expected_mode);
    assert_eq!(resolved.target_mode(), expected_mode);
    assert!(!resolved.is_ambient_module());
    assert_eq!(
        queries
            .get_symbol_declarations(resolved.target_symbol())
            .unwrap(),
        &[target.node_ref(target.parse.source_file).unwrap()]
    );
}

#[test]
fn canonical_module_modes_keep_distinct_import_and_require_targets_in_both_orders() {
    for require_first in [false, true] {
        let filesystem = package_filesystem(
            r#"{"name":"pkg","exports":{".":{"import":"./index.d.mts","require":"./index.d.cts"}}}"#,
        );
        let import = "import { value as imported } from 'pkg';\n";
        let require = "import required = require('pkg');\n";
        let imports = if require_first {
            format!("{require}{import}")
        } else {
            format!("{import}{require}")
        };
        filesystem
            .write_file(
                "/project/main.mts",
                &format!(
                    "{imports}const importedValue: number = imported;\nconst requiredValue: string = required.value;\n"
                ),
            )
            .unwrap();

        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["main.mts".to_owned()],
            options(),
            |program, queries| {
                let nodes = specifiers(program, "/project/main.mts");
                assert_eq!(nodes.len(), 2);
                let import = nodes[usize::from(require_first)];
                let require = nodes[usize::from(!require_first)];
                assert_target(
                    program,
                    queries,
                    import,
                    IMPORT_TARGET,
                    CanonicalModuleResolutionMode::Esm,
                );
                assert_target(
                    program,
                    queries,
                    require,
                    REQUIRE_TARGET,
                    CanonicalModuleResolutionMode::CommonJs,
                );
                let before = nodes
                    .iter()
                    .map(|node| queries.module_resolution(*node))
                    .collect::<Vec<_>>();
                for (name, expected) in [("importedValue", "number"), ("requiredValue", "string")] {
                    let type_ = queries
                        .get_type_at_location(variable(program, "/project/main.mts", name))
                        .unwrap();
                    assert_eq!(queries.type_to_string(type_).unwrap(), expected);
                }
                assert!(queries.replay_sources().unwrap().is_empty());
                assert_eq!(
                    nodes
                        .iter()
                        .map(|node| queries.module_resolution(*node))
                        .collect::<Vec<_>>(),
                    before
                );
            },
        )
        .unwrap_or_else(|error| panic!("require_first={require_first}: {error:?}"));
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn canonical_module_modes_use_each_type_import_attribute() {
    let filesystem = package_filesystem(
        r#"{"name":"pkg","exports":{".":{"import":"./index.d.mts","require":"./index.d.cts"}}}"#,
    );
    filesystem
        .write_file(
            "/project/main.cts",
            concat!(
                "import type { Value as Imported } from 'pkg' with { 'resolution-mode': 'import' };\n",
                "import type { Value as Required } from 'pkg' with { 'resolution-mode': 'require' };\n",
                "const importedValue: Imported = { value: 1 };\n",
                "const requiredValue: Required = { value: 'ready' };\n",
            ),
        )
        .unwrap();

    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.cts".to_owned()],
        options(),
        |program, queries| {
            let nodes = specifiers(program, "/project/main.cts");
            assert_eq!(nodes.len(), 2);
            assert_target(
                program,
                queries,
                nodes[0],
                IMPORT_TARGET,
                CanonicalModuleResolutionMode::Esm,
            );
            assert_target(
                program,
                queries,
                nodes[1],
                REQUIRE_TARGET,
                CanonicalModuleResolutionMode::CommonJs,
            );
            assert!(queries.replay_sources().unwrap().is_empty());
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

#[test]
fn canonical_module_modes_do_not_reuse_another_modes_success_for_a_missing_target() {
    for missing_import in [false, true] {
        let exports = if missing_import {
            r#"{"name":"pkg","exports":{".":{"import":"./missing.d.mts","require":"./index.d.cts"}}}"#
        } else {
            r#"{"name":"pkg","exports":{".":{"import":"./index.d.mts","require":"./missing.d.cts"}}}"#
        };
        let filesystem = package_filesystem(exports);
        filesystem
            .write_file(
                "/project/main.mts",
                "import { value } from 'pkg';\nimport required = require('pkg');\n",
            )
            .unwrap();

        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["main.mts".to_owned()],
            options(),
            |program, queries| {
                let nodes = specifiers(program, "/project/main.mts");
                assert_eq!(nodes.len(), 2);
                let missing = nodes[usize::from(!missing_import)];
                let resolved = nodes[usize::from(missing_import)];
                assert_eq!(
                    queries.module_resolution(missing),
                    CanonicalModuleResolutionLookup::Unresolved
                );
                let (target, mode) = if missing_import {
                    (REQUIRE_TARGET, CanonicalModuleResolutionMode::CommonJs)
                } else {
                    (IMPORT_TARGET, CanonicalModuleResolutionMode::Esm)
                };
                assert_target(program, queries, resolved, target, mode);
            },
        )
        .unwrap_or_else(|error| panic!("missing_import={missing_import}: {error:?}"));
        assert_eq!(result, Some(()));
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [Some(2307)]
        );
    }
}

#[test]
fn canonical_module_modes_keep_ambient_targets_in_both_modes() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/main.mts",
            concat!(
                "import { value } from 'pkg';\n",
                "import required = require('pkg');\n",
                "const importedValue: number = value;\n",
                "const requiredValue: number = required.value;\n",
            ),
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/ambient.d.ts",
            "declare module 'pkg' { export const value: number; }",
        )
        .unwrap();

    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.mts".to_owned(), "ambient.d.ts".to_owned()],
        options(),
        |program, queries| {
            let nodes = specifiers(program, "/project/main.mts");
            assert_eq!(nodes.len(), 2);
            let target = program.source_file("/project/ambient.d.ts").unwrap();
            let declaration = target
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::ModuleDeclaration(_))
                        .then(|| target.node_ref(node).unwrap())
                })
                .unwrap();
            let mut symbols = Vec::new();
            for (node, mode) in nodes.into_iter().zip([
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::CommonJs,
            ]) {
                let CanonicalModuleResolutionLookup::Resolved(resolved) =
                    queries.module_resolution(node)
                else {
                    panic!("missing ambient target for {mode:?}");
                };
                assert_eq!(resolved.target_file(), target.id);
                assert_eq!(resolved.usage_mode(), mode);
                assert!(resolved.is_ambient_module());
                assert_eq!(
                    queries
                        .get_symbol_declarations(resolved.target_symbol())
                        .unwrap(),
                    &[declaration]
                );
                symbols.push(resolved.target_symbol());
            }
            assert_eq!(symbols[0], symbols[1]);
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

#[test]
fn canonical_module_modes_keep_the_jsx_runtime_separate_from_an_explicit_require() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        (
            "/project/main.tsx",
            concat!(
                "import required = require('pkg/jsx-runtime');\n",
                "const marker: number = required.marker;\n",
                "const view = <div title='ready' />;\n",
            ),
        ),
        (
            "/project/node_modules/pkg/package.json",
            r#"{"name":"pkg","exports":{"./jsx-runtime":{"import":"./jsx.d.mts","require":"./jsx.d.cts"}}}"#,
        ),
        (
            "/project/node_modules/pkg/jsx.d.mts",
            concat!(
                "export namespace JSX {\n",
                "  interface Element {}\n",
                "  interface IntrinsicElements { div: { title: string }; }\n",
                "}\n",
            ),
        ),
        (
            "/project/node_modules/pkg/jsx.d.cts",
            concat!(
                "export declare const marker: number;\n",
                "export namespace JSX {\n",
                "  interface Element {}\n",
                "  interface IntrinsicElements { span: {}; }\n",
                "}\n",
            ),
        ),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.tsx".to_owned()],
        CompilerOptions {
            jsx: JsxEmit::ReactJsx,
            jsx_import_source: Some("pkg".to_owned()),
            ..options()
        },
        |program, queries| {
            let source = program.source_file("/project/main.tsx").unwrap();
            let require = source
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(&record.data, NodeData::StringLiteral(text) if text.text == "pkg/jsx-runtime")
                        .then(|| source.node_ref(node).unwrap())
                })
                .unwrap();
            assert_target(
                program,
                queries,
                require,
                "/project/node_modules/pkg/jsx.d.cts",
                CanonicalModuleResolutionMode::CommonJs,
            );
            let view = variable(program, "/project/main.tsx", "view");
            let type_ = queries.get_type_at_location(view).unwrap();
            assert!(queries.replay_sources().unwrap().is_empty());
            assert_eq!(queries.get_type_at_location(view).unwrap(), type_);
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
