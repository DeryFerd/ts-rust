use ts_ast::NodeData;
use ts_compiler::{
    CanonicalModuleResolutionLookup, CanonicalModuleTargetOmission, CanonicalProgramCheckError,
    Program,
};
use ts_options::{CompilerOptions, ModuleDetectionKind, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        allow_js: true,
        check_js: true,
        skip_lib_check: true,
        lib: Some(vec!["es5".to_owned()]),
        types: Some(Vec::new()),
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn write_files(filesystem: &MemoryFileSystem, files: &[(&str, &str)]) {
    for (path, text) in files {
        filesystem.write_file(path, text).unwrap();
    }
}

#[test]
fn canonical_module_targets_prefer_ambient_node_types_over_an_elided_javascript_package() {
    let filesystem = MemoryFileSystem::new(true);
    write_files(
        &filesystem,
        &[
            (
                "/project/main.ts",
                "import 'shim'; export const value: number = 1;",
            ),
            (
                "/project/node_modules/shim/package.json",
                r#"{"name":"shim","main":"index.js"}"#,
            ),
            (
                "/project/node_modules/shim/index.js",
                "var shim = module.exports = function () {};",
            ),
            (
                "/project/node_modules/@types/node/package.json",
                r#"{"name":"@types/node","types":"index.d.ts"}"#,
            ),
            (
                "/project/node_modules/@types/node/index.d.ts",
                "/// <reference path='shim.d.ts' />\n",
            ),
            (
                "/project/node_modules/@types/node/shim.d.ts",
                "declare module 'shim' { export const value: number; }",
            ),
        ],
    );
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            types: Some(vec!["node".to_owned()]),
            ..options()
        },
        |program, queries| {
            assert!(
                program
                    .source_file("/project/node_modules/shim/index.js")
                    .is_none()
            );
            let source = program.source_file("/project/main.ts").unwrap();
            let specifier = source
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(&record.data, NodeData::StringLiteral(name) if name.text == "shim")
                        .then(|| source.node_ref(node).unwrap())
                })
                .unwrap();
            let CanonicalModuleResolutionLookup::Resolved(target) =
                queries.module_resolution(specifier)
            else {
                panic!("the ambient declaration must supply the target");
            };
            let ambient = program
                .source_file("/project/node_modules/@types/node/shim.d.ts")
                .unwrap();
            assert_eq!(target.target_file(), ambient.id);
            assert!(target.is_ambient_module());
            let declarations = queries
                .get_symbol_declarations(target.target_symbol())
                .unwrap();
            assert_eq!(declarations.len(), 1);
            assert_eq!(declarations[0].file, ambient.id);
            assert!(matches!(
                ambient.parse.arena.get(declarations[0].node).unwrap().data,
                NodeData::ModuleDeclaration(_)
            ));
            assert_eq!(
                queries.get_symbol_at_location(specifier).unwrap(),
                Some(target.target_symbol())
            );
            let graph = program.project_graph_snapshot();
            let raw = graph
                .resolutions
                .iter()
                .find(|entry| entry.request.specifier == "shim")
                .unwrap();
            assert_eq!(
                raw.result.resolved.as_ref().unwrap().resolved_file_name,
                "/project/node_modules/shim/index.js"
            );
            assert!(raw.target.is_none());
            assert!(queries.replay_sources().unwrap().is_empty());
            assert_eq!(
                queries.module_resolution(specifier),
                CanonicalModuleResolutionLookup::Resolved(target)
            );
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
fn canonical_module_targets_prefer_exact_ambient_declarations_without_dropping_typescript_files() {
    let filesystem = MemoryFileSystem::new(true);
    write_files(
        &filesystem,
        &[
            ("/project/main.ts", "import 'shared'; export {};"),
            (
                "/project/ambient.d.ts",
                "module 'shared' { export const ambient: string; }",
            ),
            (
                "/project/node_modules/shared/package.json",
                r#"{"types":"index.d.ts"}"#,
            ),
            (
                "/project/node_modules/shared/index.d.ts",
                "export declare const physical: number;",
            ),
        ],
    );
    let (program, result) =
        Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["main.ts".to_owned(), "ambient.d.ts".to_owned()],
            options(),
            |program, queries| {
                let source = program.source_file("/project/main.ts").unwrap();
                let specifier = source.parse.arena.iter().find_map(|(node, record)| {
                matches!(&record.data, NodeData::StringLiteral(name) if name.text == "shared")
                    .then(|| source.node_ref(node).unwrap())
            }).unwrap();
                let CanonicalModuleResolutionLookup::Resolved(target) =
                    queries.module_resolution(specifier)
                else {
                    panic!("the global ambient module must win");
                };
                assert_eq!(
                    target.target_file(),
                    program.source_file("/project/ambient.d.ts").unwrap().id
                );
                assert!(target.is_ambient_module());
                let physical = program
                    .source_file("/project/node_modules/shared/index.d.ts")
                    .unwrap();
                let physical_symbol = queries
                    .get_symbol_at_location(physical.node_ref(physical.parse.source_file).unwrap())
                    .unwrap()
                    .unwrap();
                assert_ne!(physical_symbol, target.target_symbol());
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
fn canonical_module_targets_find_ambient_declarations_loaded_after_an_unresolved_import() {
    let filesystem = MemoryFileSystem::new(true);
    write_files(
        &filesystem,
        &[
            ("/project/main.ts", "import 'later'; export {};"),
            (
                "/project/references.ts",
                "/// <reference path='ambient.d.ts' />\nexport {};",
            ),
            (
                "/project/ambient.d.ts",
                "declare module 'later' { export const value: number; }",
            ),
        ],
    );
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem, "/project", &["main.ts".to_owned(), "references.ts".to_owned()], options(),
        |program, queries| {
            let source = program.source_file("/project/main.ts").unwrap();
            let specifier = source.parse.arena.iter().find_map(|(node, record)| {
                matches!(&record.data, NodeData::StringLiteral(name) if name.text == "later")
                    .then(|| source.node_ref(node).unwrap())
            }).unwrap();
            assert!(matches!(queries.module_resolution(specifier), CanonicalModuleResolutionLookup::Resolved(target) if target.is_ambient_module()));
        },
    ).unwrap();
    assert_eq!(result, Some(()));
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn module_targets_do_not_treat_forced_module_augmentations_as_global_ambient_modules() {
    let filesystem = MemoryFileSystem::new(true);
    write_files(
        &filesystem,
        &[
            ("/project/main.ts", "import 'shared';"),
            (
                "/project/forced.ts",
                "declare module 'shared' { export const replacement: string; }",
            ),
            (
                "/project/node_modules/shared/package.json",
                r#"{"types":"index.d.ts"}"#,
            ),
            (
                "/project/node_modules/shared/index.d.ts",
                "export declare const original: number;",
            ),
        ],
    );
    let program = Program::new_with_options(
        &filesystem,
        "/project",
        &["main.ts".to_owned(), "forced.ts".to_owned()],
        CompilerOptions {
            no_check: true,
            module_detection: ModuleDetectionKind::Force,
            ..options()
        },
    );
    let graph = program.project_graph_snapshot();
    let manifest = graph.module_resolution_manifest.unwrap();
    let target = program
        .source_file("/project/node_modules/shared/index.d.ts")
        .unwrap();
    assert!(matches!(
        manifest.entries()[0].resolution(),
        ts_checker::semantic::CanonicalModuleResolutionInput::Resolved(resolution)
            if resolution.target_file() == target.id
    ));
}

#[test]
fn canonical_module_targets_keep_intentional_omissions_explicit() {
    for (allow_js, check_js, no_resolve, reason) in [
        (
            true,
            false,
            false,
            CanonicalModuleTargetOmission::NodeModuleJavaScriptDepth { depth: 1, limit: 0 },
        ),
        (
            true,
            true,
            false,
            CanonicalModuleTargetOmission::NodeModuleJavaScriptDepth { depth: 1, limit: 0 },
        ),
        (
            false,
            false,
            false,
            CanonicalModuleTargetOmission::JavaScriptDisabled,
        ),
        (true, false, true, CanonicalModuleTargetOmission::NoResolve),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        write_files(
            &filesystem,
            &[
                ("/project/main.ts", "import 'untyped'; export {};"),
                (
                    "/project/node_modules/untyped/package.json",
                    r#"{"main":"index.js"}"#,
                ),
                (
                    "/project/node_modules/untyped/index.js",
                    "export const value = 1;",
                ),
            ],
        );
        let result = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                allow_js,
                allow_js_specified: true,
                check_js,
                no_resolve,
                ..options()
            },
        );
        let Err(error) = result else {
            panic!(
                "expected an omission with allow_js={allow_js}, check_js={check_js}, no_resolve={no_resolve}"
            );
        };
        assert!(error.failure_class().is_unsupported());
        assert_eq!(error.failure_class().code(), "M00.OMITTED_MODULE_TARGET");
        assert!(
            matches!(error, CanonicalProgramCheckError::OmittedModuleTargetUnsupported { reason: actual, target_file_name, .. }
            if actual == reason && target_file_name == "/project/node_modules/untyped/index.js")
        );
    }
}

#[test]
fn canonical_module_targets_keep_explicit_javascript_roots_at_depth_zero() {
    let filesystem = MemoryFileSystem::new(true);
    write_files(
        &filesystem,
        &[
            ("/project/main.ts", "import 'untyped'; export {};"),
            (
                "/project/node_modules/untyped/package.json",
                r#"{"main":"index.js"}"#,
            ),
            (
                "/project/node_modules/untyped/index.js",
                "export const value = 1;",
            ),
        ],
    );
    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &[
            "main.ts".to_owned(),
            "node_modules/untyped/index.js".to_owned(),
        ],
        options(),
    )
    .unwrap();
    assert!(
        program
            .source_file("/project/node_modules/untyped/index.js")
            .is_some()
    );
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn module_targets_apply_the_configured_external_javascript_depth() {
    for depth in [0, 1, 2] {
        let filesystem = MemoryFileSystem::new(true);
        write_files(
            &filesystem,
            &[
                ("/project/main.ts", "import 'first';"),
                (
                    "/project/node_modules/first/package.json",
                    r#"{"main":"index.js"}"#,
                ),
                (
                    "/project/node_modules/first/index.js",
                    "import 'second'; export {};",
                ),
                (
                    "/project/node_modules/second/package.json",
                    r#"{"main":"index.js"}"#,
                ),
                (
                    "/project/node_modules/second/index.js",
                    "export const value = 1;",
                ),
            ],
        );
        let program = Program::new_with_options(
            &filesystem,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_check: true,
                no_lib: true,
                max_node_module_js_depth: Some(depth),
                ..options()
            },
        );
        assert_eq!(
            program
                .source_file("/project/node_modules/first/index.js")
                .is_some(),
            depth >= 1
        );
        assert_eq!(
            program
                .source_file("/project/node_modules/second/index.js")
                .is_some(),
            depth >= 2
        );
    }
}

#[test]
fn module_targets_admit_descendants_after_a_shallower_route_without_resolving_them_again() {
    let filesystem = MemoryFileSystem::new(true);
    write_files(
        &filesystem,
        &[
            ("/project/main.ts", "import 'first'; import './bridge-one';"),
            (
                "/project/node_modules/first/package.json",
                r#"{"types":"index.ts"}"#,
            ),
            (
                "/project/node_modules/first/index.ts",
                "import 'middle'; export {};",
            ),
            ("/project/bridge-one.ts", "import './bridge-two';"),
            (
                "/project/bridge-two.ts",
                "import './node_modules/middle/index.js';",
            ),
            (
                "/project/node_modules/middle/package.json",
                r#"{"main":"index.js"}"#,
            ),
            (
                "/project/node_modules/middle/index.js",
                "import 'leaf'; export {};",
            ),
            (
                "/project/node_modules/leaf/package.json",
                r#"{"main":"index.js"}"#,
            ),
            (
                "/project/node_modules/leaf/index.js",
                "export const value = 1;",
            ),
        ],
    );
    let program = Program::new_with_options(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            no_check: true,
            no_lib: true,
            max_node_module_js_depth: Some(2),
            ..options()
        },
    );
    assert!(
        program
            .source_file("/project/node_modules/leaf/index.js")
            .is_some()
    );
    let graph = program.project_graph_snapshot();
    assert_eq!(
        graph
            .sources
            .iter()
            .filter(|source| source.file_name == "/project/node_modules/middle/index.js")
            .count(),
        1
    );
    assert_eq!(
        graph
            .resolutions
            .iter()
            .filter(|resolution| resolution.request.specifier == "leaf")
            .count(),
        1
    );
    assert!(graph.module_resolution_manifest.is_ok());
}
