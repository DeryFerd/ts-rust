use serde_json::json;
use ts_compiler::{Program, ProgramGraphResolutionKind};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

const CONFIG: &str = "/project/tsconfig.json";
const NODE_DECLARATION: &str = "/project/node_modules/@types/node/index.d.ts";

fn project(types: Option<&[&str]>, source: &str) -> MemoryFileSystem {
    let filesystem = MemoryFileSystem::new(true);
    let mut options = json!({
        "module": "esnext",
        "moduleResolution": "bundler",
        "lib": ["es5"],
        "strict": true,
        "skipLibCheck": true,
        "noEmit": true
    });
    if let Some(types) = types {
        options["types"] = json!(types);
    }
    filesystem
        .write_file(
            CONFIG,
            &json!({"files": ["main.ts"], "compilerOptions": options}).to_string(),
        )
        .unwrap();
    for (path, text) in [
        ("/project/main.ts", source),
        (NODE_DECLARATION, "declare const NODE_GLOBAL: number;"),
        (
            "/project/node_modules/@types/jest/index.d.ts",
            "declare const JEST_GLOBAL: string;",
        ),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    filesystem
}

fn check(filesystem: &MemoryFileSystem) -> Program {
    let (program, checked) =
        Program::try_from_config_with_canonical_checker_and_queries(filesystem, CONFIG, |_, _| ())
            .unwrap();
    assert_eq!(checked, Some(()));
    program
}

#[test]
fn omitted_and_empty_types_do_not_load_installed_node_declarations() {
    for types in [None, Some([].as_slice())] {
        let filesystem = project(types, "const value: number = 1;");
        let program = check(&filesystem);
        assert_eq!(
            program.options().types,
            types.map(|names| names.iter().map(|name| (*name).to_owned()).collect())
        );
        assert!(program.source_file(NODE_DECLARATION).is_none());
        assert_eq!(
            program
                .source_files()
                .iter()
                .filter(|source| !source.is_default_library)
                .count(),
            1
        );
        assert!(
            program
                .project_graph_snapshot()
                .resolutions
                .iter()
                .all(|resolution| {
                    resolution.request.kind != ProgramGraphResolutionKind::AutomaticTypeDirective
                })
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn explicit_types_load_node_and_report_an_explicit_missing_package() {
    let filesystem = project(
        Some(&["node", "missing"]),
        "const value: number = NODE_GLOBAL;",
    );
    let program = check(&filesystem);
    assert!(program.source_file(NODE_DECLARATION).is_some());
    assert!(
        program
            .source_file("/project/node_modules/@types/jest/index.d.ts")
            .is_none()
    );
    let graph = program.project_graph_snapshot();
    let directives = graph
        .resolutions
        .iter()
        .filter(|resolution| {
            resolution.request.kind == ProgramGraphResolutionKind::AutomaticTypeDirective
        })
        .collect::<Vec<_>>();
    assert_eq!(
        directives
            .iter()
            .map(|resolution| resolution.request.specifier.as_str())
            .collect::<Vec<_>>(),
        ["node", "missing"]
    );
    assert_eq!(
        directives[0]
            .result
            .resolved
            .as_ref()
            .unwrap()
            .resolved_file_name,
        NODE_DECLARATION
    );
    assert!(directives[1].result.resolved.is_none());
    let [diagnostic] = program.diagnostics() else {
        panic!("expected TS2688: {:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2688));
    assert_eq!(diagnostic.file_name, None);
    assert_eq!(diagnostic.range, None);
    assert_eq!(
        diagnostic.message,
        "Cannot find type definition file for 'missing'."
    );
}

#[test]
fn wildcard_types_keep_explicit_order_and_filter_installed_packages() {
    let filesystem = project(
        Some(&["zeta", "*", "node", "*", "jest"]),
        "const value: number = NODE_GLOBAL; const outer: number = OUTER_GLOBAL;",
    );
    for (path, text) in [
        (
            "/project/node_modules/@types/zeta/index.d.ts",
            "declare const ZETA_GLOBAL: string;",
        ),
        (
            "/project/node_modules/@types/.hidden/index.d.ts",
            "declare const HIDDEN_GLOBAL: string;",
        ),
        (
            "/project/node_modules/@types/obsolete/package.json",
            r#"{"typings":null}"#,
        ),
        (
            "/project/node_modules/@types/obsolete/index.d.ts",
            "declare const OBSOLETE_GLOBAL: string;",
        ),
        (
            "/project/node_modules/@types/types-null/package.json",
            r#"{"types":null}"#,
        ),
        (
            "/project/node_modules/@types/types-null/index.d.ts",
            "declare const TYPES_NULL_GLOBAL: string;",
        ),
        (
            "/node_modules/@types/node/index.d.ts",
            "declare const OUTER_NODE_GLOBAL: string;",
        ),
        (
            "/node_modules/@types/outer/index.d.ts",
            "declare const OUTER_GLOBAL: number;",
        ),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    let program = check(&filesystem);
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    let graph = program.project_graph_snapshot();
    assert_eq!(
        graph
            .resolutions
            .iter()
            .filter(|resolution| {
                resolution.request.kind == ProgramGraphResolutionKind::AutomaticTypeDirective
            })
            .map(|resolution| resolution.request.specifier.as_str())
            .collect::<Vec<_>>(),
        ["zeta", "jest", "node", "types-null", "outer"]
    );
    assert!(program.source_file(NODE_DECLARATION).is_some());
    assert!(
        program
            .source_file("/project/node_modules/@types/types-null/index.d.ts")
            .is_some()
    );
    assert!(
        program
            .source_file("/node_modules/@types/outer/index.d.ts")
            .is_some()
    );
    for excluded in [
        "/project/node_modules/@types/.hidden/index.d.ts",
        "/project/node_modules/@types/obsolete/index.d.ts",
        "/node_modules/@types/node/index.d.ts",
    ] {
        assert!(program.source_file(excluded).is_none(), "loaded {excluded}");
    }
}

#[test]
fn omitted_types_do_not_disable_triple_slash_type_references() {
    let filesystem = project(
        None,
        concat!(
            "/// <reference types=\"node\"/>\n",
            "const value: number = NODE_GLOBAL;",
        ),
    );
    let program = check(&filesystem);
    assert!(program.source_file(NODE_DECLARATION).is_some());
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    let graph = program.project_graph_snapshot();
    assert!(graph.resolutions.iter().all(|resolution| {
        resolution.request.kind != ProgramGraphResolutionKind::AutomaticTypeDirective
    }));
    assert!(graph.resolutions.iter().any(|resolution| {
        resolution.request.kind == ProgramGraphResolutionKind::TypeReference
            && resolution.request.specifier == "node"
            && resolution
                .result
                .resolved
                .as_ref()
                .is_some_and(|target| target.resolved_file_name == NODE_DECLARATION)
    }));
}

#[test]
fn wildcard_types_report_packages_without_declarations() {
    let filesystem = project(Some(&["*"]), "const value: number = 1;");
    filesystem
        .write_file("/project/node_modules/@types/broken/package.json", "{}")
        .unwrap();
    let program = check(&filesystem);
    let [diagnostic] = program.diagnostics() else {
        panic!("expected TS2688: {:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2688));
    assert_eq!(diagnostic.file_name, None);
    assert_eq!(diagnostic.range, None);
    assert_eq!(
        diagnostic.message,
        "Cannot find type definition file for 'broken'."
    );
    assert!(program.source_file(NODE_DECLARATION).is_some());
    let graph = program.project_graph_snapshot();
    let broken = graph
        .resolutions
        .iter()
        .find(|resolution| {
            resolution.request.kind == ProgramGraphResolutionKind::AutomaticTypeDirective
                && resolution.request.specifier == "broken"
        })
        .unwrap();
    assert!(broken.result.resolved.is_none());
}

#[test]
fn explicit_type_roots_block_automatic_fallback_but_keep_source_references() {
    for roots in [Vec::new(), vec!["./custom-types"]] {
        for source_reference in [false, true] {
            let source = if source_reference {
                "/// <reference types=\"node\"/>\nconst value: number = NODE_GLOBAL;"
            } else {
                "const value: number = 1;"
            };
            let filesystem = project(None, source);
            let mut config: serde_json::Value =
                serde_json::from_str(&filesystem.read_file(CONFIG).unwrap()).unwrap();
            config["compilerOptions"]["typeRoots"] = json!(roots);
            if !source_reference {
                config["compilerOptions"]["types"] = json!(["node"]);
            }
            filesystem.write_file(CONFIG, &config.to_string()).unwrap();
            filesystem
                .write_file(
                    "/project/custom-types/local/index.d.ts",
                    "declare const LOCAL_GLOBAL: number;",
                )
                .unwrap();
            let program = check(&filesystem);
            assert_eq!(
                program.source_file(NODE_DECLARATION).is_some(),
                source_reference
            );
            let graph = program.project_graph_snapshot();
            let [reference] = graph.resolutions.as_slice() else {
                panic!("expected one type request: {:?}", graph.resolutions);
            };
            assert_eq!(reference.request.specifier, "node");
            assert_eq!(reference.result.resolved.is_some(), source_reference);
            if source_reference {
                assert_eq!(
                    reference.request.kind,
                    ProgramGraphResolutionKind::TypeReference
                );
                assert!(
                    program.diagnostics().is_empty(),
                    "{:?}",
                    program.diagnostics()
                );
            } else {
                assert_eq!(
                    reference.request.kind,
                    ProgramGraphResolutionKind::AutomaticTypeDirective
                );
                let [diagnostic] = program.diagnostics() else {
                    panic!("expected TS2688: {:?}", program.diagnostics());
                };
                assert_eq!(diagnostic.code, Some(2688));
                assert_eq!(
                    diagnostic.message,
                    "Cannot find type definition file for 'node'."
                );
            }
        }
    }
}

#[test]
fn automatic_types_use_the_config_directory_when_it_differs_from_cwd() {
    let filesystem = MemoryFileSystem::new(true);
    let config_path = "/repo/packages/app/tsconfig.json";
    for (path, source) in [
        (
            "/repo/packages/app/main.ts",
            "const local: number = APP_GLOBAL; const shared: number = SHARED_GLOBAL;",
        ),
        (
            "/repo/packages/app/node_modules/@types/app-only/index.d.ts",
            "declare const APP_GLOBAL: number;",
        ),
        (
            "/repo/packages/app/node_modules/@types/shared/index.d.ts",
            "declare const SHARED_GLOBAL: number;",
        ),
        (
            "/repo/node_modules/@types/shared/index.d.ts",
            "declare const SHARED_GLOBAL: string;",
        ),
    ] {
        filesystem.write_file(path, source).unwrap();
    }
    for types in [
        vec!["*".to_owned()],
        vec!["app-only".to_owned(), "shared".to_owned()],
    ] {
        filesystem
            .write_file(
                config_path,
                &json!({
                    "files": ["main.ts"],
                    "compilerOptions": {
                        "module": "esnext", "moduleResolution": "bundler", "lib": ["es5"],
                        "types": types, "strict": true, "skipLibCheck": true, "noEmit": true
                    }
                })
                .to_string(),
            )
            .unwrap();
        let (program, checked) =
            Program::try_new_with_canonical_checker_and_queries_with_config_path(
                &filesystem,
                "/repo",
                &["packages/app/main.ts".to_owned()],
                CompilerOptions {
                    module: ModuleKind::EsNext,
                    module_specified: true,
                    module_resolution: ModuleResolutionKind::Bundler,
                    lib: Some(vec!["es5".to_owned()]),
                    types: Some(types),
                    skip_lib_check: true,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
                Some(config_path),
                |_, _| (),
            )
            .unwrap();
        assert_eq!(checked, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert!(
            program
                .source_file("/repo/packages/app/node_modules/@types/app-only/index.d.ts")
                .is_some()
        );
        assert!(
            program
                .source_file("/repo/packages/app/node_modules/@types/shared/index.d.ts")
                .is_some()
        );
        assert!(
            program
                .source_file("/repo/node_modules/@types/shared/index.d.ts")
                .is_none()
        );
        let graph = program.project_graph_snapshot();
        assert_eq!(
            graph
                .resolutions
                .iter()
                .map(|resolution| {
                    assert_eq!(
                        resolution.request.kind,
                        ProgramGraphResolutionKind::AutomaticTypeDirective
                    );
                    assert_eq!(
                        resolution.request.containing_file,
                        "/repo/packages/app/__inferred type names__.ts"
                    );
                    resolution.request.specifier.as_str()
                })
                .collect::<Vec<_>>(),
            ["app-only", "shared"]
        );
    }
}
