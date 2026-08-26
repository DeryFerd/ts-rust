use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ts_ast::{NodeData, NodeRef};
use ts_compiler::{CanonicalModuleResolutionLookup, CanonicalProgramCheckError, Program};
use ts_options::{ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem, OsFileSystem};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct ProjectDirectory(PathBuf);

impl ProjectDirectory {
    fn new(files: &[(&str, &str)]) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ts-rust-canonical-config-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        let directory = Self(path);
        for (name, source) in files {
            let path = directory.0.join(name);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, source).unwrap();
        }
        directory
    }
}

impl Drop for ProjectDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn identifier(program: &Program, file_name: &str, name: &str) -> NodeRef {
    let source = program.source_file(file_name).expect("program source");
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| match &record.data {
            NodeData::Identifier(identifier) if identifier.text == name => source.node_ref(node),
            _ => None,
        })
        .expect("source identifier")
}

fn inherited_project() -> ProjectDirectory {
    ProjectDirectory::new(&[
        (
            "config/base.json",
            r#"{
                "compilerOptions": {
                    "module": "esnext",
                    "moduleResolution": "bundler",
                    "lib": ["es5"],
                    "types": [],
                    "strict": true,
                    "skipLibCheck": true,
                    "noEmit": true,
                    "incremental": true,
                    "paths": {"@shared/*": ["../shared/*"]}
                },
                "include": ["../app/src/**/*.ts"],
                "exclude": ["../app/src/excluded/**"]
            }"#,
        ),
        (
            "app/tsconfig.json",
            r#"{"extends":"../config/base.json","files":["explicit.ts"]}"#,
        ),
        ("app/explicit.ts", "export const explicit: number = 1;"),
        (
            "app/src/main.ts",
            concat!(
                "import { value } from '@shared/value';\n",
                "import { text } from 'pkg';\n",
                "const copy: number = value;\n",
                "const packageCopy: string = text;\n",
                "const bad: boolean = value;\n",
            ),
        ),
        ("shared/value.d.ts", "export declare const value: number;"),
        (
            "app/node_modules/pkg/package.json",
            r#"{"name":"pkg","exports":{".":{"types":"./index.d.ts"}}}"#,
        ),
        (
            "app/node_modules/pkg/index.d.ts",
            "export declare const text: string;",
        ),
        ("app/src/excluded/unused.ts", "not valid TypeScript"),
        ("app/outside.ts", "not valid TypeScript"),
    ])
}

#[test]
fn canonical_config_preserves_inherited_inputs_and_declaration_module_graph() {
    let directory = inherited_project();
    let config = directory.0.join("app/tsconfig.json");
    let main = directory.0.join("app/src/main.ts");
    let shared = directory.0.join("shared/value.d.ts");
    let package = directory.0.join("app/node_modules/pkg/index.d.ts");
    let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
        &OsFileSystem::default(),
        &config.to_string_lossy(),
        |program, queries| {
            assert_eq!(program.config_file_path(), Some(config.to_str().unwrap()));
            assert!(queries.has_diagnostics());
            let source = program.source_file(&main.to_string_lossy()).unwrap();
            for (name, target) in [("@shared/value", &shared), ("pkg", &package)] {
                let specifier = source
                    .parse
                    .arena
                    .iter()
                    .find_map(|(node, record)| match &record.data {
                        NodeData::StringLiteral(literal) if literal.text == name => {
                            source.node_ref(node)
                        }
                        _ => None,
                    })
                    .unwrap();
                let CanonicalModuleResolutionLookup::Resolved(resolution) =
                    queries.module_resolution(specifier)
                else {
                    panic!("unresolved project import {name}");
                };
                assert_eq!(
                    program
                        .source_file_by_id(resolution.target_file())
                        .unwrap()
                        .file_name,
                    target.to_string_lossy()
                );
            }
            let copy = identifier(program, &main.to_string_lossy(), "copy");
            let declared = identifier(program, &shared.to_string_lossy(), "value");
            let copy_type = queries.get_type_at_location(copy).unwrap();
            assert_eq!(copy_type, queries.get_type_at_location(declared).unwrap());
            queries.type_to_string(copy_type).unwrap()
        },
    )
    .unwrap();

    assert_eq!(queried.as_deref(), Some("number"));
    assert!(program.options().strict);
    assert!(program.options().strict_null_checks);
    assert!(program.options().no_implicit_any);
    assert!(program.options().incremental);
    assert_eq!(program.options().module, ModuleKind::EsNext);
    assert_eq!(
        program.options().module_resolution,
        ModuleResolutionKind::Bundler
    );
    assert!(
        program
            .source_file(&directory.0.join("app/explicit.ts").to_string_lossy())
            .is_some()
    );
    assert_eq!(
        program
            .source_files()
            .iter()
            .filter(|source| !source.is_default_library)
            .count(),
        4
    );
    assert!(program.source_files().iter().any(|source| {
        source.is_default_library && source.file_name.ends_with("/lib.es5.d.ts")
    }));
    assert!(!program.source_files().iter().any(|source| {
        source.is_default_library && source.file_name.ends_with("/lib.dom.d.ts")
    }));
    let [diagnostic] = program.diagnostics() else {
        panic!("expected one assignment error: {:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.file_name.as_deref(), main.to_str());
    assert_eq!(diagnostic.code, Some(2322));
    assert_eq!(
        diagnostic.message,
        "Type 'number' is not assignable to type 'boolean'."
    );
}

#[test]
fn canonical_config_diagnostics_are_visible_to_queries() {
    let filesystem = MemoryFileSystem::new(true);
    let config = r#"{
        "extends": "./missing.json",
        "files": ["main.ts"],
        "compilerOptions": {
            "lib":["es5"],"noEmit":true,"emitDeclarationOnly":true,"unknownCompilerOption":true
        }
    }"#;
    filesystem
        .write_file("/project/tsconfig.json", config)
        .unwrap();
    filesystem
        .write_file("/project/main.ts", "const value: number = 1;")
        .unwrap();

    let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |program, queries| {
            assert!(queries.has_diagnostics());
            program.diagnostics().to_vec()
        },
    )
    .unwrap();

    assert_eq!(program.diagnostics(), queried.unwrap());
    let mut codes = program
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code.unwrap())
        .collect::<Vec<_>>();
    codes.sort_unstable();
    assert_eq!(codes, [5023, 5069, 6053]);
    let option = program
        .diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.code == Some(5069))
        .unwrap();
    assert_eq!(option.file_name.as_deref(), Some("/project/tsconfig.json"));
    let range = option.range.unwrap();
    assert_eq!(
        &config[range.start.get() as usize..range.end.get() as usize],
        "\"emitDeclarationOnly\""
    );
}

#[test]
fn canonical_config_without_a_loadable_config_does_not_query() {
    for (name, contents) in [("missing", None), ("invalid", Some("!"))] {
        let filesystem = MemoryFileSystem::new(true);
        if let Some(contents) = contents {
            filesystem
                .write_file("/project/tsconfig.json", contents)
                .unwrap();
        }
        let mut called = false;
        let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
            &filesystem,
            "/project/./tsconfig.json",
            |_, _| called = true,
        )
        .unwrap();

        assert!(!called, "{name}");
        assert_eq!(queried, None, "{name}");
        assert!(!program.diagnostics().is_empty(), "{name}");
        assert!(program.source_files().is_empty(), "{name}");
        assert_eq!(program.config_file_path(), Some("/project/tsconfig.json"));
    }
}

#[test]
fn canonical_config_no_check_retains_inputs_without_querying() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/tsconfig.json",
            r#"{"files":["main.ts"],"compilerOptions":{"noCheck":true,"noEmit":true}}"#,
        )
        .unwrap();
    filesystem
        .write_file("/project/main.ts", "const value: number = 'wrong';")
        .unwrap();
    let mut called = false;

    let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |_, _| called = true,
    )
    .unwrap();

    assert!(!called);
    assert_eq!(queried, None);
    assert!(program.options().no_check);
    assert!(program.source_file("/project/main.ts").is_some());
    assert!(program.diagnostics().is_empty());
}

#[test]
fn canonical_config_unsupported_source_returns_the_canonical_failure() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/tsconfig.json",
            r#"{
                "files":["settings.json"],
                "compilerOptions":{
                    "module":"esnext","moduleResolution":"bundler",
                    "resolveJsonModule":true,"lib":["es5"],"noEmit":true
                }
            }"#,
        )
        .unwrap();
    filesystem
        .write_file("/project/settings.json", r#"{"enabled":true}"#)
        .unwrap();
    let mut called = false;

    let error = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |_, _| called = true,
    )
    .unwrap_err();

    assert!(!called);
    assert!(error.is_unsupported_boundary());
    assert!(matches!(
        error,
        CanonicalProgramCheckError::UnsupportedSourceKind { file_name, .. }
            if file_name == "/project/settings.json"
    ));
}

#[test]
fn canonical_config_preserves_emit_options_without_writing_outputs() {
    let directory = ProjectDirectory::new(&[
        (
            "tsconfig.json",
            r#"{
                "files":["src/main.ts"],
                "compilerOptions":{
                    "lib":["es5"],"types":[],"declaration":true,"rootDir":"src","outDir":"out"
                }
            }"#,
        ),
        ("src/main.ts", "export const value: number = 1;"),
    ]);
    let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
        &OsFileSystem::default(),
        &directory.0.join("tsconfig.json").to_string_lossy(),
        |_, queries| queries.has_diagnostics(),
    )
    .unwrap();

    assert_eq!(queried, Some(false));
    assert!(program.diagnostics().is_empty());
    assert!(!program.options().no_emit);
    assert!(program.options().declaration);
    assert!(!directory.0.join("out").exists());
}

#[test]
fn canonical_config_rejects_project_references_before_queries() {
    for dependency_exists in [false, true] {
        for no_check in [false, true] {
            let filesystem = MemoryFileSystem::new(true);
            let config = serde_json::json!({
                "files": [],
                "references": [{"path": "./dependency"}],
                "compilerOptions": {"noCheck": no_check, "noEmit": true}
            });
            filesystem
                .write_file("/project/tsconfig.json", &config.to_string())
                .unwrap();
            if dependency_exists {
                filesystem
                    .write_file(
                        "/project/dependency/tsconfig.json",
                        r#"{"files":["index.ts"],"compilerOptions":{"composite":true}}"#,
                    )
                    .unwrap();
                filesystem
                    .write_file("/project/dependency/index.ts", "export const value = 1;")
                    .unwrap();
            }
            let mut called = false;
            let error = Program::try_from_config_with_canonical_checker_and_queries(
                &filesystem,
                "/project/tsconfig.json",
                |_, _| called = true,
            )
            .unwrap_err();

            assert!(!called);
            assert_eq!(
                error,
                CanonicalProgramCheckError::ProjectReferencesUnsupported {
                    config_path: "/project/tsconfig.json".to_owned()
                }
            );
            assert!(error.is_unsupported_boundary());
            assert_eq!(error.failure_class().code(), "M00.PROJECT_REFERENCES");
        }
    }
}

#[test]
fn canonical_config_empty_files_does_not_discover_unrelated_sources() {
    let filesystem = MemoryFileSystem::new(true);
    let config = r#"{
        "files": [ /* empty */ ],
        "compilerOptions": {"lib":["es5"],"types":[],"noEmit":true}
    }"#;
    filesystem
        .write_file("/project/tsconfig.json", config)
        .unwrap();
    filesystem
        .write_file("/project/unrelated.ts", "not valid TypeScript")
        .unwrap();

    let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |program, queries| {
            assert!(queries.has_diagnostics());
            program.diagnostics().to_vec()
        },
    )
    .unwrap();
    assert_eq!(program.diagnostics(), queried.unwrap());

    let legacy = Program::from_config(&filesystem, "/project/tsconfig.json");
    for program in [&program, &legacy] {
        assert!(program.source_file("/project/unrelated.ts").is_none());
        assert!(
            program
                .source_files()
                .iter()
                .all(|source| source.is_default_library)
        );
        let [diagnostic] = program.diagnostics() else {
            panic!("expected TS18002: {:?}", program.diagnostics());
        };
        assert_eq!(diagnostic.code, Some(18_002));
        assert_eq!(
            diagnostic.file_name.as_deref(),
            Some("/project/tsconfig.json")
        );
        assert_eq!(
            diagnostic.message,
            "The 'files' list in config file '/project/tsconfig.json' is empty."
        );
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &config[range.start.get() as usize..range.end.get() as usize],
            "[ /* empty */ ]"
        );
    }
}

#[test]
fn canonical_config_empty_files_keeps_explicit_include_patterns() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/tsconfig.json",
            r#"{
                "files":[],"include":["src/*.ts"],"references":[],"extends":null,
                "compilerOptions":{"lib":["es5"],"types":[],"noEmit":true}
            }"#,
        )
        .unwrap();
    filesystem
        .write_file("/project/src/main.ts", "const value: number = 1;")
        .unwrap();
    filesystem
        .write_file("/project/unrelated.ts", "not valid TypeScript")
        .unwrap();

    let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |_, queries| queries.has_diagnostics(),
    )
    .unwrap();

    assert_eq!(queried, Some(true));
    assert!(program.source_file("/project/src/main.ts").is_some());
    assert!(program.source_file("/project/unrelated.ts").is_none());
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(18_002)]
    );
}

#[test]
fn canonical_config_inherited_empty_files_preserves_presence() {
    for override_files in [false, true] {
        let filesystem = MemoryFileSystem::new(true);
        let base = serde_json::json!({
            "files": if override_files { vec!["main.ts"] } else { Vec::new() },
            "compilerOptions": {"lib": ["es5"], "types": [], "noEmit": true}
        });
        let mut config = serde_json::json!({"extends": "./base.json"});
        if override_files {
            config["files"] = serde_json::json!([]);
        }
        filesystem
            .write_file("/project/base.json", &base.to_string())
            .unwrap();
        filesystem
            .write_file("/project/tsconfig.json", &config.to_string())
            .unwrap();
        filesystem
            .write_file("/project/main.ts", "not valid TypeScript")
            .unwrap();

        let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
            &filesystem,
            "/project/tsconfig.json",
            |_, queries| queries.has_diagnostics(),
        )
        .unwrap();

        assert_eq!(queried, Some(false));
        assert!(program.diagnostics().is_empty());
        assert!(program.source_file("/project/main.ts").is_none());
        assert!(
            program
                .source_files()
                .iter()
                .all(|source| source.is_default_library)
        );
    }
}

#[test]
fn canonical_config_absent_or_null_files_keeps_default_discovery() {
    for mut config in [serde_json::json!({}), serde_json::json!({"files": null})] {
        let filesystem = MemoryFileSystem::new(true);
        config["compilerOptions"] =
            serde_json::json!({"lib": ["es5"], "types": [], "noEmit": true});
        filesystem
            .write_file("/project/tsconfig.json", &config.to_string())
            .unwrap();
        filesystem
            .write_file("/project/main.ts", "const value: number = 1;")
            .unwrap();

        let (program, queried) = Program::try_from_config_with_canonical_checker_and_queries(
            &filesystem,
            "/project/tsconfig.json",
            |_, queries| queries.has_diagnostics(),
        )
        .unwrap();

        assert_eq!(queried, Some(false));
        assert!(program.diagnostics().is_empty());
        assert!(program.source_file("/project/main.ts").is_some());
    }
}
