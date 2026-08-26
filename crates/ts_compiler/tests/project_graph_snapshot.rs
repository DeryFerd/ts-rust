use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ts_ast::FileId;
use ts_checker::semantic::{CanonicalModuleResolutionInput, CanonicalModuleResolutionMode};
use ts_compiler::{
    CanonicalProgramCheckError, Program, ProgramGraphMissingEvidence, ProgramGraphReferenceKind,
    ProgramGraphResolutionKind,
};
use ts_module::{ModuleFormat, ResolutionMode};
use ts_options::{CompilerOptions, JsxEmit, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem, OsFileSystem};

fn graph_options() -> CompilerOptions {
    CompilerOptions {
        no_check: true,
        no_emit: true,
        no_lib: true,
        module: ModuleKind::EsNext,
        module_resolution: ModuleResolutionKind::Bundler,
        ..CompilerOptions::default()
    }
}

fn write_files(file_system: &dyn FileSystem, files: &[(&str, &str)]) {
    for (path, text) in files {
        file_system.write_file(path, text).unwrap();
    }
}

#[test]
fn graph_snapshot_retains_exact_roots_with_nonmonotonic_ids_and_owned_text() {
    let file_system = MemoryFileSystem::new(true);
    write_files(
        &file_system,
        &[
            ("/project/z.ts", "export const z = 1;"),
            ("/project/a.ts", "export const a = 2;"),
        ],
    );
    let roots = ["./z.ts", "a.ts", "./z.ts", "missing.ts"].map(str::to_owned);
    let program = Program::new_with_options(&file_system, "/project", &roots, graph_options());
    assert_eq!(program.ordered_root_file_names(), roots);

    let graph = program.project_graph_snapshot();
    assert_eq!(
        graph
            .roots
            .iter()
            .map(|root| root.requested_name.as_str())
            .collect::<Vec<_>>(),
        ["./z.ts", "a.ts", "./z.ts", "missing.ts"]
    );
    assert_eq!(
        graph
            .roots
            .iter()
            .map(|root| root.file_id)
            .collect::<Vec<_>>(),
        [
            Some(FileId::new(0)),
            Some(FileId::new(1)),
            Some(FileId::new(0)),
            None
        ]
    );
    assert_eq!(
        graph
            .sources
            .iter()
            .map(|source| source.file_name.as_str())
            .collect::<Vec<_>>(),
        ["/project/z.ts", "/project/a.ts"]
    );
    assert_eq!(graph.roots[0].file_name, "/project/z.ts");
    assert_eq!(graph.options, *program.options());
    let diagnostics = program.diagnostics().to_vec();
    file_system
        .write_file("/project/z.ts", "changed after loading")
        .unwrap();
    assert_eq!(graph, program.project_graph_snapshot());
    assert_eq!(program.diagnostics(), diagnostics);
    drop(program);
    assert_eq!(graph.sources[0].source_text, "export const z = 1;");
}

#[test]
fn graph_snapshot_keeps_each_mode_and_unresolved_lookup() {
    let file_system = MemoryFileSystem::new(true);
    write_files(
        &file_system,
        &[
            (
                "/project/main.mts",
                concat!(
                    "import { value } from 'pkg';\n",
                    "import other = require('pkg');\n",
                    "import { missing } from './missing.js';\n",
                ),
            ),
            (
                "/project/node_modules/pkg/package.json",
                r#"{"name":"pkg","exports":{".":{"import":"./index.d.mts","require":"./index.d.cts"}}}"#,
            ),
            (
                "/project/node_modules/pkg/index.d.mts",
                "export declare const value: number;",
            ),
            (
                "/project/node_modules/pkg/index.d.cts",
                "export declare const value: string;",
            ),
        ],
    );
    let options = CompilerOptions {
        module: ModuleKind::NodeNext,
        module_resolution: ModuleResolutionKind::NodeNext,
        ..graph_options()
    };
    let program =
        Program::new_with_options(&file_system, "/project", &["main.mts".to_owned()], options);
    let graph = program.project_graph_snapshot();
    assert_eq!(
        graph.resolution_options.as_ref().unwrap().mode,
        ResolutionMode::NodeNext
    );
    let [import, require, missing] = graph.resolutions.as_slice() else {
        panic!("expected three resolver calls: {:?}", graph.resolutions);
    };
    for (resolution, mode, extension, target_mode) in [
        (
            import,
            ModuleFormat::Esm,
            "mts",
            CanonicalModuleResolutionMode::Esm,
        ),
        (
            require,
            ModuleFormat::CommonJs,
            "cts",
            CanonicalModuleResolutionMode::CommonJs,
        ),
    ] {
        assert_eq!(resolution.request.mode, Some(mode));
        assert_eq!(resolution.result.effective_mode, Some(mode));
        assert_eq!(resolution.request.kind, ProgramGraphResolutionKind::Module);
        assert_eq!(resolution.request.specifier, "pkg");
        assert!(resolution.request.range.is_some());
        assert_eq!(
            resolution
                .result
                .resolved
                .as_ref()
                .unwrap()
                .resolved_file_name,
            format!("/project/node_modules/pkg/index.d.{extension}")
        );
        assert_eq!(
            resolution.target.as_ref().unwrap().emit_module_mode,
            target_mode
        );
    }
    assert_eq!(missing.request.specifier, "./missing.js");
    assert_eq!(missing.request.mode, Some(ModuleFormat::Esm));
    assert!(missing.result.resolved.is_none());
    assert!(missing.target.is_none());
    assert!(!missing.result.failed_lookups.is_empty());
    let manifest = graph.module_resolution_manifest.unwrap();
    assert_eq!(manifest.entries().len(), 3);
    assert_eq!(
        manifest.entries()[2].resolution(),
        CanonicalModuleResolutionInput::Unresolved
    );
}

#[test]
fn graph_snapshot_retains_package_aliases_and_location_choices() {
    let file_system = MemoryFileSystem::new(true);
    write_files(
        &file_system,
        &[
            (
                "/shared/package.json",
                r#"{"name":"real-package","exports":{".":"./index.js"}}"#,
            ),
            (
                "/shared/index.d.ts",
                "export interface Item { value: number; }",
            ),
            ("/outside/use.ts", "export const outside = 1;"),
        ],
    );
    for (directory, alias) in [("/one", "alias-one"), ("/two", "alias-two")] {
        file_system.add_directory_link("/shared", &format!("{directory}/node_modules/{alias}"));
        file_system
            .write_file(
                &format!("{directory}/use.ts"),
                &format!("import type {{ Item }} from '{alias}';"),
            )
            .unwrap();
    }
    let program = Program::new_with_options(
        &file_system,
        "/",
        &["/one/use.ts", "/two/use.ts", "/outside/use.ts"].map(str::to_owned),
        graph_options(),
    );
    let graph = program.project_graph_snapshot();
    assert_eq!(
        graph.package_export_specifiers["/shared/index.d.ts"],
        ["alias-one", "alias-two"],
    );
    for (file, expected) in [
        ("/one/use.ts", Some("alias-one")),
        ("/two/use.ts", Some("alias-two")),
        ("/outside/use.ts", None),
    ] {
        let file_id = program.source_file(file).unwrap().id;
        assert_eq!(
            graph
                .package_display_specifiers
                .get(&(file_id, "/shared/index.d.ts".to_owned()))
                .map(String::as_str),
            expected,
        );
    }
    assert_eq!(program.project_graph_snapshot(), graph);
}

#[test]
fn graph_snapshot_distinguishes_ambient_fallback_from_a_resolver_hit() {
    let file_system = MemoryFileSystem::new(true);
    write_files(
        &file_system,
        &[
            ("/project/main.ts", "import { value } from 'ambient';"),
            (
                "/project/ambient.d.ts",
                "declare module 'ambient' { export const value: number; }",
            ),
        ],
    );
    let program = Program::new_with_options(
        &file_system,
        "/project",
        &["main.ts".to_owned(), "ambient.d.ts".to_owned()],
        graph_options(),
    );
    let graph = program.project_graph_snapshot();
    let [resolution] = graph.resolutions.as_slice() else {
        panic!("expected one import: {:?}", graph.resolutions);
    };
    assert!(resolution.result.resolved.is_none());
    assert!(!resolution.result.failed_lookups.is_empty());
    assert_eq!(
        resolution.ambient_target.as_deref(),
        Some("/project/ambient.d.ts")
    );
    assert_eq!(resolution.target.as_ref().unwrap().file_id, FileId::new(1));
    assert!(matches!(
        graph.module_resolution_manifest.unwrap().entries()[0].resolution(),
        CanonicalModuleResolutionInput::Resolved(_)
    ));
}

#[test]
fn graph_snapshot_records_type_directives_runtime_and_reference_targets() {
    let file_system = MemoryFileSystem::new(true);
    write_files(
        &file_system,
        &[
            (
                "/project/main.tsx",
                concat!(
                    "/// <reference types='missing-explicit' />\n",
                    "/// <reference path='./missing-path.ts' />\n",
                    "/// <reference lib='es5' />\n",
                    "export const view = <div />;\n",
                ),
            ),
            (
                "/project/node_modules/@types/present/index.d.ts",
                "declare const present: number;",
            ),
        ],
    );
    let options = CompilerOptions {
        no_lib: false,
        lib: Some(Vec::new()),
        no_check: false,
        jsx: JsxEmit::ReactJsx,
        types: Some(vec!["present".to_owned(), "missing-automatic".to_owned()]),
        ..graph_options()
    };
    let program =
        Program::new_with_options(&file_system, "/project", &["main.tsx".to_owned()], options);
    let graph = program.project_graph_snapshot();
    let [present, automatic, explicit, runtime] = graph.resolutions.as_slice() else {
        panic!("expected type and runtime calls: {:?}", graph.resolutions);
    };
    assert_eq!(
        present.request.kind,
        ProgramGraphResolutionKind::AutomaticTypeDirective
    );
    assert_eq!(present.request.specifier, "present");
    assert!(present.target.is_some());
    assert_eq!(
        automatic.request.kind,
        ProgramGraphResolutionKind::AutomaticTypeDirective
    );
    assert_eq!(automatic.request.specifier, "missing-automatic");
    assert!(automatic.result.resolved.is_none());
    assert_eq!(
        explicit.request.kind,
        ProgramGraphResolutionKind::TypeReference
    );
    assert_eq!(explicit.request.specifier, "missing-explicit");
    assert!(explicit.request.range.is_some());
    assert!(explicit.result.resolved.is_none());
    assert_eq!(runtime.request.kind, ProgramGraphResolutionKind::JsxRuntime);
    assert_eq!(runtime.request.specifier, "react/jsx-runtime");
    assert_eq!(runtime.request.mode, Some(ModuleFormat::Esm));
    assert!(runtime.result.resolved.is_none());
    let [path, library] = graph.references.as_slice() else {
        panic!(
            "expected path and library references: {:?}",
            graph.references
        );
    };
    assert_eq!(path.kind, ProgramGraphReferenceKind::Path);
    assert!(!path.skipped);
    assert_eq!(path.targets[0].file_name, "/project/missing-path.ts");
    assert!(path.targets[0].file_id.is_none());
    assert_eq!(library.kind, ProgramGraphReferenceKind::Library);
    assert!(
        library
            .targets
            .iter()
            .all(|target| target.file_id.is_some())
    );
    assert!(graph.sources.iter().any(|source| {
        source.is_default_library && source.file_name == "/__typescript/lib/lib.es5.d.ts"
    }));
    assert!(
        !graph
            .missing_evidence
            .contains(&ProgramGraphMissingEvidence::ResolutionDefaultModes)
    );

    let no_lib = Program::new_with_options(
        &file_system,
        "/project",
        &["main.tsx".to_owned()],
        CompilerOptions {
            no_lib: true,
            lib: None,
            ..program.options().clone()
        },
    )
    .project_graph_snapshot();
    assert_eq!(no_lib.resolutions, graph.resolutions);
    assert_eq!(no_lib.references, vec![path.clone()]);
    assert!(
        no_lib
            .sources
            .iter()
            .all(|source| !source.is_default_library)
    );
}

#[test]
fn graph_snapshot_keeps_terminal_realpath_and_names_missing_package_evidence() {
    let file_system = MemoryFileSystem::new(true);
    write_files(
        &file_system,
        &[
            ("/project/main.ts", "import { value } from 'pkg';"),
            (
                "/packages/pkg/package.json",
                r#"{"name":"pkg","version":"1.2.3","types":"index.d.ts"}"#,
            ),
            (
                "/packages/pkg/index.d.ts",
                "export declare const value: number;",
            ),
        ],
    );
    file_system.add_directory_link("/packages/pkg", "/project/node_modules/pkg");
    let program = Program::new_with_options(
        &file_system,
        "/project",
        &["main.ts".to_owned()],
        graph_options(),
    );
    let graph = program.project_graph_snapshot();
    let resolved = graph.resolutions[0].result.resolved.as_ref().unwrap();
    assert_eq!(resolved.resolved_file_name, "/packages/pkg/index.d.ts");
    assert_eq!(
        resolved.original_file_name,
        "/project/node_modules/pkg/index.d.ts"
    );
    assert_eq!(
        resolved.package_json.as_deref(),
        Some("/project/node_modules/pkg/package.json")
    );
    assert!(resolved.is_external_library_import);
    assert_eq!(
        graph.resolutions[0].target.as_ref().unwrap().file_name,
        resolved.resolved_file_name
    );
    assert!(
        !graph
            .missing_evidence
            .contains(&ProgramGraphMissingEvidence::ResolutionOriginalPaths)
    );
    assert!(
        graph
            .missing_evidence
            .contains(&ProgramGraphMissingEvidence::PackageIdentities)
    );
    assert!(
        graph
            .missing_evidence
            .contains(&ProgramGraphMissingEvidence::SourcePackageScopes)
    );
}

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct ProjectDirectory(PathBuf);

impl ProjectDirectory {
    fn new() -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ts-rust-project-graph-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, source: &str) {
        fs::write(self.0.join(name), source).unwrap();
    }
}

impl Drop for ProjectDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn graph_snapshot_owns_on_disk_config_and_effective_options() {
    let directory = ProjectDirectory::new();
    directory.write(
        "base.json",
        r#"{"compilerOptions":{"strict":true,"lib":["es5"],"types":[],"skipLibCheck":true,"noEmit":true}}"#,
    );
    let config_text = r#"{"extends":"./base.json","files":["z.ts","a.ts"]}"#;
    directory.write("tsconfig.json", config_text);
    directory.write("z.ts", "const z: number = 1;");
    directory.write("a.ts", "const a: string = 'a';");
    let config_path = directory.0.join("tsconfig.json");
    let (program, graph) = Program::try_from_config_with_canonical_checker_and_queries(
        &OsFileSystem::default(),
        config_path.to_str().unwrap(),
        |program, _| program.project_graph_snapshot(),
    )
    .unwrap();
    let graph = graph.unwrap();
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert_eq!(graph.config_file_path.as_deref(), config_path.to_str());
    assert_eq!(
        graph.config.as_ref().unwrap().source_text.as_deref(),
        Some(config_text)
    );
    assert_eq!(
        graph.config.as_ref().unwrap().resolved.path,
        config_path.to_string_lossy()
    );
    assert!(graph.options.strict);
    assert!(graph.options.strict_null_checks);
    assert!(graph.options.no_implicit_any);
    assert_eq!(
        graph.roots[0].file_name,
        directory.0.join("z.ts").to_string_lossy()
    );
    assert_eq!(
        graph.roots[1].file_name,
        directory.0.join("a.ts").to_string_lossy()
    );
    assert!(graph.sources.iter().any(|source| source.is_default_library));
    assert!(
        !graph
            .missing_evidence
            .contains(&ProgramGraphMissingEvidence::ConfigExtendsInputs)
    );
    directory.write("tsconfig.json", "changed after loading");
    assert_eq!(program.project_graph_snapshot(), graph);
}

#[test]
fn graph_snapshot_retains_decoded_config_parser_text_not_disk_bytes() {
    let directory = ProjectDirectory::new();
    directory.write("main.ts", "const value = 1;");
    let text =
        r#"{"files":["main.ts"],"compilerOptions":{"noCheck":true,"noEmit":true,"noLib":true}}"#;
    let bytes = std::iter::once(0xfeff)
        .chain(text.encode_utf16())
        .flat_map(u16::to_le_bytes)
        .collect::<Vec<_>>();
    let config_path = directory.0.join("tsconfig.json");
    fs::write(&config_path, &bytes).unwrap();
    let program = Program::from_config(&OsFileSystem::default(), config_path.to_str().unwrap());
    let graph = program.project_graph_snapshot();
    let observation = graph.config_resolution_observation.as_ref().unwrap();
    assert!(observation.is_complete());
    let parser_text = observation
        .events
        .iter()
        .find_map(|event| match event {
            ts_config::ConfigResolutionEvent::ReadFile {
                kind: ts_config::ConfigInputKind::Config,
                result: Ok(text),
                ..
            } => Some(text),
            _ => None,
        })
        .unwrap();
    assert_eq!(parser_text, text);
    assert_ne!(parser_text.len(), bytes.len());
    assert_eq!(
        graph.config.as_ref().unwrap().source_text.as_deref(),
        Some(text)
    );
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn graph_snapshot_keeps_manifest_errors_and_no_resolve_skips() {
    let file_system = MemoryFileSystem::new(true);
    write_files(
        &file_system,
        &[
            (
                "/project/main.ts",
                "/// <reference path='./ignored.ts' />\nimport { value } from './script';",
            ),
            ("/project/script.ts", "const value = 1;"),
            ("/project/ignored.ts", "const ignored = 2;"),
        ],
    );
    let program = Program::new_with_options(
        &file_system,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            no_resolve: true,
            ..graph_options()
        },
    );
    let graph = program.project_graph_snapshot();
    assert!(matches!(
        graph.module_resolution_manifest,
        Err(CanonicalProgramCheckError::ExternalModuleTargetUnsupported { .. })
    ));
    assert!(graph.resolutions[0].target.is_some());
    assert!(graph.references[0].skipped);
    assert!(graph.references[0].targets.is_empty());
    assert!(
        graph
            .sources
            .iter()
            .all(|source| source.file_name != "/project/ignored.ts")
    );
}
