use std::{
    io,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use serde_json::{Value, json};
use ts_compiler::{
    Program, ProgramGraphMissingEvidence, ProgramGraphPackageScopeDecision,
    ProgramGraphPackageScopeEvent, ProgramGraphPackageScopeObservation,
    ProgramGraphPackageScopeReadError, ProgramGraphResolution, ProgramGraphResolutionKind,
    ProgramGraphResolutionRequest,
};
use ts_module::{
    PackageJsonInputEvent, PackageJsonInputPurpose, PackageJsonInputReadError, PackageJsonInputs,
    ResolutionMode, ResolutionOptions, ResolutionResult, Resolver,
};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

use super::{
    missing_evidence_report, package_json_inputs_report, parser_input_text_report, snapshot_report,
    source_package_scope_observation_report,
};
use crate::{SCORECARD_DIGEST_ALGORITHM, stable_digest};

const PACKAGE_TEXT: &str =
    "{\r\n\"type\":\"module\",\"types\":\"index.d.ts\",\"unused\":\"first \u{00e9}\"}\r\n";
const CHANGED_PACKAGE_TEXT: &str =
    "{\r\n\"type\":\"module\",\"types\":\"index.d.ts\",\"unused\":\"second\"}\r\n";
const PACKAGE_PATH: &str = "/project/node_modules/pkg/package.json";
const TARGET_PATH: &str = "/project/node_modules/pkg/index.d.ts";

struct CountingFileSystem {
    inner: MemoryFileSystem,
    calls: AtomicUsize,
}

impl CountingFileSystem {
    fn new() -> Self {
        let inner = MemoryFileSystem::new(true);
        for (path, text) in [
            ("/project/package.json", r#"{"type":"module"}"#),
            (
                "/project/main.ts",
                "import { value } from 'pkg'; export { value };",
            ),
            (PACKAGE_PATH, PACKAGE_TEXT),
            (TARGET_PATH, "export declare const value: number;"),
        ] {
            inner.write_file(path, text).unwrap();
        }
        Self {
            inner,
            calls: AtomicUsize::new(0),
        }
    }

    fn calls(&self) -> usize {
        self.calls.load(Ordering::Relaxed)
    }
}

impl FileSystem for CountingFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.directory_exists(path)
    }

    fn realpath(&self, path: &str) -> String {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.realpath(path)
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.modified_time(path)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.read_file(path)
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        self.inner.write_file(path, contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.read_directory(path)
    }
}

fn build_program(filesystem: &dyn FileSystem, preserve_symlinks: bool) -> Program {
    Program::new_with_options(
        filesystem,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            no_check: true,
            no_emit: true,
            no_lib: true,
            types: Some(Vec::new()),
            module: ModuleKind::EsNext,
            module_resolution: ModuleResolutionKind::Bundler,
            preserve_symlinks,
            ..CompilerOptions::default()
        },
    )
}

#[test]
fn package_input_report_keeps_absent_empty_and_incomplete_prefixes_distinct() {
    assert_eq!(package_json_inputs_report(None), Value::Null);
    assert_eq!(
        package_json_inputs_report(Some(&PackageJsonInputs::default())),
        json!({
            "inputOrigin": "resolver_worker",
            "retentionComplete": true,
            "omittedEvents": 0,
            "textRepresentation": "vfs_parser_input",
            "events": [],
        })
    );
    let text = "\u{feff}{\r\n\"type\":\"module\",\"name\":\"\u{00e9}\"}\r\n";
    let inputs = PackageJsonInputs {
        events: vec![
            PackageJsonInputEvent::FileExists {
                path: PACKAGE_PATH.to_owned(),
                exists: true,
            },
            PackageJsonInputEvent::ReadFile {
                path: PACKAGE_PATH.to_owned(),
                purpose: PackageJsonInputPurpose::DefaultMode,
                result: Ok(text.to_owned()),
            },
            PackageJsonInputEvent::ReadFile {
                path: PACKAGE_PATH.to_owned(),
                purpose: PackageJsonInputPurpose::PackageResolution,
                result: Err(PackageJsonInputReadError {
                    kind: io::ErrorKind::PermissionDenied,
                    message: "denied \u{00e9}\r\n".to_owned(),
                }),
            },
        ]
        .into(),
        omitted_events: 4,
    };
    assert_eq!(
        package_json_inputs_report(Some(&inputs)),
        json!({
            "inputOrigin": "resolver_worker",
            "retentionComplete": false,
            "omittedEvents": 4,
            "textRepresentation": "vfs_parser_input",
            "events": [
                {"kind": "file_exists", "path": PACKAGE_PATH, "exists": true},
                {"kind": "read_file", "path": PACKAGE_PATH, "purpose": "default_mode",
                 "result": {
                     "status": "read", "parserInputText": text,
                     "parserInputTextUtf8ByteCount": text.len(),
                     "parserInputTextDigest": stable_digest(text.as_bytes()),
                     "digestAlgorithm": SCORECARD_DIGEST_ALGORITHM,
                 }},
                {"kind": "read_file", "path": PACKAGE_PATH, "purpose": "package_resolution",
                 "result": {"status": "error", "errorKind": "PermissionDenied", "message": "denied \u{00e9}\r\n"}},
            ],
        })
    );
}

#[test]
fn package_input_gaps_do_not_clear_other_graph_gaps() {
    for (inputs, incomplete) in [
        (None, true),
        (Some(PackageJsonInputs::default()), false),
        (
            Some(PackageJsonInputs {
                omitted_events: 1,
                ..PackageJsonInputs::default()
            }),
            true,
        ),
    ] {
        let mut graph = Program::default().project_graph_snapshot();
        graph.missing_evidence = vec![
            ProgramGraphMissingEvidence::ConfigParseInputs,
            ProgramGraphMissingEvidence::SourceRealPaths,
            ProgramGraphMissingEvidence::ResolutionDefaultModes,
            ProgramGraphMissingEvidence::PackageIdentities,
            ProgramGraphMissingEvidence::SourcePackageScopes,
        ];
        graph.resolutions.push(ProgramGraphResolution {
            request: ProgramGraphResolutionRequest {
                kind: ProgramGraphResolutionKind::Module,
                containing_file: "/project/main.ts".to_owned(),
                range: None,
                specifier: "pkg".to_owned(),
                mode: None,
            },
            result: ResolutionResult {
                package_json_inputs: inputs,
                ..ResolutionResult::default()
            },
            ambient_target: None,
            target: None,
        });
        let mut expected = vec![
            "config_parse_inputs",
            "source_real_paths",
            "resolution_default_modes",
            "package_identities",
            "source_package_scopes",
        ];
        if incomplete {
            expected.push("resolution_package_json_inputs");
        }
        assert_eq!(missing_evidence_report(&graph), expected);
    }
}

#[test]
fn source_scope_report_keeps_source_mapping_errors_and_incomplete_prefixes() {
    let filesystem = CountingFileSystem::new();
    let program = build_program(&filesystem, false);
    let graph = program.project_graph_snapshot();
    let retained =
        source_package_scope_observation_report(&program, &graph.source_package_scope_observation);
    let events = retained["events"].as_array().unwrap();
    assert_eq!(events.len(), 6);
    for event in &events[..3] {
        assert_eq!(event["sourceFile"], "/project/main.ts");
    }
    for event in &events[3..] {
        assert_eq!(event["sourceFile"], TARGET_PATH);
    }
    assert_eq!(events[4]["result"], parser_input_text_report(PACKAGE_TEXT));
    let source_id = program.source_file(TARGET_PATH).unwrap().id;
    let observation = ProgramGraphPackageScopeObservation {
        events: vec![
            ProgramGraphPackageScopeEvent::FileExists {
                file_id: source_id,
                path: PACKAGE_PATH.to_owned(),
                exists: true,
            },
            ProgramGraphPackageScopeEvent::ReadFile {
                file_id: source_id,
                path: PACKAGE_PATH.to_owned(),
                result: Err(ProgramGraphPackageScopeReadError {
                    kind: io::ErrorKind::PermissionDenied,
                    message: "denied\r\n".to_owned(),
                }),
            },
        ],
        omitted_events: 3,
    };
    assert_eq!(
        source_package_scope_observation_report(&program, &observation),
        json!({
            "retentionComplete": false,
            "omittedEvents": 3,
            "textRepresentation": "vfs_parser_input",
            "events": [
                {"kind": "file_exists", "sourceFile": TARGET_PATH, "path": PACKAGE_PATH, "exists": true},
                {"kind": "read_file", "sourceFile": TARGET_PATH, "path": PACKAGE_PATH,
                 "result": {"status": "error", "errorKind": "PermissionDenied", "message": "denied\r\n"}},
            ],
        })
    );
}

#[test]
fn source_scope_report_keeps_each_decision_reason_and_format() {
    let filesystem = CountingFileSystem::new();
    let program = build_program(&filesystem, false);
    let file_id = program.source_file("/project/main.ts").unwrap().id;
    for (reason, name, format, format_name) in [
        (
            ProgramGraphPackageScopeDecision::FixedExtension,
            "fixed_extension",
            ModuleKind::EsNext,
            "esnext",
        ),
        (
            ProgramGraphPackageScopeDecision::PackageJson,
            "package_json",
            ModuleKind::EsNext,
            "esnext",
        ),
        (
            ProgramGraphPackageScopeDecision::InvalidPackageJson,
            "invalid_package_json",
            ModuleKind::CommonJs,
            "commonjs",
        ),
        (
            ProgramGraphPackageScopeDecision::ReadFailure,
            "read_failure",
            ModuleKind::CommonJs,
            "commonjs",
        ),
        (
            ProgramGraphPackageScopeDecision::NoPackage,
            "no_package",
            ModuleKind::CommonJs,
            "commonjs",
        ),
    ] {
        let observation = ProgramGraphPackageScopeObservation {
            events: vec![ProgramGraphPackageScopeEvent::Decision {
                file_id,
                implied_node_format: format,
                reason,
            }],
            omitted_events: 0,
        };
        let report = source_package_scope_observation_report(&program, &observation);
        assert_eq!(
            report["events"],
            json!([{
                "kind": "decision", "sourceFile": "/project/main.ts",
                "impliedNodeFormat": format_name, "reason": name,
            }])
        );
        assert_eq!(report["retentionComplete"], true);
    }
}

#[test]
fn cached_package_input_reports_keep_original_worker_text_without_new_calls() {
    let filesystem = CountingFileSystem::new();
    let resolver = Resolver::new(
        &filesystem,
        ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        },
    );
    let original = resolver.resolve("pkg", "/project/main.ts");
    let original_report = package_json_inputs_report(original.package_json_inputs.as_ref());
    let calls = filesystem.calls();
    filesystem
        .write_file(PACKAGE_PATH, CHANGED_PACKAGE_TEXT)
        .unwrap();
    let cached = resolver.resolve("pkg", "/project/main.ts");
    assert_eq!(filesystem.calls(), calls);
    assert!(Arc::ptr_eq(
        &original.package_json_inputs.as_ref().unwrap().events,
        &cached.package_json_inputs.as_ref().unwrap().events,
    ));
    assert_eq!(
        original_report,
        package_json_inputs_report(cached.package_json_inputs.as_ref())
    );
    assert_eq!(original_report["inputOrigin"], "resolver_worker");
    assert!(
        original_report["events"]
            .as_array()
            .unwrap()
            .iter()
            .any(|event| {
                event["path"] == PACKAGE_PATH && event["result"]["parserInputText"] == PACKAGE_TEXT
            })
    );
    resolver.clear_cache();
    let fresh = resolver.resolve("pkg", "/project/main.ts");
    assert_eq!(original.resolved, fresh.resolved);
    assert_ne!(
        original_report,
        package_json_inputs_report(fresh.package_json_inputs.as_ref())
    );
}

#[test]
fn graph_digest_includes_retained_package_inputs_without_new_filesystem_calls() {
    let filesystem = CountingFileSystem::new();
    let program = build_program(&filesystem, false);
    let calls = filesystem.calls();
    let original = snapshot_report(&program);
    assert_eq!(filesystem.calls(), calls);
    filesystem
        .write_file(PACKAGE_PATH, CHANGED_PACKAGE_TEXT)
        .unwrap();
    assert_eq!(original, snapshot_report(&program));
    assert_eq!(filesystem.calls(), calls);
    let fresh = snapshot_report(&build_program(&filesystem, false));
    assert_eq!(original.evidence["sources"], fresh.evidence["sources"]);
    assert_eq!(
        original.evidence["resolutions"][0]["resolved"],
        fresh.evidence["resolutions"][0]["resolved"]
    );
    assert_ne!(original.digest, fresh.digest);
    assert_ne!(
        original.evidence["resolutions"][0]["packageJsonInputs"],
        fresh.evidence["resolutions"][0]["packageJsonInputs"]
    );
    assert_ne!(
        original.evidence["sourcePackageScopeObservation"],
        fresh.evidence["sourcePackageScopeObservation"]
    );
    for report in [&original, &fresh] {
        for gap in ["source_package_scopes", "resolution_package_json_inputs"] {
            assert!(!report.missing_evidence.iter().any(|value| value == gap));
        }
        for gap in ["source_real_paths", "package_identities"] {
            assert!(report.missing_evidence.iter().any(|value| value == gap));
        }
    }
}

#[test]
fn graph_report_projects_preserve_symlinks_and_selected_source_paths() {
    let filesystem = CountingFileSystem::new();
    filesystem
        .inner
        .add_directory_link("/project/node_modules/pkg", "/project/node_modules/alias");
    filesystem
        .write_file(
            "/project/main.ts",
            "import { value } from 'alias'; export { value };",
        )
        .unwrap();
    for (preserve_symlinks, selected) in [
        (false, TARGET_PATH),
        (true, "/project/node_modules/alias/index.d.ts"),
    ] {
        let graph = snapshot_report(&build_program(&filesystem, preserve_symlinks));
        assert_eq!(
            graph.evidence["resolutionOptions"]["preserveSymlinks"],
            preserve_symlinks
        );
        let resolution = &graph.evidence["resolutions"][0];
        assert_eq!(resolution["resolved"]["fileName"], selected);
        assert_eq!(resolution["loadedTarget"]["fileName"], selected);
        assert_eq!(
            resolution["resolved"]["originalFileName"],
            "/project/node_modules/alias/index.d.ts"
        );
        assert!(
            graph.evidence["sourcePackageScopeObservation"]["events"]
                .as_array()
                .unwrap()
                .iter()
                .any(|event| event["sourceFile"] == selected)
        );
        assert!(
            graph
                .missing_evidence
                .iter()
                .any(|gap| gap == "source_real_paths")
        );
    }
}
