use std::{
    collections::{BTreeMap, VecDeque},
    io,
    sync::Mutex,
};

use ts_ast::FileId;
use ts_compiler::{
    Program, ProgramGraphMissingEvidence, ProgramGraphPackageScopeDecision as Decision,
    ProgramGraphPackageScopeEvent as Event, ProgramGraphPackageScopeReadError,
};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Call {
    FileExists(String),
    DirectoryExists(String),
    ReadFile(String),
    ReadDirectory(String),
    Realpath(String),
    ModifiedTime(String),
}

struct RecordingFileSystem {
    inner: MemoryFileSystem,
    calls: Mutex<Vec<Call>>,
    replies: Mutex<BTreeMap<String, VecDeque<io::Result<String>>>>,
}

impl RecordingFileSystem {
    fn new() -> Self {
        Self {
            inner: MemoryFileSystem::new(true),
            calls: Mutex::default(),
            replies: Mutex::default(),
        }
    }

    fn reply_to_reads(&self, path: &str, replies: impl IntoIterator<Item = io::Result<String>>) {
        self.replies
            .lock()
            .unwrap()
            .insert(path.to_owned(), replies.into_iter().collect());
    }

    fn calls(&self) -> Vec<Call> {
        self.calls.lock().unwrap().clone()
    }
}

impl FileSystem for RecordingFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.inner.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.calls
            .lock()
            .unwrap()
            .push(Call::FileExists(path.to_owned()));
        self.inner.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.calls
            .lock()
            .unwrap()
            .push(Call::DirectoryExists(path.to_owned()));
        self.inner.directory_exists(path)
    }

    fn realpath(&self, path: &str) -> String {
        self.calls
            .lock()
            .unwrap()
            .push(Call::Realpath(path.to_owned()));
        self.inner.realpath(path)
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.calls
            .lock()
            .unwrap()
            .push(Call::ModifiedTime(path.to_owned()));
        self.inner.modified_time(path)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        self.calls
            .lock()
            .unwrap()
            .push(Call::ReadFile(path.to_owned()));
        if let Some(reply) = self
            .replies
            .lock()
            .unwrap()
            .get_mut(path)
            .and_then(VecDeque::pop_front)
        {
            return reply;
        }
        self.inner.read_file(path)
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        self.inner.write_file(path, contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        self.calls
            .lock()
            .unwrap()
            .push(Call::ReadDirectory(path.to_owned()));
        self.inner.read_directory(path)
    }
}

fn options() -> CompilerOptions {
    CompilerOptions {
        no_check: true,
        no_emit: true,
        no_lib: true,
        allow_js: true,
        types: Some(Vec::new()),
        module: ModuleKind::NodeNext,
        module_resolution: ModuleResolutionKind::NodeNext,
        ..CompilerOptions::default()
    }
}

fn load_program(filesystem: &dyn FileSystem, roots: &[String], canonical: bool) -> Program {
    if canonical {
        Program::try_new_with_canonical_checker_and_queries(
            filesystem,
            "/project",
            roots,
            options(),
            |_, _| panic!("noCheck must not construct a checker"),
        )
        .unwrap()
        .0
    } else {
        Program::new_with_options(filesystem, "/project", roots, options())
    }
}

#[test]
fn package_scope_observation_keeps_each_dynamic_read_and_duplicate_roots_stay_cold() {
    const FIRST: &str = "\r\n{\"type\":\"module\",\"description\":\"\\u0061\"}\r\n";
    const SECOND: &str = "{\"type\":\"commonjs\"}";
    for canonical in [false, true] {
        let filesystem = RecordingFileSystem::new();
        for path in ["/project/sub/a.ts", "/project/sub/b.ts"] {
            filesystem
                .write_file(path, "export const value = 1;")
                .unwrap();
        }
        filesystem
            .write_file("/project/package.json", "{}")
            .unwrap();
        filesystem.reply_to_reads(
            "/project/package.json",
            [Ok(FIRST.to_owned()), Ok(SECOND.to_owned())],
        );
        let program = load_program(
            &filesystem,
            &[
                "sub/a.ts".to_owned(),
                "sub/b.ts".to_owned(),
                "sub/a.ts".to_owned(),
            ],
            canonical,
        );
        let graph = program.project_graph_snapshot();
        let mut expected = Vec::new();
        for (file_id, text, format) in [
            (FileId::new(0), FIRST, ModuleKind::EsNext),
            (FileId::new(1), SECOND, ModuleKind::CommonJs),
        ] {
            expected.extend([
                Event::FileExists {
                    file_id,
                    path: "/project/sub/package.json".to_owned(),
                    exists: false,
                },
                Event::FileExists {
                    file_id,
                    path: "/project/package.json".to_owned(),
                    exists: true,
                },
                Event::ReadFile {
                    file_id,
                    path: "/project/package.json".to_owned(),
                    result: Ok(text.to_owned()),
                },
                Event::Decision {
                    file_id,
                    implied_node_format: format,
                    reason: Decision::PackageJson,
                },
            ]);
        }
        assert_eq!(graph.source_package_scope_observation.events, expected);
        assert!(graph.source_package_scope_observation.is_complete());
        assert_eq!(graph.sources[0].file_id, FileId::new(0));
        assert_eq!(graph.sources[0].implied_node_format, ModuleKind::EsNext);
        assert_eq!(graph.sources[1].file_id, FileId::new(1));
        assert_eq!(graph.sources[1].implied_node_format, ModuleKind::CommonJs);
        assert_eq!(graph.roots[0].file_id, graph.roots[2].file_id);
        assert!(
            !graph
                .missing_evidence
                .contains(&ProgramGraphMissingEvidence::SourcePackageScopes)
        );
        assert!(
            graph
                .missing_evidence
                .contains(&ProgramGraphMissingEvidence::SourceRealPaths)
        );
        assert!(
            graph
                .missing_evidence
                .contains(&ProgramGraphMissingEvidence::PackageIdentities)
        );
        let calls = filesystem.calls();
        assert_eq!(
            calls,
            [
                Call::ReadFile("/project/sub/a.ts".to_owned()),
                Call::FileExists("/project/sub/package.json".to_owned()),
                Call::FileExists("/project/package.json".to_owned()),
                Call::ReadFile("/project/package.json".to_owned()),
                Call::ReadFile("/project/sub/b.ts".to_owned()),
                Call::FileExists("/project/sub/package.json".to_owned()),
                Call::FileExists("/project/package.json".to_owned()),
                Call::ReadFile("/project/package.json".to_owned()),
            ]
        );
        filesystem
            .write_file("/project/package.json", "changed after loading")
            .unwrap();
        assert_eq!(program.project_graph_snapshot(), graph);
        assert_eq!(program.project_graph_snapshot(), graph);
        assert_eq!(filesystem.calls(), calls);
        drop(program);
        assert_eq!(graph.source_package_scope_observation.events, expected);
    }
}

#[test]
fn package_scope_observation_stops_at_the_first_existing_package_after_read_or_parse_failure() {
    for (reply, retained, reason) in [
        (
            Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "denied\r\n",
            )),
            Err(ProgramGraphPackageScopeReadError {
                kind: io::ErrorKind::PermissionDenied,
                message: "denied\r\n".to_owned(),
            }),
            Decision::ReadFailure,
        ),
        (
            Err(io::Error::new(
                io::ErrorKind::NotFound,
                "removed after probe",
            )),
            Err(ProgramGraphPackageScopeReadError {
                kind: io::ErrorKind::NotFound,
                message: "removed after probe".to_owned(),
            }),
            Decision::ReadFailure,
        ),
        (
            Ok("\u{feff}{\"type\":\"module\"}\r\n".to_owned()),
            Ok("\u{feff}{\"type\":\"module\"}\r\n".to_owned()),
            Decision::InvalidPackageJson,
        ),
        (
            Ok("{}".to_owned()),
            Ok("{}".to_owned()),
            Decision::PackageJson,
        ),
    ] {
        let filesystem = RecordingFileSystem::new();
        filesystem
            .write_file("/project/sub/main.ts", "export const value = 1;")
            .unwrap();
        filesystem
            .write_file("/project/sub/package.json", "{}")
            .unwrap();
        filesystem
            .write_file("/project/package.json", "{\"type\":\"module\"}")
            .unwrap();
        filesystem.reply_to_reads("/project/sub/package.json", [reply]);
        let program = load_program(&filesystem, &["sub/main.ts".to_owned()], false);
        let graph = program.project_graph_snapshot();
        let file_id = graph.sources[0].file_id;
        assert_eq!(graph.sources[0].implied_node_format, ModuleKind::CommonJs);
        assert_eq!(
            graph.source_package_scope_observation.events,
            [
                Event::FileExists {
                    file_id,
                    path: "/project/sub/package.json".to_owned(),
                    exists: true
                },
                Event::ReadFile {
                    file_id,
                    path: "/project/sub/package.json".to_owned(),
                    result: retained
                },
                Event::Decision {
                    file_id,
                    implied_node_format: ModuleKind::CommonJs,
                    reason
                },
            ]
        );
        assert!(graph.source_package_scope_observation.is_complete());
        assert!(
            !graph
                .missing_evidence
                .contains(&ProgramGraphMissingEvidence::SourcePackageScopes)
        );
        assert_eq!(
            filesystem.calls(),
            [
                Call::ReadFile("/project/sub/main.ts".to_owned()),
                Call::FileExists("/project/sub/package.json".to_owned()),
                Call::ReadFile("/project/sub/package.json".to_owned()),
            ]
        );
    }
}

#[test]
fn package_scope_observation_keeps_all_negative_probes_without_reading_a_package() {
    let filesystem = RecordingFileSystem::new();
    filesystem
        .write_file("/project/sub/main.ts", "export const value = 1;")
        .unwrap();
    let program = load_program(&filesystem, &["sub/main.ts".to_owned()], false);
    let graph = program.project_graph_snapshot();
    let file_id = graph.sources[0].file_id;
    assert_eq!(graph.sources[0].implied_node_format, ModuleKind::CommonJs);
    assert_eq!(
        graph.source_package_scope_observation.events,
        [
            Event::FileExists {
                file_id,
                path: "/project/sub/package.json".to_owned(),
                exists: false
            },
            Event::FileExists {
                file_id,
                path: "/project/package.json".to_owned(),
                exists: false
            },
            Event::FileExists {
                file_id,
                path: "/package.json".to_owned(),
                exists: false
            },
            Event::Decision {
                file_id,
                implied_node_format: ModuleKind::CommonJs,
                reason: Decision::NoPackage
            },
        ]
    );
    assert_eq!(
        filesystem.calls(),
        [
            Call::ReadFile("/project/sub/main.ts".to_owned()),
            Call::FileExists("/project/sub/package.json".to_owned()),
            Call::FileExists("/project/package.json".to_owned()),
            Call::FileExists("/package.json".to_owned()),
        ]
    );
    assert!(graph.source_package_scope_observation.is_complete());
    assert!(
        !graph
            .missing_evidence
            .contains(&ProgramGraphMissingEvidence::SourcePackageScopes)
    );
}

#[test]
fn package_scope_observation_records_fixed_formats_without_package_probes() {
    let filesystem = RecordingFileSystem::new();
    let sources = [
        ("a.mts", ModuleKind::EsNext),
        ("b.mjs", ModuleKind::EsNext),
        ("c.cts", ModuleKind::CommonJs),
        ("d.cjs", ModuleKind::CommonJs),
        ("e.d.MTS", ModuleKind::EsNext),
        ("f.d.CTS", ModuleKind::CommonJs),
    ];
    for (name, _) in sources {
        filesystem
            .write_file(&format!("/project/{name}"), "export const value = 1;")
            .unwrap();
    }
    filesystem
        .write_file("/project/package.json", "{\"type\":\"module\"}")
        .unwrap();
    let program = load_program(
        &filesystem,
        &sources.map(|(name, _)| name.to_owned()),
        false,
    );
    let graph = program.project_graph_snapshot();
    assert_eq!(graph.sources.len(), sources.len());
    assert_eq!(
        graph.source_package_scope_observation.events,
        sources
            .iter()
            .enumerate()
            .map(|(index, (_, format))| {
                Event::Decision {
                    file_id: FileId::new(u32::try_from(index).unwrap()),
                    implied_node_format: *format,
                    reason: Decision::FixedExtension,
                }
            })
            .collect::<Vec<_>>()
    );
    for (source, (_, format)) in graph.sources.iter().zip(sources) {
        assert_eq!(source.implied_node_format, format);
    }
    assert_eq!(
        filesystem.calls(),
        sources.map(|(name, _)| Call::ReadFile(format!("/project/{name}")))
    );
    assert!(graph.source_package_scope_observation.is_complete());
    assert!(
        !graph
            .missing_evidence
            .contains(&ProgramGraphMissingEvidence::SourcePackageScopes)
    );
}

#[test]
fn canonical_source_replay_does_not_repeat_package_scope_calls() {
    let filesystem = RecordingFileSystem::new();
    filesystem
        .write_file("/project/main.ts", "export const value: number = 1;")
        .unwrap();
    filesystem
        .write_file("/project/package.json", "{\"type\":\"module\"}")
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            no_check: false,
            no_lib: false,
            lib: Some(vec!["es5".to_owned()]),
            ..options()
        },
        |program, queries| {
            let graph = program.project_graph_snapshot();
            let calls = filesystem.calls();
            filesystem
                .write_file("/project/package.json", "{\"type\":\"commonjs\"}")
                .unwrap();
            assert!(queries.replay_sources().unwrap().is_empty());
            assert_eq!(program.project_graph_snapshot(), graph);
            assert_eq!(filesystem.calls(), calls);
            let source = graph
                .sources
                .iter()
                .find(|source| source.file_name == "/project/main.ts")
                .unwrap();
            assert_eq!(source.implied_node_format, ModuleKind::EsNext);
            assert_eq!(graph.source_package_scope_observation.events.len(), 3);
            assert!(graph.sources.iter().any(|source| source.is_default_library));
            assert!(
                !graph
                    .missing_evidence
                    .contains(&ProgramGraphMissingEvidence::SourcePackageScopes)
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
