use std::{
    collections::{BTreeMap, VecDeque},
    io,
    sync::Mutex,
};

use ts_compiler::{Program, ProgramGraphMissingEvidence};
use ts_config::{ConfigInputKind, ConfigResolutionEvent};
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

struct RecordingFileSystem {
    inner: MemoryFileSystem,
    reads: Mutex<Vec<String>>,
    replies: Mutex<BTreeMap<String, VecDeque<io::Result<String>>>>,
}

impl RecordingFileSystem {
    fn new() -> Self {
        Self {
            inner: MemoryFileSystem::new(true),
            reads: Mutex::default(),
            replies: Mutex::default(),
        }
    }

    fn reply_to_reads(&self, path: &str, replies: impl IntoIterator<Item = io::Result<String>>) {
        self.replies
            .lock()
            .unwrap()
            .insert(path.to_owned(), replies.into_iter().collect());
    }
}

impl FileSystem for RecordingFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.inner.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.inner.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.inner.directory_exists(path)
    }

    fn realpath(&self, path: &str) -> String {
        self.inner.realpath(path)
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.inner.modified_time(path)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        self.reads.lock().unwrap().push(path.to_owned());
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
        self.inner.read_directory(path)
    }
}

fn load_program(filesystem: &dyn FileSystem, canonical: bool) -> Program {
    if canonical {
        Program::try_from_config_with_canonical_checker_and_queries(
            filesystem,
            "/project/tsconfig.json",
            |_, _| panic!("noCheck or failed config loading must skip the checker callback"),
        )
        .unwrap()
        .0
    } else {
        Program::from_config(filesystem, "/project/tsconfig.json")
    }
}

#[test]
fn config_observation_keeps_parser_and_diagnostic_reads_separate() {
    const LEAF: &str = concat!(
        "\u{feff}{\r\n",
        "\"extends\":[\"./base\",\"./base\"],\"files\":[\"main.ts\"],",
        "\"compilerOptions\":{\"noCheck\":true,\"noEmit\":true,\"noLib\":true,\"types\":[]}\r\n}",
    );
    const LATER: &str = r#"{"files":["changed.ts"],"compilerOptions":{"strict":true}}"#;
    const FIRST_BASE: &str = r#"{"compilerOptions":{"strict":true}}"#;
    const SECOND_BASE: &str = r#"{"compilerOptions":{"strict":false}}"#;
    for canonical in [false, true] {
        for diagnostic_read_fails in [false, true] {
            let filesystem = RecordingFileSystem::new();
            filesystem
                .write_file("/project/tsconfig.json", LEAF)
                .unwrap();
            filesystem.write_file("/project/base.json", "{}").unwrap();
            filesystem
                .write_file("/project/main.ts", "const value = 1;")
                .unwrap();
            filesystem.reply_to_reads(
                "/project/tsconfig.json",
                [
                    Ok(LEAF.to_owned()),
                    if diagnostic_read_fails {
                        Err(io::Error::new(
                            io::ErrorKind::PermissionDenied,
                            "later read denied",
                        ))
                    } else {
                        Ok(LATER.to_owned())
                    },
                ],
            );
            filesystem.reply_to_reads(
                "/project/base.json",
                [Ok(FIRST_BASE.to_owned()), Ok(SECOND_BASE.to_owned())],
            );
            let program = load_program(&filesystem, canonical);
            let graph = program.project_graph_snapshot();
            let observation = graph.config_resolution_observation.as_ref().unwrap();
            assert!(observation.is_complete());
            let inputs = observation
                .events
                .iter()
                .filter_map(|event| match event {
                    ConfigResolutionEvent::ReadFile {
                        path,
                        kind: ConfigInputKind::Config,
                        result: Ok(text),
                    } => Some((path.as_str(), text.as_str())),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(
                inputs,
                [
                    ("/project/tsconfig.json", LEAF),
                    ("/project/base.json", FIRST_BASE),
                    ("/project/base.json", SECOND_BASE),
                ]
            );
            assert_eq!(
                graph.config.as_ref().unwrap().source_text.as_deref(),
                (!diagnostic_read_fails).then_some(LATER),
            );
            assert!(!graph.options.strict);
            assert_eq!(graph.roots[0].file_name, "/project/main.ts");
            assert_eq!(
                graph
                    .sources
                    .iter()
                    .map(|source| source.file_name.as_str())
                    .collect::<Vec<_>>(),
                ["/project/main.ts"],
            );
            for missing in [
                ProgramGraphMissingEvidence::ConfigSourceText,
                ProgramGraphMissingEvidence::ConfigParseInputs,
                ProgramGraphMissingEvidence::ConfigExtendsInputs,
            ] {
                assert!(!graph.missing_evidence.contains(&missing));
            }
            let reads = filesystem.reads.lock().unwrap().clone();
            assert_eq!(
                reads,
                [
                    "/project/tsconfig.json",
                    "/project/base.json",
                    "/project/base.json",
                    "/project/tsconfig.json",
                    "/project/main.ts",
                ]
            );
            assert_eq!(program.project_graph_snapshot(), graph);
            assert_eq!(*filesystem.reads.lock().unwrap(), reads);
        }
    }
}

#[test]
fn failed_config_loads_keep_complete_observations_without_claiming_a_resolved_config() {
    for canonical in [false, true] {
        for (source, denied) in [(None, false), (Some("!"), false), (Some("{}"), true)] {
            let filesystem = RecordingFileSystem::new();
            if let Some(source) = source {
                filesystem
                    .write_file("/project/tsconfig.json", source)
                    .unwrap();
            }
            if denied {
                filesystem.reply_to_reads(
                    "/project/tsconfig.json",
                    [Err(io::Error::new(
                        io::ErrorKind::PermissionDenied,
                        "denied",
                    ))],
                );
            }
            let program = load_program(&filesystem, canonical);
            let graph = program.project_graph_snapshot();
            assert!(graph.config.is_none());
            assert!(graph.sources.is_empty());
            assert!(!program.diagnostics().is_empty());
            let observation = graph.config_resolution_observation.as_ref().unwrap();
            assert!(observation.is_complete());
            assert!(
                !graph
                    .missing_evidence
                    .contains(&ProgramGraphMissingEvidence::ConfigParseInputs)
            );
            assert!(
                !graph
                    .missing_evidence
                    .contains(&ProgramGraphMissingEvidence::ConfigExtendsInputs)
            );
            assert_eq!(
                graph
                    .missing_evidence
                    .contains(&ProgramGraphMissingEvidence::ConfigSourceText),
                source.is_none() || denied,
            );
            if denied {
                assert_eq!(program.diagnostics()[0].code, Some(5012));
                assert!(observation.events.iter().any(|event| matches!(
                    event,
                    ConfigResolutionEvent::ReadFile { result: Err(error), .. }
                        if error.kind == io::ErrorKind::PermissionDenied && error.message == "denied"
                )));
            }
            let reads = filesystem.reads.lock().unwrap().clone();
            assert_eq!(reads.len(), usize::from(source.is_some()));
            assert_eq!(program.project_graph_snapshot(), graph);
            assert_eq!(*filesystem.reads.lock().unwrap(), reads);
        }
    }
}
