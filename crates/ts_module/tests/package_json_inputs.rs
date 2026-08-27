use std::{
    collections::{BTreeMap, VecDeque},
    io,
    sync::{Arc, Mutex},
};

use ts_module::{
    FailedLookupKind, ModuleFormat, PackageJsonInputEvent, PackageJsonInputLimits,
    PackageJsonInputPurpose, ResolutionMode, ResolutionOptions, ResolutionResult, Resolver,
};
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

#[derive(Clone, Debug, Eq, PartialEq)]
enum FsCall {
    FileExists(String),
    DirectoryExists(String),
    ReadFile(String),
    Realpath(String),
}

enum ReadReply {
    Text(&'static str),
    Error(io::ErrorKind, &'static str),
}

#[derive(Default)]
struct FsState {
    calls: Vec<FsCall>,
    replies: BTreeMap<String, VecDeque<ReadReply>>,
}

struct TestFileSystem {
    inner: MemoryFileSystem,
    state: Mutex<FsState>,
}

impl TestFileSystem {
    fn new(files: &[(&str, &str)]) -> Self {
        let inner = MemoryFileSystem::new(true);
        for &(path, text) in files {
            inner.write_file(path, text).unwrap();
        }
        Self {
            inner,
            state: Mutex::default(),
        }
    }

    fn reply_to_reads(&self, path: &str, replies: impl IntoIterator<Item = ReadReply>) {
        self.state
            .lock()
            .unwrap()
            .replies
            .insert(path.to_owned(), replies.into_iter().collect());
    }

    fn calls(&self) -> Vec<FsCall> {
        self.state.lock().unwrap().calls.clone()
    }
}

impl FileSystem for TestFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.inner.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.state
            .lock()
            .unwrap()
            .calls
            .push(FsCall::FileExists(path.to_owned()));
        self.inner.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.state
            .lock()
            .unwrap()
            .calls
            .push(FsCall::DirectoryExists(path.to_owned()));
        self.inner.directory_exists(path)
    }

    fn realpath(&self, path: &str) -> String {
        self.state
            .lock()
            .unwrap()
            .calls
            .push(FsCall::Realpath(path.to_owned()));
        self.inner.realpath(path)
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.inner.modified_time(path)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        let reply = {
            let mut state = self.state.lock().unwrap();
            state.calls.push(FsCall::ReadFile(path.to_owned()));
            state.replies.get_mut(path).and_then(VecDeque::pop_front)
        };
        match reply {
            Some(ReadReply::Text(text)) => Ok(text.to_owned()),
            Some(ReadReply::Error(kind, message)) => Err(io::Error::new(kind, message)),
            None => self.inner.read_file(path),
        }
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        self.inner.write_file(path, contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        self.inner.read_directory(path)
    }
}

fn successful_reads(
    events: &[PackageJsonInputEvent],
) -> Vec<(&str, PackageJsonInputPurpose, &str)> {
    events
        .iter()
        .filter_map(|event| match event {
            PackageJsonInputEvent::ReadFile {
                path,
                purpose,
                result: Ok(text),
            } => Some((path.as_str(), *purpose, text.as_str())),
            _ => None,
        })
        .collect()
}

#[test]
fn default_mode_records_direct_reads_without_new_existence_probes() {
    let package = "{\r\n  \"type\": \"module\"\r\n}\r\n";
    let fs = TestFileSystem::new(&[("/app/package.json", package), ("/app/src/value.ts", "")]);
    let resolver = Resolver::new(
        &fs,
        ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        },
    );
    let result = resolver.resolve("./value.js", "/app/src/main.ts");

    assert_eq!(result.effective_mode, Some(ModuleFormat::Esm));
    assert_eq!(
        result.resolved.unwrap().original_file_name,
        "/app/src/value.ts"
    );
    assert!(result.failed_lookups.is_empty());
    let inputs = result.package_json_inputs.unwrap();
    assert!(inputs.is_complete());
    assert_eq!(inputs.events.len(), 2);
    assert!(matches!(
        &inputs.events[0],
        PackageJsonInputEvent::ReadFile {
            path,
            purpose: PackageJsonInputPurpose::DefaultMode,
            result: Err(error),
        } if path == "/app/src/package.json" && error.kind == io::ErrorKind::NotFound
    ));
    assert_eq!(
        successful_reads(&inputs.events),
        [(
            "/app/package.json",
            PackageJsonInputPurpose::DefaultMode,
            package
        )]
    );
    assert_eq!(
        fs.calls(),
        [
            FsCall::ReadFile("/app/src/package.json".to_owned()),
            FsCall::ReadFile("/app/package.json".to_owned()),
            FsCall::FileExists("/app/src/value.ts".to_owned()),
        ]
    );
}

#[test]
fn keeps_each_package_read_when_text_changes_within_one_resolution() {
    const PACKAGE_PATH: &str = "/app/node_modules/pkg/package.json";
    const FIRST: &str = r#"{"types":"first.d.ts"}"#;
    const SECOND: &str = r#"{"types":"second.d.ts"}"#;
    let files = [
        (PACKAGE_PATH, "{}"),
        ("/app/node_modules/pkg/first.d.ts", ""),
        ("/app/node_modules/pkg/second.d.ts", ""),
    ];
    let observed_fs = TestFileSystem::new(&files);
    let limited_fs = TestFileSystem::new(&files);
    for fs in [&observed_fs, &limited_fs] {
        fs.reply_to_reads(
            PACKAGE_PATH,
            [ReadReply::Text(FIRST), ReadReply::Text(SECOND)],
        );
    }
    let observed =
        Resolver::new(&observed_fs, ResolutionOptions::default()).resolve("pkg", "/app/main.ts");
    let limited = Resolver::new_with_package_json_input_limits(
        &limited_fs,
        ResolutionOptions::default(),
        PackageJsonInputLimits {
            max_events: 0,
            max_string_bytes: 0,
        },
    )
    .resolve("pkg", "/app/main.ts");

    assert_eq!(observed.resolved, limited.resolved);
    assert_eq!(observed.failed_lookups, limited.failed_lookups);
    assert_eq!(observed.effective_mode, limited.effective_mode);
    assert_eq!(observed_fs.calls(), limited_fs.calls());
    assert_eq!(
        observed.resolved.unwrap().original_file_name,
        "/app/node_modules/pkg/second.d.ts"
    );
    let inputs = observed.package_json_inputs.unwrap();
    assert!(inputs.is_complete());
    assert_eq!(
        inputs.events.as_ref(),
        [
            PackageJsonInputEvent::FileExists {
                path: PACKAGE_PATH.to_owned(),
                exists: true
            },
            PackageJsonInputEvent::FileExists {
                path: PACKAGE_PATH.to_owned(),
                exists: true
            },
            PackageJsonInputEvent::ReadFile {
                path: PACKAGE_PATH.to_owned(),
                purpose: PackageJsonInputPurpose::PackageResolution,
                result: Ok(FIRST.to_owned()),
            },
            PackageJsonInputEvent::FileExists {
                path: PACKAGE_PATH.to_owned(),
                exists: true
            },
            PackageJsonInputEvent::ReadFile {
                path: PACKAGE_PATH.to_owned(),
                purpose: PackageJsonInputPurpose::PackageResolution,
                result: Ok(SECOND.to_owned()),
            },
        ]
    );
    let limited_inputs = limited.package_json_inputs.unwrap();
    assert!(limited_inputs.events.is_empty());
    assert!(!limited_inputs.is_complete());
    assert_eq!(limited_inputs.omitted_events, inputs.events.len());
}

#[test]
fn cache_hits_share_original_inputs_and_keep_explicit_mode_keys_separate() {
    let first_package = r#"{"exports":{".":{"import":"./first.d.mts","require":"./first.d.cts"}}}"#;
    let second_package =
        r#"{"exports":{".":{"import":"./second.d.mts","require":"./second.d.cts"}}}"#;
    let fs = TestFileSystem::new(&[
        ("/app/package.json", r#"{"name":"app","type":"module"}"#),
        ("/app/node_modules/pkg/package.json", first_package),
        ("/app/node_modules/pkg/first.d.mts", ""),
        ("/app/node_modules/pkg/first.d.cts", ""),
        ("/app/node_modules/pkg/second.d.mts", ""),
        ("/app/node_modules/pkg/second.d.cts", ""),
    ]);
    let resolver = Resolver::new(
        &fs,
        ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        },
    );
    let first = resolver.resolve("pkg", "/app/main.ts");
    let first_calls = fs.calls();
    fs.write_file("/app/package.json", r#"{"name":"app","type":"commonjs"}"#)
        .unwrap();
    fs.write_file("/app/node_modules/pkg/package.json", second_package)
        .unwrap();

    let cached = resolver.resolve("pkg", "/app/main.ts");
    assert_eq!(cached, first);
    assert_eq!(fs.calls(), first_calls);
    assert!(Arc::ptr_eq(
        &cached.package_json_inputs.as_ref().unwrap().events,
        &first.package_json_inputs.as_ref().unwrap().events,
    ));
    for (mode, target) in [
        (ModuleFormat::CommonJs, "/app/node_modules/pkg/second.d.cts"),
        (ModuleFormat::Esm, "/app/node_modules/pkg/second.d.mts"),
    ] {
        let explicit = resolver.resolve_with_mode("pkg", "/app/main.ts", mode);
        assert_eq!(explicit.effective_mode, Some(mode));
        assert_eq!(
            explicit.resolved.as_ref().unwrap().original_file_name,
            target
        );
        let inputs = explicit.package_json_inputs.as_ref().unwrap();
        assert!(inputs.is_complete());
        assert!(inputs.events.iter().all(|event| !matches!(
            event,
            PackageJsonInputEvent::ReadFile {
                purpose: PackageJsonInputPurpose::DefaultMode,
                ..
            }
        )));
        assert!(
            successful_reads(&inputs.events)
                .iter()
                .any(|(path, _, text)| {
                    *path == "/app/node_modules/pkg/package.json" && *text == second_package
                })
        );
        let calls = fs.calls();
        assert_eq!(
            resolver.resolve_with_mode("pkg", "/app/main.ts", mode),
            explicit
        );
        assert_eq!(fs.calls(), calls);
    }
    assert_eq!(resolver.resolve("pkg", "/app/main.ts"), first);
    resolver.clear_cache();
    let fresh = resolver.resolve("pkg", "/app/main.ts");
    assert_eq!(fresh.effective_mode, Some(ModuleFormat::CommonJs));
    assert_eq!(
        fresh.resolved.unwrap().original_file_name,
        "/app/node_modules/pkg/second.d.cts"
    );
    assert!(
        successful_reads(&first.package_json_inputs.unwrap().events)
            .iter()
            .any(
                |(path, _, text)| *path == "/app/node_modules/pkg/package.json"
                    && *text == first_package
            )
    );
    assert!(
        successful_reads(&fresh.package_json_inputs.unwrap().events)
            .iter()
            .any(
                |(path, _, text)| *path == "/app/node_modules/pkg/package.json"
                    && *text == second_package
            )
    );
}

#[test]
fn keeps_read_errors_and_malformed_text_without_changing_index_fallback() {
    const PATH: &str = "/app/node_modules/pkg/package.json";
    const MALFORMED: &str = "{\"types\":";
    let fs = TestFileSystem::new(&[(PATH, "{}"), ("/app/node_modules/pkg/index.d.ts", "")]);
    fs.reply_to_reads(
        PATH,
        [
            ReadReply::Error(io::ErrorKind::PermissionDenied, "denied"),
            ReadReply::Text(MALFORMED),
        ],
    );
    let result = Resolver::new(&fs, ResolutionOptions::default()).resolve("pkg", "/app/main.ts");

    assert_eq!(
        result.resolved.unwrap().original_file_name,
        "/app/node_modules/pkg/index.d.ts"
    );
    assert!(
        !result
            .failed_lookups
            .iter()
            .any(|lookup| { lookup.kind == FailedLookupKind::PackageJson && lookup.path == PATH })
    );
    let inputs = result.package_json_inputs.unwrap();
    assert!(inputs.is_complete());
    assert!(inputs.events.iter().any(|event| matches!(event,
        PackageJsonInputEvent::ReadFile { path, result: Err(error), .. }
            if path == PATH && error.kind == io::ErrorKind::PermissionDenied && error.message == "denied"
    )));
    assert_eq!(
        successful_reads(&inputs.events),
        [(PATH, PackageJsonInputPurpose::PackageResolution, MALFORMED),]
    );
    assert_eq!(
        fs.calls()
            .iter()
            .filter(|call| matches!(call, FsCall::ReadFile(path) if path == PATH))
            .count(),
        2
    );
}

#[test]
fn missing_package_probes_do_not_add_reads_or_new_failed_lookups() {
    let path = "/app/node_modules/pkg/package.json";
    let fs = TestFileSystem::new(&[("/app/node_modules/pkg/index.d.ts", "")]);
    let result = Resolver::new(&fs, ResolutionOptions::default()).resolve("pkg", "/app/main.ts");

    assert_eq!(
        result.resolved.unwrap().original_file_name,
        "/app/node_modules/pkg/index.d.ts"
    );
    assert_eq!(
        result
            .failed_lookups
            .iter()
            .filter(|lookup| {
                lookup.kind == FailedLookupKind::PackageJson && lookup.path == path
            })
            .count(),
        1
    );
    assert_eq!(
        result.package_json_inputs.unwrap().events.as_ref(),
        [
            PackageJsonInputEvent::FileExists {
                path: path.to_owned(),
                exists: false
            },
            PackageJsonInputEvent::FileExists {
                path: path.to_owned(),
                exists: false
            },
        ]
    );
    assert!(
        fs.calls()
            .iter()
            .all(|call| !matches!(call, FsCall::ReadFile(_)))
    );
}

#[test]
fn nested_package_probes_do_not_read_metadata_skipped_by_exports() {
    let package_path = "/app/node_modules/pkg/package.json";
    let nested_path = "/app/node_modules/pkg/sub/package.json";
    let package = r#"{"exports":{"./sub":"./selected.d.ts"}}"#;
    let fs = TestFileSystem::new(&[
        (package_path, package),
        (nested_path, r#"{"types":"ignored.d.ts"}"#),
        ("/app/node_modules/pkg/selected.d.ts", ""),
        ("/app/node_modules/pkg/sub/ignored.d.ts", ""),
    ]);
    let result = Resolver::new(
        &fs,
        ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        },
    )
    .resolve_with_mode("pkg/sub", "/app/main.cts", ModuleFormat::CommonJs);

    assert_eq!(
        result.resolved.unwrap().original_file_name,
        "/app/node_modules/pkg/selected.d.ts"
    );
    let inputs = result.package_json_inputs.unwrap();
    let nested = inputs
        .events
        .iter()
        .position(|event| {
            matches!(event,
                PackageJsonInputEvent::FileExists { path, exists: true } if path == nested_path
            )
        })
        .unwrap();
    assert_eq!(
        &inputs.events[nested + 1],
        &PackageJsonInputEvent::FileExists {
            path: package_path.to_owned(),
            exists: true,
        }
    );
    assert!(matches!(&inputs.events[nested + 2],
        PackageJsonInputEvent::ReadFile { path, result: Ok(text), .. }
            if path == package_path && text == package
    ));
    assert!(fs.calls().iter().all(|call| !matches!(call,
        FsCall::ReadFile(path) if path == nested_path
    )));
}

#[test]
fn type_reference_operations_keep_fresh_inputs_without_adding_a_cache() {
    let path = "/types/pkg/package.json";
    let first_package = r#"{"types":"first.d.ts"}"#;
    let second_package = r#"{"types":"second.d.ts"}"#;
    let fs = TestFileSystem::new(&[
        (path, first_package),
        ("/types/pkg/first.d.ts", ""),
        ("/types/pkg/second.d.ts", ""),
    ]);
    let resolver = Resolver::new(
        &fs,
        ResolutionOptions {
            type_roots: Some(vec!["/types".to_owned()]),
            ..ResolutionOptions::default()
        },
    );
    let first = resolver.resolve_type_reference("pkg", "/app/main.ts");
    let calls = fs.calls();
    fs.write_file(path, second_package).unwrap();
    let second = resolver.resolve_type_reference("pkg", "/app/main.ts");

    assert_eq!(
        first.resolved.unwrap().original_file_name,
        "/types/pkg/first.d.ts"
    );
    assert_eq!(
        second.resolved.unwrap().original_file_name,
        "/types/pkg/second.d.ts"
    );
    assert!(fs.calls().len() > calls.len());
    assert_eq!(
        successful_reads(&first.package_json_inputs.unwrap().events),
        [(
            path,
            PackageJsonInputPurpose::PackageResolution,
            first_package
        ),]
    );
    assert_eq!(
        successful_reads(&second.package_json_inputs.unwrap().events),
        [(
            path,
            PackageJsonInputPurpose::PackageResolution,
            second_package
        ),]
    );
}

#[test]
fn limits_keep_complete_prefix_events_without_changing_calls_or_resolution() {
    let package = "{\"types\":\"index.d.ts\",\"note\":\"\u{00e9}\"}";
    let path = "/app/node_modules/pkg/package.json";
    let files = [(path, package), ("/app/node_modules/pkg/index.d.ts", "")];
    let full_fs = TestFileSystem::new(&files);
    let full = Resolver::new(&full_fs, ResolutionOptions::default()).resolve("pkg", "/app/main.ts");
    let full_inputs = full.package_json_inputs.as_ref().unwrap();
    assert!(full_inputs.is_complete());
    let first_read_bytes = path.len() * 3 + package.len();
    for (limits, retained) in [
        (
            PackageJsonInputLimits {
                max_events: 0,
                max_string_bytes: usize::MAX,
            },
            0,
        ),
        (
            PackageJsonInputLimits {
                max_events: 2,
                max_string_bytes: usize::MAX,
            },
            2,
        ),
        (
            PackageJsonInputLimits {
                max_events: usize::MAX,
                max_string_bytes: first_read_bytes - 1,
            },
            2,
        ),
        (
            PackageJsonInputLimits {
                max_events: usize::MAX,
                max_string_bytes: first_read_bytes,
            },
            3,
        ),
    ] {
        let limited_fs = TestFileSystem::new(&files);
        let limited = Resolver::new_with_package_json_input_limits(
            &limited_fs,
            ResolutionOptions::default(),
            limits,
        )
        .resolve("pkg", "/app/main.ts");
        assert_eq!(limited.resolved, full.resolved);
        assert_eq!(limited.failed_lookups, full.failed_lookups);
        assert_eq!(limited.effective_mode, full.effective_mode);
        assert_eq!(limited_fs.calls(), full_fs.calls());
        let inputs = limited.package_json_inputs.unwrap();
        assert!(!inputs.is_complete());
        assert_eq!(inputs.events.as_ref(), &full_inputs.events[..retained]);
        assert_eq!(inputs.omitted_events, full_inputs.events.len() - retained);
    }
}

#[test]
fn empty_worker_inputs_are_distinct_from_missing_synthetic_evidence() {
    assert!(ResolutionResult::default().package_json_inputs.is_none());
    let fs = TestFileSystem::new(&[("/app/value.ts", "")]);
    let result =
        Resolver::new(&fs, ResolutionOptions::default()).resolve("./value", "/app/main.ts");
    let inputs = result.package_json_inputs.unwrap();

    assert!(inputs.is_complete());
    assert!(inputs.events.is_empty());
    assert_eq!(
        fs.calls(),
        [
            FsCall::FileExists("/app/value.ts".to_owned()),
            FsCall::Realpath("/app/value.ts".to_owned()),
        ]
    );
}
