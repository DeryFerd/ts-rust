use std::{
    collections::{BTreeMap, VecDeque},
    io,
    sync::Mutex,
};

use ts_config::{
    ConfigInputKind, ConfigObservationLimits, ConfigResolutionEvent, JsonValue,
    resolve_config_file, resolve_config_file_with_observation,
};
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

#[derive(Clone, Debug, Eq, PartialEq)]
enum FsCall {
    FileExists(String),
    DirectoryExists(String),
    ReadFile(String),
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
    fn new(files: &[(&str, &str)], case_sensitive: bool) -> Self {
        let inner = MemoryFileSystem::new(case_sensitive);
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

fn successful_reads(events: &[ConfigResolutionEvent]) -> Vec<(&str, ConfigInputKind, &str)> {
    events
        .iter()
        .filter_map(|event| match event {
            ConfigResolutionEvent::ReadFile {
                path,
                kind,
                result: Ok(text),
            } => Some((path.as_str(), *kind, text.as_str())),
            _ => None,
        })
        .collect()
}

#[test]
fn observes_inheritance_in_parse_and_merge_order() {
    let leaf = "\u{feff}{\r\n  // leaf\r\n  \"extends\": [\"./first\", \"./second\"],\r\n  \"compilerOptions\": {\"noEmit\": true}\r\n}\r\n";
    let first = r#"{"compilerOptions":{"strict":true,"target":"es2018"}}"#;
    let second = r#"{"compilerOptions":{"target":"es2022"},"files":["second.ts"]}"#;
    let files = [
        ("/repo/tsconfig.json", leaf),
        ("/repo/first.json", first),
        ("/repo/second.json", second),
    ];
    let plain_fs = TestFileSystem::new(&files, true);
    let observed_fs = TestFileSystem::new(&files, true);
    // MemoryFileSystem removes a BOM before returning text.
    for fs in [&plain_fs, &observed_fs] {
        fs.reply_to_reads("/repo/tsconfig.json", [ReadReply::Text(leaf)]);
    }
    let plain = resolve_config_file(&plain_fs, "/repo/./tsconfig.json");
    let observed = resolve_config_file_with_observation(
        &observed_fs,
        "/repo/./tsconfig.json",
        ConfigObservationLimits::default(),
    );

    assert!(plain.is_ok(), "{:?}", plain.diagnostics);
    assert_eq!(observed.result, plain);
    assert_eq!(observed_fs.calls(), plain_fs.calls());
    assert!(observed.observation.is_complete());
    assert_eq!(
        successful_reads(&observed.observation.events),
        [
            ("/repo/tsconfig.json", ConfigInputKind::Config, leaf),
            ("/repo/first.json", ConfigInputKind::Config, first),
            ("/repo/second.json", ConfigInputKind::Config, second),
        ]
    );
    let edges = observed
        .observation
        .events
        .iter()
        .filter_map(|event| match event {
            ConfigResolutionEvent::Extends {
                config_path,
                specifier,
                resolved_path,
            } => Some((
                config_path.as_str(),
                specifier.as_str(),
                resolved_path.as_deref(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        edges,
        [
            ("/repo/tsconfig.json", "./first", Some("/repo/first.json")),
            ("/repo/tsconfig.json", "./second", Some("/repo/second.json")),
        ]
    );
    let config = observed.result.value.unwrap();
    assert_eq!(config.files.unwrap(), ["/repo/second.ts"]);
    assert_eq!(config.compiler_options["strict"], JsonValue::Bool(true));
    assert_eq!(config.compiler_options["noEmit"], JsonValue::Bool(true));
    assert_eq!(config.compiler_options["target"].as_str(), Some("es2022"));
}

#[test]
fn keeps_each_read_when_files_change_without_rereading_for_evidence() {
    const LEAF: &str = r#"{"extends":["./base","./base"]}"#;
    const LATER_LEAF: &str = r#"{"files":["changed.ts"]}"#;
    const FIRST_BASE: &str = r#"{"compilerOptions":{"strict":true}}"#;
    const SECOND_BASE: &str = r#"{"compilerOptions":{"strict":false}}"#;
    let files = [("/repo/tsconfig.json", LEAF), ("/repo/base.json", "{}")];
    let plain_fs = TestFileSystem::new(&files, true);
    let observed_fs = TestFileSystem::new(&files, true);
    for fs in [&plain_fs, &observed_fs] {
        fs.reply_to_reads(
            "/repo/tsconfig.json",
            [ReadReply::Text(LEAF), ReadReply::Text(LATER_LEAF)],
        );
        fs.reply_to_reads(
            "/repo/base.json",
            [ReadReply::Text(FIRST_BASE), ReadReply::Text(SECOND_BASE)],
        );
    }
    let plain = resolve_config_file(&plain_fs, "/repo/tsconfig.json");
    let observed = resolve_config_file_with_observation(
        &observed_fs,
        "/repo/tsconfig.json",
        ConfigObservationLimits::default(),
    );

    assert!(observed.result.is_ok());
    assert_eq!(observed.result, plain);
    assert_eq!(observed_fs.calls(), plain_fs.calls());
    assert_eq!(
        successful_reads(&observed.observation.events),
        [
            ("/repo/tsconfig.json", ConfigInputKind::Config, LEAF),
            ("/repo/base.json", ConfigInputKind::Config, FIRST_BASE),
            ("/repo/base.json", ConfigInputKind::Config, SECOND_BASE),
        ]
    );
    assert_eq!(
        observed.result.value.unwrap().compiler_options["strict"],
        JsonValue::Bool(false)
    );
    assert_eq!(
        observed_fs.read_file("/repo/tsconfig.json").unwrap(),
        LATER_LEAF
    );
}

#[test]
fn observes_cycles_and_missing_extends_without_reading_the_cycle_again() {
    let files = [
        ("/repo/a.json", r#"{"extends":["./b","./missing"]}"#),
        ("/repo/b.json", r#"{"extends":"./a"}"#),
    ];
    let plain_fs = TestFileSystem::new(&files, true);
    let observed_fs = TestFileSystem::new(&files, true);
    let plain = resolve_config_file(&plain_fs, "/repo/a.json");
    let observed = resolve_config_file_with_observation(
        &observed_fs,
        "/repo/a.json",
        ConfigObservationLimits::default(),
    );

    assert_eq!(observed.result, plain);
    assert_eq!(observed_fs.calls(), plain_fs.calls());
    assert_eq!(
        observed
            .result
            .diagnostics
            .iter()
            .map(ts_config::ConfigDiagnostic::code)
            .collect::<Vec<_>>(),
        [18_000, 6_053]
    );
    assert_eq!(successful_reads(&observed.observation.events).len(), 2);
    assert!(observed.observation.is_complete());
    assert!(
        observed
            .observation
            .events
            .contains(&ConfigResolutionEvent::Cycle {
                path: "/repo/a.json".to_owned(),
                chain: ["/repo/a.json", "/repo/b.json", "/repo/a.json"]
                    .map(str::to_owned)
                    .to_vec(),
            })
    );
    let missing = observed
        .observation
        .events
        .iter()
        .position(|event| {
            event
                == &ConfigResolutionEvent::Extends {
                    config_path: "/repo/a.json".to_owned(),
                    specifier: "./missing".to_owned(),
                    resolved_path: None,
                }
        })
        .unwrap();
    assert_eq!(
        &observed.observation.events[missing - 3..missing],
        [
            ConfigResolutionEvent::FileExists {
                path: "/repo/missing".to_owned(),
                exists: false,
            },
            ConfigResolutionEvent::FileExists {
                path: "/repo/missing.json".to_owned(),
                exists: false,
            },
            ConfigResolutionEvent::DirectoryExists {
                path: "/repo/missing".to_owned(),
                exists: false,
            },
        ]
    );
}

#[test]
fn retains_requested_case_when_a_cycle_is_case_insensitive() {
    let files = [("/repo/base.json", r#"{"extends":"./BASE.json"}"#)];
    let plain_fs = TestFileSystem::new(&files, false);
    let observed_fs = TestFileSystem::new(&files, false);
    let plain = resolve_config_file(&plain_fs, "/repo/base.json");
    let observed = resolve_config_file_with_observation(
        &observed_fs,
        "/repo/base.json",
        ConfigObservationLimits::default(),
    );

    assert_eq!(observed.result, plain);
    assert_eq!(observed_fs.calls(), plain_fs.calls());
    assert_eq!(successful_reads(&observed.observation.events).len(), 1);
    assert_eq!(
        observed.observation.events.last(),
        Some(&ConfigResolutionEvent::Cycle {
            path: "/repo/BASE.json".to_owned(),
            chain: vec!["/repo/base.json".to_owned(), "/repo/BASE.json".to_owned()],
        })
    );
}

#[test]
fn observes_package_json_text_before_resolving_its_config_entry() {
    let leaf = r#"{"extends":"preset"}"#;
    let package = "{\n // config entry\n \"tsconfig\": \"configs/base\"\n}\n";
    let base = r#"{"compilerOptions":{"strict":true}}"#;
    let files = [
        ("/repo/app/tsconfig.json", leaf),
        ("/repo/node_modules/preset/package.json", package),
        ("/repo/node_modules/preset/configs/base.json", base),
    ];
    let plain_fs = TestFileSystem::new(&files, true);
    let observed_fs = TestFileSystem::new(&files, true);
    let plain = resolve_config_file(&plain_fs, "/repo/app/tsconfig.json");
    let observed = resolve_config_file_with_observation(
        &observed_fs,
        "/repo/app/tsconfig.json",
        ConfigObservationLimits::default(),
    );

    assert!(plain.is_ok());
    assert_eq!(observed.result, plain);
    assert_eq!(observed_fs.calls(), plain_fs.calls());
    assert_eq!(
        successful_reads(&observed.observation.events),
        [
            ("/repo/app/tsconfig.json", ConfigInputKind::Config, leaf),
            (
                "/repo/node_modules/preset/package.json",
                ConfigInputKind::PackageJson,
                package,
            ),
            (
                "/repo/node_modules/preset/configs/base.json",
                ConfigInputKind::Config,
                base,
            ),
        ]
    );
    let edge = observed
        .observation
        .events
        .iter()
        .position(|event| matches!(event, ConfigResolutionEvent::Extends { .. }))
        .unwrap();
    assert_eq!(
        observed.observation.events[edge],
        ConfigResolutionEvent::Extends {
            config_path: "/repo/app/tsconfig.json".to_owned(),
            specifier: "preset".to_owned(),
            resolved_path: Some("/repo/node_modules/preset/configs/base.json".to_owned()),
        }
    );
    assert!(matches!(
        &observed.observation.events[edge + 1],
        ConfigResolutionEvent::FileExists { path, exists: true }
            if path == "/repo/node_modules/preset/configs/base.json"
    ));
    assert!(matches!(
        &observed.observation.events[edge + 2],
        ConfigResolutionEvent::ReadFile { path, kind: ConfigInputKind::Config, .. }
            if path == "/repo/node_modules/preset/configs/base.json"
    ));
}

#[test]
fn retains_read_errors_without_changing_config_errors_or_package_fallback() {
    let files = [
        ("/repo/tsconfig.json", r#"{"extends":"preset"}"#),
        ("/repo/node_modules/preset/package.json", "{}"),
        ("/repo/node_modules/preset/tsconfig.json", "{}"),
    ];
    for (path, kind) in [
        ("/repo/tsconfig.json", ConfigInputKind::Config),
        (
            "/repo/node_modules/preset/package.json",
            ConfigInputKind::PackageJson,
        ),
    ] {
        let plain_fs = TestFileSystem::new(&files, true);
        let observed_fs = TestFileSystem::new(&files, true);
        for fs in [&plain_fs, &observed_fs] {
            fs.reply_to_reads(
                path,
                [ReadReply::Error(io::ErrorKind::PermissionDenied, "denied")],
            );
        }
        let plain = resolve_config_file(&plain_fs, "/repo/tsconfig.json");
        let observed = resolve_config_file_with_observation(
            &observed_fs,
            "/repo/tsconfig.json",
            ConfigObservationLimits::default(),
        );

        assert_eq!(observed.result, plain);
        assert_eq!(observed_fs.calls(), plain_fs.calls());
        assert!(observed.observation.is_complete());
        assert!(observed.observation.events.iter().any(|event| {
            matches!(event, ConfigResolutionEvent::ReadFile {
                path: actual_path,
                kind: actual_kind,
                result: Err(error),
            } if actual_path == path
                && *actual_kind == kind
                && error.kind == io::ErrorKind::PermissionDenied
                && error.message == "denied")
        }));
        if kind == ConfigInputKind::Config {
            assert!(observed.result.value.is_none());
            assert_eq!(observed.result.diagnostics[0].code(), 5012);
        } else {
            assert!(observed.result.is_ok());
            assert!(successful_reads(&observed.observation.events).iter().any(
                |(path, kind, _)| *path == "/repo/node_modules/preset/tsconfig.json"
                    && *kind == ConfigInputKind::Config
            ));
        }
    }
}

#[test]
fn retains_missing_and_invalid_leaf_inputs_without_extra_reads() {
    for source in [None, Some("[\r\n  1, 2\r\n]\r\n")] {
        let files = source
            .map(|text| vec![("/repo/tsconfig.json", text)])
            .unwrap_or_default();
        let plain_fs = TestFileSystem::new(&files, true);
        let observed_fs = TestFileSystem::new(&files, true);
        let plain = resolve_config_file(&plain_fs, "/repo/tsconfig.json");
        let observed = resolve_config_file_with_observation(
            &observed_fs,
            "/repo/tsconfig.json",
            ConfigObservationLimits::default(),
        );

        assert!(!plain.is_ok());
        assert_eq!(observed.result, plain);
        assert_eq!(observed_fs.calls(), plain_fs.calls());
        assert!(observed.observation.is_complete());
        let expected = source
            .map(|text| vec![("/repo/tsconfig.json", ConfigInputKind::Config, text)])
            .unwrap_or_default();
        assert_eq!(successful_reads(&observed.observation.events), expected);
        if source.is_none() {
            assert_eq!(
                observed.observation.events,
                [ConfigResolutionEvent::FileExists {
                    path: "/repo/tsconfig.json".to_owned(),
                    exists: false,
                }]
            );
        }
    }
}

#[test]
fn limits_retain_whole_prefix_events_without_changing_resolution() {
    let leaf = "{\"extends\":\"./base\",\"note\":\"\u{00e9}\"}";
    let path = "/repo/tsconfig.json";
    let files = [(path, leaf), ("/repo/base.json", "{}")];
    let unlimited_fs = TestFileSystem::new(&files, true);
    let unlimited = resolve_config_file_with_observation(
        &unlimited_fs,
        path,
        ConfigObservationLimits::default(),
    );
    assert!(unlimited.observation.is_complete());
    let first_read_bytes = path.len() * 2 + leaf.len();
    for (limits, retained) in [
        (
            ConfigObservationLimits {
                max_events: 0,
                max_string_bytes: usize::MAX,
            },
            0,
        ),
        (
            ConfigObservationLimits {
                max_events: 2,
                max_string_bytes: usize::MAX,
            },
            2,
        ),
        (
            ConfigObservationLimits {
                max_events: usize::MAX,
                max_string_bytes: first_read_bytes - 1,
            },
            1,
        ),
        (
            ConfigObservationLimits {
                max_events: usize::MAX,
                max_string_bytes: first_read_bytes,
            },
            2,
        ),
    ] {
        let limited_fs = TestFileSystem::new(&files, true);
        let limited = resolve_config_file_with_observation(&limited_fs, path, limits);
        assert_eq!(limited.result, unlimited.result);
        assert_eq!(limited_fs.calls(), unlimited_fs.calls());
        assert!(!limited.observation.is_complete());
        assert_eq!(
            limited.observation.events,
            unlimited.observation.events[..retained]
        );
        assert_eq!(
            limited.observation.omitted_events,
            unlimited.observation.events.len() - retained
        );
    }
}
