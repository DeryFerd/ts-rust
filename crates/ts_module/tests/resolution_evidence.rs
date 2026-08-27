use std::{
    io,
    sync::{
        Mutex,
        atomic::{AtomicUsize, Ordering},
    },
};

use ts_module::{
    FailedLookupKind, ModuleFormat, ResolutionMode, ResolutionOptions, ResolutionResult, Resolver,
};
use ts_path::FileExtension;
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

enum RealpathReply {
    FileSystem,
    Input,
    Fixed(String),
}

struct ObservedFileSystem {
    files: MemoryFileSystem,
    calls: AtomicUsize,
    realpaths: Mutex<Vec<(String, String)>>,
    realpath_reply: RealpathReply,
}

impl ObservedFileSystem {
    fn new(entries: &[(&str, &str)]) -> Self {
        Self::with_case_sensitivity(entries, true)
    }

    fn with_case_sensitivity(entries: &[(&str, &str)], case_sensitive: bool) -> Self {
        let files = MemoryFileSystem::new(case_sensitive);
        for (path, contents) in entries {
            files.write_file(path, contents).unwrap();
        }
        Self {
            files,
            calls: AtomicUsize::new(0),
            realpaths: Mutex::new(Vec::new()),
            realpath_reply: RealpathReply::FileSystem,
        }
    }
}

impl FileSystem for ObservedFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.files.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.files.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.files.directory_exists(path)
    }

    fn realpath(&self, path: &str) -> String {
        self.calls.fetch_add(1, Ordering::Relaxed);
        let result = match &self.realpath_reply {
            RealpathReply::FileSystem => self.files.realpath(path),
            RealpathReply::Input => path.to_owned(),
            RealpathReply::Fixed(result) => result.clone(),
        };
        self.realpaths
            .lock()
            .unwrap()
            .push((path.to_owned(), result.clone()));
        result
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.files.modified_time(path)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.files.read_file(path)
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        self.files.write_file(path, contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.files.read_directory(path)
    }
}

fn conditional_package() -> ObservedFileSystem {
    let filesystem = ObservedFileSystem::new(&[
        ("/app/package.json", r#"{"type":"module"}"#),
        (
            "/packages/pkg/package.json",
            r#"{"name":"pkg","exports":{".":{"import":"./esm.d.mts","require":"./commonjs.d.cts"}}}"#,
        ),
        ("/packages/pkg/esm.d.mts", ""),
        ("/packages/pkg/commonjs.d.cts", ""),
    ]);
    filesystem
        .files
        .add_directory_link("/packages/pkg", "/app/node_modules/pkg");
    filesystem
}

#[test]
fn resolution_evidence_retains_relative_candidates_without_realpath() {
    let filesystem = ObservedFileSystem::new(&[("/real/pkg/entry.ios.d.ts", "")]);
    filesystem
        .files
        .add_directory_link("/real/pkg", "/app/node_modules/pkg");
    let resolver = Resolver::new(
        &filesystem,
        ResolutionOptions {
            module_suffixes: vec![".android".to_owned(), ".ios".to_owned()],
            ..ResolutionOptions::default()
        },
    );
    let result = resolver.resolve("./node_modules/pkg/entry.js", "/app/main.ts");
    assert_eq!(result.effective_mode, Some(ModuleFormat::CommonJs));
    let entry = result.resolved.unwrap();
    assert_eq!(
        entry.original_file_name,
        "/app/node_modules/pkg/entry.ios.d.ts"
    );
    assert_eq!(
        entry.resolved_file_name,
        "/app/node_modules/pkg/entry.ios.d.ts"
    );
    assert!(entry.is_external_library_import);
    assert!(filesystem.realpaths.lock().unwrap().is_empty());
    assert_eq!(
        result
            .failed_lookups
            .iter()
            .map(|lookup| (lookup.kind, lookup.path.as_str()))
            .collect::<Vec<_>>(),
        [
            (
                FailedLookupKind::File,
                "/app/node_modules/pkg/entry.android.ts"
            ),
            (FailedLookupKind::File, "/app/node_modules/pkg/entry.ios.ts"),
            (
                FailedLookupKind::File,
                "/app/node_modules/pkg/entry.android.tsx"
            ),
            (
                FailedLookupKind::File,
                "/app/node_modules/pkg/entry.ios.tsx"
            ),
            (
                FailedLookupKind::File,
                "/app/node_modules/pkg/entry.android.d.ts"
            ),
        ]
    );
}

#[test]
fn resolution_evidence_records_unchanged_realpath_results() {
    for (return_input, specifier, candidate) in [
        (false, "direct", "/app/node_modules/direct/index.d.ts"),
        (true, "alias", "/app/node_modules/alias/index.d.ts"),
    ] {
        let mut filesystem = ObservedFileSystem::new(&[
            ("/app/node_modules/direct/index.d.ts", ""),
            ("/real/entry.d.ts", ""),
        ]);
        filesystem
            .files
            .add_file_link("/real/entry.d.ts", "/app/node_modules/alias/index.d.ts");
        if return_input {
            filesystem.realpath_reply = RealpathReply::Input;
        }
        let resolver = Resolver::new(&filesystem, ResolutionOptions::default());
        let entry = resolver
            .resolve(specifier, "/app/main.ts")
            .resolved
            .unwrap();
        assert_eq!(entry.original_file_name, candidate);
        assert_eq!(entry.resolved_file_name, candidate);
        assert_eq!(
            *filesystem.realpaths.lock().unwrap(),
            [(candidate.to_owned(), candidate.to_owned())]
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep lookup kinds beside their expected realpath policy.
fn symlink_rules_distinguish_relative_package_and_mapped_modules() {
    for preserve_symlinks in [false, true] {
        for (specifier, candidate, realpath, external, eligible) in [
            ("./local", "/app/local.ts", "/real/local.ts", false, false),
            (
                "./node_modules/pkg/index",
                "/app/node_modules/pkg/index.d.ts",
                "/real/pkg/index.d.ts",
                true,
                false,
            ),
            (
                "/app/node_modules/pkg/index.d.ts",
                "/app/node_modules/pkg/index.d.ts",
                "/real/pkg/index.d.ts",
                true,
                false,
            ),
            (
                "pkg",
                "/app/node_modules/pkg/index.d.ts",
                "/real/pkg/index.d.ts",
                true,
                true,
            ),
            (
                "mapped",
                "/app/node_modules/pkg/index.d.ts",
                "/real/pkg/index.d.ts",
                true,
                true,
            ),
            (
                "asset://pkg",
                "/app/node_modules/pkg/index.d.ts",
                "/real/pkg/index.d.ts",
                true,
                true,
            ),
            (
                "local-mapped",
                "/app/local.ts",
                "/real/local.ts",
                false,
                false,
            ),
        ] {
            let filesystem =
                ObservedFileSystem::new(&[("/real/local.ts", ""), ("/real/pkg/index.d.ts", "")]);
            filesystem
                .files
                .add_file_link("/real/local.ts", "/app/local.ts");
            filesystem
                .files
                .add_directory_link("/real/pkg", "/app/node_modules/pkg");
            let resolver = Resolver::new(
                &filesystem,
                ResolutionOptions {
                    mode: ResolutionMode::Bundler,
                    preserve_symlinks,
                    base_url: Some("/app".to_owned()),
                    paths: std::collections::BTreeMap::from([
                        (
                            "mapped".to_owned(),
                            vec!["node_modules/pkg/index.d.ts".to_owned()],
                        ),
                        (
                            "asset://pkg".to_owned(),
                            vec!["node_modules/pkg/index.d.ts".to_owned()],
                        ),
                        ("local-mapped".to_owned(), vec!["local.ts".to_owned()]),
                    ]),
                    ..ResolutionOptions::default()
                },
            );
            let result = resolver.resolve(specifier, "/app/main.ts");
            assert_eq!(result.effective_mode, Some(ModuleFormat::Esm));
            let entry = result.resolved.as_ref().unwrap();
            let follows = eligible && !preserve_symlinks;
            assert_eq!(entry.original_file_name, candidate);
            assert_eq!(
                entry.resolved_file_name,
                if follows { realpath } else { candidate }
            );
            assert_eq!(entry.is_external_library_import, external);
            let expected = if follows {
                vec![(candidate.to_owned(), realpath.to_owned())]
            } else {
                Vec::new()
            };
            assert_eq!(
                *filesystem.realpaths.lock().unwrap(),
                expected,
                "{specifier}"
            );
            let calls = filesystem.calls.load(Ordering::Relaxed);
            assert_eq!(resolver.resolve(specifier, "/app/main.ts"), result);
            assert_eq!(filesystem.calls.load(Ordering::Relaxed), calls);
        }
    }
}

#[test]
fn symlink_rules_keep_type_directives_distinct_outside_node_modules() {
    for preserve_symlinks in [false, true] {
        let filesystem = ObservedFileSystem::new(&[("/real/types/index.d.ts", "")]);
        filesystem
            .files
            .add_directory_link("/real/types", "/types/pkg");
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                preserve_symlinks,
                type_roots: Some(vec!["/types".to_owned()]),
                ..ResolutionOptions::default()
            },
        );
        let module = resolver.resolve("pkg", "/app/main.ts");
        assert_eq!(module.effective_mode, Some(ModuleFormat::Esm));
        let module = module.resolved.unwrap();
        assert_eq!(module.original_file_name, "/types/pkg/index.d.ts");
        assert_eq!(module.resolved_file_name, "/types/pkg/index.d.ts");
        assert!(!module.is_external_library_import);
        assert!(filesystem.realpaths.lock().unwrap().is_empty());

        let directive = resolver.resolve_type_reference("pkg", "/app/main.ts");
        assert_eq!(directive.effective_mode, Some(ModuleFormat::Esm));
        let directive = directive.resolved.unwrap();
        assert_eq!(directive.original_file_name, "/types/pkg/index.d.ts");
        assert_eq!(
            directive.resolved_file_name,
            if preserve_symlinks {
                "/types/pkg/index.d.ts"
            } else {
                "/real/types/index.d.ts"
            }
        );
        assert!(!directive.is_external_library_import);
        let expected = if preserve_symlinks {
            Vec::new()
        } else {
            vec![(
                "/types/pkg/index.d.ts".to_owned(),
                "/real/types/index.d.ts".to_owned(),
            )]
        };
        assert_eq!(*filesystem.realpaths.lock().unwrap(), expected);
    }
}

#[test]
fn symlink_rules_preserve_lookup_spelling_for_case_equivalent_results() {
    let candidate = "/app/node_modules/pkg/index.d.ts";
    let returned = "/APP/NODE_MODULES/PKG/index.d.ts";
    for case_sensitive in [false, true] {
        let mut filesystem =
            ObservedFileSystem::with_case_sensitivity(&[(candidate, "")], case_sensitive);
        filesystem.realpath_reply = RealpathReply::Fixed(returned.to_owned());
        let resolver = Resolver::new(&filesystem, ResolutionOptions::default());
        let result = resolver.resolve("pkg", "/app/main.ts").resolved.unwrap();
        assert_eq!(result.original_file_name, candidate);
        assert_eq!(
            result.resolved_file_name,
            if case_sensitive { returned } else { candidate }
        );
        assert_eq!(
            *filesystem.realpaths.lock().unwrap(),
            [(candidate.to_owned(), returned.to_owned())]
        );
    }
}

#[test]
fn symlink_rules_compare_drive_roots_without_case_sensitivity() {
    let candidate = "c:/app/node_modules/pkg/index.d.ts";
    let returned = "C:/app/node_modules/pkg/index.d.ts";
    let mut filesystem = ObservedFileSystem::new(&[(candidate, "")]);
    filesystem.realpath_reply = RealpathReply::Fixed(returned.to_owned());
    let resolver = Resolver::new(&filesystem, ResolutionOptions::default());
    let result = resolver.resolve("pkg", "c:/app/main.ts").resolved.unwrap();
    assert_eq!(result.original_file_name, candidate);
    assert_eq!(result.resolved_file_name, candidate);
    assert_eq!(
        *filesystem.realpaths.lock().unwrap(),
        [(candidate.to_owned(), returned.to_owned())]
    );
}

#[test]
fn symlink_rules_use_go_character_case_comparison() {
    let candidate = "/app/node_modules/pkg/\u{0130}tem.d.ts";
    let returned = "/app/node_modules/pkg/item.d.ts";
    let mut filesystem = ObservedFileSystem::with_case_sensitivity(
        &[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"types":"\u0130tem.d.ts"}"#,
            ),
            (candidate, ""),
        ],
        false,
    );
    filesystem.realpath_reply = RealpathReply::Fixed(returned.to_owned());
    let resolver = Resolver::new(&filesystem, ResolutionOptions::default());
    let result = resolver.resolve("pkg", "/app/main.ts").resolved.unwrap();
    assert_eq!(result.original_file_name, candidate);
    assert_eq!(result.resolved_file_name, candidate);
    assert_eq!(
        *filesystem.realpaths.lock().unwrap(),
        [(candidate.to_owned(), returned.to_owned())]
    );
}

#[test]
fn symlink_rules_normalize_returned_paths_and_keep_candidate_extension() {
    let candidate = "/app/node_modules/pkg/index.d.ts";
    let returned = "/real/./temporary/../entry.js";
    let mut filesystem = ObservedFileSystem::new(&[(candidate, "")]);
    filesystem.realpath_reply = RealpathReply::Fixed(returned.to_owned());
    let resolver = Resolver::new(&filesystem, ResolutionOptions::default());
    let result = resolver.resolve("pkg", "/app/main.ts").resolved.unwrap();
    assert_eq!(result.original_file_name, candidate);
    assert_eq!(result.resolved_file_name, "/real/entry.js");
    assert_eq!(result.extension, Some(FileExtension::Dts));
    assert_eq!(
        *filesystem.realpaths.lock().unwrap(),
        [(candidate.to_owned(), returned.to_owned())]
    );
}

#[test]
fn resolution_evidence_retains_default_modes_for_unresolved_attempts() {
    let filesystem = ObservedFileSystem::new(&[
        ("/app/package.json", r#"{"type":"module"}"#),
        ("/app/nested/package.json", r#"{"type":"commonjs"}"#),
    ]);
    for (mode, containing_file, expected) in [
        (
            ResolutionMode::Classic,
            "/app/main.ts",
            ModuleFormat::CommonJs,
        ),
        (
            ResolutionMode::Node10,
            "/app/main.mts",
            ModuleFormat::CommonJs,
        ),
        (ResolutionMode::Bundler, "/app/main.cts", ModuleFormat::Esm),
        (ResolutionMode::Node16, "/app/main.mts", ModuleFormat::Esm),
        (
            ResolutionMode::Node16,
            "/app/main.cts",
            ModuleFormat::CommonJs,
        ),
        (ResolutionMode::Node16, "/app/main.ts", ModuleFormat::Esm),
        (
            ResolutionMode::Node16,
            "/app/nested/main.ts",
            ModuleFormat::CommonJs,
        ),
        (
            ResolutionMode::NodeNext,
            "/app/main.d.mts",
            ModuleFormat::Esm,
        ),
        (
            ResolutionMode::NodeNext,
            "/app/main.d.cts",
            ModuleFormat::CommonJs,
        ),
        (ResolutionMode::NodeNext, "/app/main.ts", ModuleFormat::Esm),
        (
            ResolutionMode::NodeNext,
            "/app/nested/main.ts",
            ModuleFormat::CommonJs,
        ),
    ] {
        let resolver = Resolver::new(
            &filesystem,
            ResolutionOptions {
                mode,
                ..ResolutionOptions::default()
            },
        );
        for result in [
            resolver.resolve("./missing", containing_file),
            resolver.resolve_type_reference("missing", containing_file),
        ] {
            assert!(result.resolved.is_none());
            assert_eq!(
                result.effective_mode,
                Some(expected),
                "{mode:?} {containing_file}"
            );
        }
    }
    assert!(filesystem.realpaths.lock().unwrap().is_empty());
    assert_eq!(ResolutionResult::default().effective_mode, None);
}

#[test]
fn resolution_evidence_retains_modes_and_paths_for_type_references() {
    let filesystem = conditional_package();
    let resolver = Resolver::new(
        &filesystem,
        ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        },
    );
    for (containing_file, mode, target) in [
        ("/app/main.ts", ModuleFormat::Esm, "esm.d.mts"),
        ("/app/main.cts", ModuleFormat::CommonJs, "commonjs.d.cts"),
    ] {
        let result = resolver.resolve_type_reference("pkg", containing_file);
        assert_eq!(result.effective_mode, Some(mode));
        let entry = result.resolved.unwrap();
        assert_eq!(
            entry.original_file_name,
            format!("/app/node_modules/pkg/{target}")
        );
        assert_eq!(entry.resolved_file_name, format!("/packages/pkg/{target}"));
        assert_eq!(
            filesystem.realpaths.lock().unwrap().last(),
            Some(&(entry.original_file_name, entry.resolved_file_name))
        );
    }
    assert_eq!(filesystem.realpaths.lock().unwrap().len(), 2);
}

#[test]
fn resolution_evidence_cache_hits_keep_original_observations() {
    let filesystem = conditional_package();
    let resolver = Resolver::new(
        &filesystem,
        ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        },
    );
    let first = resolver.resolve("pkg", "/app/main.ts");
    assert_eq!(first.effective_mode, Some(ModuleFormat::Esm));
    let observed_calls = filesystem.calls.load(Ordering::Relaxed);
    filesystem
        .write_file("/app/package.json", r#"{"type":"commonjs"}"#)
        .unwrap();
    assert_eq!(resolver.resolve("pkg", "/app/main.ts"), first);
    assert_eq!(filesystem.calls.load(Ordering::Relaxed), observed_calls);
    assert_eq!(filesystem.realpaths.lock().unwrap().len(), 1);

    resolver.clear_cache();
    let fresh = resolver.resolve("pkg", "/app/main.ts");
    assert_eq!(fresh.effective_mode, Some(ModuleFormat::CommonJs));
    let entry = fresh.resolved.unwrap();
    assert_eq!(
        entry.original_file_name,
        "/app/node_modules/pkg/commonjs.d.cts"
    );
    assert_eq!(entry.resolved_file_name, "/packages/pkg/commonjs.d.cts");
    assert_eq!(filesystem.realpaths.lock().unwrap().len(), 2);
}

#[test]
fn resolution_evidence_keeps_explicit_mode_cache_entries_separate() {
    let filesystem = conditional_package();
    let resolver = Resolver::new(
        &filesystem,
        ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        },
    );
    let default = resolver.resolve("pkg", "/app/main.ts");
    let required = resolver.resolve_with_mode("pkg", "/app/main.ts", ModuleFormat::CommonJs);
    let imported = resolver.resolve_with_mode("pkg", "/app/main.ts", ModuleFormat::Esm);
    assert_eq!(default.effective_mode, Some(ModuleFormat::Esm));
    assert_eq!(required.effective_mode, Some(ModuleFormat::CommonJs));
    assert_eq!(imported.effective_mode, Some(ModuleFormat::Esm));
    assert_eq!(default.resolved, imported.resolved);
    assert_ne!(required.resolved, imported.resolved);
    assert_eq!(filesystem.realpaths.lock().unwrap().len(), 3);
    let observed_calls = filesystem.calls.load(Ordering::Relaxed);
    assert_eq!(resolver.resolve("pkg", "/app/main.ts"), default);
    assert_eq!(
        resolver.resolve_with_mode("pkg", "/app/main.ts", ModuleFormat::CommonJs),
        required
    );
    assert_eq!(
        resolver.resolve_with_mode("pkg", "/app/main.ts", ModuleFormat::Esm),
        imported
    );
    assert_eq!(filesystem.calls.load(Ordering::Relaxed), observed_calls);
}
