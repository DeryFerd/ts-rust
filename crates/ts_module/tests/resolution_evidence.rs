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
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

struct ObservedFileSystem {
    files: MemoryFileSystem,
    calls: AtomicUsize,
    realpaths: Mutex<Vec<(String, String)>>,
    return_input_from_realpath: bool,
}

impl ObservedFileSystem {
    fn new(entries: &[(&str, &str)]) -> Self {
        let files = MemoryFileSystem::new(true);
        for (path, contents) in entries {
            files.write_file(path, contents).unwrap();
        }
        Self {
            files,
            calls: AtomicUsize::new(0),
            realpaths: Mutex::new(Vec::new()),
            return_input_from_realpath: false,
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
        let result = if self.return_input_from_realpath {
            path.to_owned()
        } else {
            self.files.realpath(path)
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
fn resolution_evidence_records_the_selected_symlink_candidate() {
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
    assert_eq!(entry.resolved_file_name, "/real/pkg/entry.ios.d.ts");
    assert!(entry.is_external_library_import);
    assert_eq!(
        *filesystem.realpaths.lock().unwrap(),
        [(entry.original_file_name, entry.resolved_file_name)]
    );
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
        (false, "./direct", "/app/direct.ts"),
        (true, "./alias", "/app/alias.ts"),
    ] {
        let mut filesystem =
            ObservedFileSystem::new(&[("/app/direct.ts", ""), ("/real/entry.ts", "")]);
        filesystem
            .files
            .add_file_link("/real/entry.ts", "/app/alias.ts");
        filesystem.return_input_from_realpath = return_input;
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
