//! Port of Go `internal/project/refcountcache_test.go` (`TestRefCountingCaches`).
//!
//! PORT: Go `file.Hash` is `xxh3_128(file.Text())` for a program file (see
//! `project::parsecache::HashedSourceFile`); the Rust `ParsedSourceFile`
//! has no hash field, so `key` computes it.

use std::rc::Rc;

use ts_goport::frontend::compiler::DuplicateSourceFile;
use ts_goport::frontend::parser::ParsedSourceFile;
use ts_goport::lsp::lsproto;
use ts_goport::project::{
    HashedSourceFile, ParseCacheKey, ProgramUpdateKind, RefCountCacheEntry, ResourceRequest,
    Session, SnapshotChange, UpdateReason, new_parse_cache_key,
};

use super::projecttestutil::{FileMap, files};
use super::util::*;

// Go: refcountcache_test.go:23 setup
fn setup(files: FileMap) -> Rc<Session> {
    bare_session(files)
}

/// Go `NewParseCacheKey(f.ParseOptions(), f.Hash, f.ScriptKind)`.
fn key(f: &ParsedSourceFile) -> ParseCacheKey {
    new_parse_cache_key(
        f.parse_options(),
        xxhash_rust::xxh3::xxh3_128(f.text.as_bytes()),
        f.script_kind,
    )
}

/// Go `NewParseCacheKey(dup.ParseOptions, dup.Hash, dup.ScriptKind)`.
fn dup_key(dup: &DuplicateSourceFile) -> ParseCacheKey {
    new_parse_cache_key(
        &dup.parse_options,
        xxhash_rust::xxh3::xxh3_128(dup.text.as_bytes()),
        dup.script_kind,
    )
}

/// Go `session.parseCache.entries.Load(key)`.
fn load(
    session: &Session,
    key: &ParseCacheKey,
) -> Option<Rc<RefCountCacheEntry<HashedSourceFile>>> {
    session.parse_cache.entries.borrow().get(key).cloned()
}

fn ref_count(entry: &RefCountCacheEntry<HashedSourceFile>) -> i32 {
    entry.ref_count.get()
}

const MAIN: &str = "/user/username/projects/myproject/src/main.ts";
const UTILS: &str = "/user/username/projects/myproject/src/utils.ts";
const MAIN_URI: &str = "file:///user/username/projects/myproject/src/main.ts";
const UTILS_URI: &str = "file:///user/username/projects/myproject/src/utils.ts";

// Go: refcountcache_test.go:42 files
fn parse_cache_files() -> FileMap {
    files(&[(MAIN, "const x = 1;"), (UTILS, "export function util() {}")])
}

fn inferred_program(session: &Session) -> &'static ts_goport::frontend::compiler::NewProgram {
    session
        .snapshot()
        .project_collection
        .inferred_project()
        .expect("inferred project")
        .borrow()
        .program
        .expect("inferred program")
}

child_test! {
    // Go: refcountcache_test.go:48 TestRefCountingCaches/parseCache/reuse unchanged file
    fn parse_cache_reuse_unchanged_file() {
        let session = setup(parse_cache_files());
        open(&session, MAIN_URI, "const x = 1;");
        open(&session, UTILS_URI, "export function util() {}");
        let program = inferred_program(&session);
        let main = program.get_source_file(MAIN).unwrap();
        let utils = program.get_source_file(UTILS).unwrap();
        let main_entry = load(&session, &key(&main)).expect("main entry");
        let utils_entry = load(&session, &key(&utils)).expect("utils entry");
        assert_eq!(ref_count(&main_entry), 1);
        assert_eq!(ref_count(&utils_entry), 1);

        edit(&session, MAIN_URI, 2, (0, 0), (0, 12), "const x = 2;");
        let p = program_of(&session, MAIN_URI);
        session.wait_for_background_tasks();
        let new_main = p.get_source_file(MAIN).unwrap();
        let new_main_entry = load(&session, &key(&new_main)).expect("new main entry");
        assert!(!Rc::ptr_eq(&new_main, &main));
        assert!(!Rc::ptr_eq(&new_main_entry, &main_entry));
        assert!(Rc::ptr_eq(&p.get_source_file(UTILS).unwrap(), &utils));
        // Old snapshot is deref'd immediately when replaced by UpdateSnapshot,
        // so old mainEntry is already disposed and utils refCount is already 1.
        assert_eq!(ref_count(&main_entry), 0);
        assert_eq!(ref_count(&new_main_entry), 1);
        assert_eq!(ref_count(&utils_entry), 1);
    }
}

child_test! {
    // Go: refcountcache_test.go:89 TestRefCountingCaches/parseCache/release file on close
    fn parse_cache_release_file_on_close() {
        let session = setup(parse_cache_files());
        open(&session, MAIN_URI, "const x = 1;");
        open(&session, UTILS_URI, "export function util() {}");
        let program = inferred_program(&session);
        let main = program.get_source_file(MAIN).unwrap();
        let utils = program.get_source_file(UTILS).unwrap();
        let main_entry = load(&session, &key(&main)).expect("main entry");
        let utils_entry = load(&session, &key(&utils)).expect("utils entry");
        assert_eq!(ref_count(&main_entry), 1);
        assert_eq!(ref_count(&utils_entry), 1);

        close(&session, MAIN_URI);
        let _ = language_service(&session, UTILS_URI);
        session.wait_for_background_tasks();
        assert_eq!(ref_count(&utils_entry), 1);
        assert_eq!(ref_count(&main_entry), 0);
        assert!(load(&session, &key(&main)).is_none());
    }
}

child_test! {
    // Go: refcountcache_test.go:114 TestRefCountingCaches/parseCache/unchanged program does not over-ref
    fn parse_cache_unchanged_program_does_not_over_ref() {
        let session = setup(parse_cache_files());
        open(&session, MAIN_URI, "const x = 1;");
        open(&session, UTILS_URI, "export function util() {}");

        // Get first snapshot and capture the program/entries
        let program1 = inferred_program(&session);
        let main = program1.get_source_file(MAIN).unwrap();
        let main_entry = load(&session, &key(&main)).expect("main entry");
        assert_eq!(ref_count(&main_entry), 1, "initial refCount should be 1");

        // Change utils.ts to trigger a new snapshot, but main.ts stays the same
        // so main's source file should be reused.
        edit(&session, UTILS_URI, 2, (0, 0), (0, 25), "export function util2() {}");

        // Get second snapshot - main.ts should be reused (program is new but shares source files)
        let program2 = program_of(&session, MAIN_URI);
        session.wait_for_background_tasks();
        let main2 = program2.get_source_file(MAIN).unwrap();
        assert!(Rc::ptr_eq(&main, &main2), "main.ts source file should be reused");

        // main.ts refCount should be 1: the old snapshot was immediately deref'd
        // when replaced, so only the new snapshot holds a ref.
        let main_entry = load(&session, &key(&main)).expect("main entry");
        assert_eq!(ref_count(&main_entry), 1, "refCount should be 1 (only new snapshot)");

        // Close files to trigger cleanup
        close(&session, MAIN_URI);
        close(&session, UTILS_URI);
        open(&session, "untitled:Untitled-1", "");
        session.wait_for_background_tasks();

        // Entry should now be gone (refCount 0, deleted)
        let entry = load(&session, &key(&main));
        assert!(
            entry.is_none(),
            "entry should be deleted after program is disposed (refCount {:?})",
            entry.map(|e| ref_count(&e))
        );
    }
}

child_test! {
    // Go: refcountcache_test.go:172 TestRefCountingCaches/parseCache/fallback rebuild does not double-ref changed file
    fn parse_cache_fallback_rebuild_does_not_double_ref_changed_file() {
        let session = setup(files(&[(MAIN, "const x = 1;"), (UTILS, "export const util = 1;")]));
        open(&session, MAIN_URI, "const x = 1;");

        let _ = language_service(&session, MAIN_URI);

        session.did_change_file(
            &bg(),
            &uri(MAIN_URI),
            2,
            &[lsproto::TextDocumentContentChangePartialOrWholeDocument {
                partial: None,
                whole_document: Some(lsproto::TextDocumentContentChangeWholeDocument {
                    text: "import { util } from \"./utils\";\nconst x = util;".to_string(),
                }),
            }],
        );

        let p_after = program_of(&session, MAIN_URI);
        session.wait_for_background_tasks();

        let project = session
            .snapshot()
            .project_collection
            .inferred_project()
            .expect("inferred project");
        assert_eq!(project.borrow().program_update_kind, ProgramUpdateKind::NEW_FILES);

        let main = p_after.get_source_file(MAIN).unwrap();
        let main_key = key(&main);
        let main_entry = load(&session, &main_key).expect("main entry");
        assert_eq!(ref_count(&main_entry), 1);

        close(&session, MAIN_URI);
        open(&session, "untitled:Untitled-1", "");
        session.wait_for_background_tasks();

        assert!(load(&session, &main_key).is_none());
    }
}

fn project_entries(session: &Session) -> usize {
    session
        .parse_cache
        .entries
        .borrow()
        .keys()
        .filter(|key| {
            key.file_name
                .starts_with("/user/username/projects/myproject/src/")
        })
        .count()
}

child_test! {
    // Go: refcountcache_test.go:216 TestRefCountingCaches/parseCache/case-only duplicate loads are released on dispose
    fn parse_cache_case_only_duplicate_loads_are_released_on_dispose() {
        let main_text = "import { util as a } from \"./utils\";\nimport { util as b } from \"./UTILS\";\nconst x = a + b;";
        let session = setup(files(&[(MAIN, main_text), (UTILS, "export const util = 1;")]));
        open(&session, MAIN_URI, main_text);

        let p = program_of(&session, MAIN_URI);

        assert_eq!(project_entries(&session), 3);

        assert!(p.get_source_file(UTILS).is_some());

        close(&session, MAIN_URI);
        open(&session, "untitled:Untitled-1", "");
        session.wait_for_background_tasks();

        assert_eq!(project_entries(&session), 0);
    }
}

const ENTRY: &str = "/user/username/projects/myproject/src/entry.ts";
const ENTRY_URI: &str = "file:///user/username/projects/myproject/src/entry.ts";

/// Go `session.DidChangeFile(ctx, entryURI, version, ...)` with one whole-document change.
fn change_entry(session: &Rc<Session>, version: i32, text: &str) {
    session.did_change_file(
        &bg(),
        &uri(ENTRY_URI),
        version,
        &[lsproto::TextDocumentContentChangePartialOrWholeDocument {
            partial: None,
            whole_document: Some(lsproto::TextDocumentContentChangeWholeDocument {
                text: text.to_string(),
            }),
        }],
    );
}

child_test! {
    // Go: refcountcache_test.go:256 TestRefCountingCaches/parseCache/case-only duplicate imported from multiple files is refcounted once
    fn parse_cache_case_only_duplicate_imported_from_multiple_files_is_refcounted_once() {
        // A file reached through a case-only-different file name from more than one
        // import site is parsed and acquired in the parse cache exactly once (same-casing
        // loads dedupe), but it must also be recorded as a duplicate exactly once.
        // Recording it once per import site would release it from the parse cache more
        // times than it was acquired, deleting the live entry out from under a program
        // that still references it and panicking the next time it is ref'd during a clone.
        let entry_text =
            "import { dep } from './sub/dep';\nimport './a';\nimport './b';\nexport const e = dep;";
        let session = setup(files(&[
            // entry.ts imports the canonical casing first, then pulls in a.ts and b.ts,
            // which both import the same file through an upper-cased name.
            (ENTRY, entry_text),
            (
                "/user/username/projects/myproject/src/a.ts",
                "import { dep } from './sub/DEP';\nexport const a = dep;",
            ),
            (
                "/user/username/projects/myproject/src/b.ts",
                "import { dep } from './sub/DEP';\nexport const b = dep;",
            ),
            ("/user/username/projects/myproject/src/sub/dep.ts", "export const dep = 1;"),
            ("/user/username/projects/myproject/src/c.ts", "export const c = 1;"),
        ]));
        open(&session, ENTRY_URI, entry_text);

        // The upper-cased name is recorded as a duplicate, and it should appear exactly once.
        let program = language_service(&session, ENTRY_URI).get_program();
        let dup_keys: Vec<ParseCacheKey> = program
            .duplicate_source_files()
            .iter()
            .filter(|dup| dup.parse_options.file_name.ends_with("/sub/DEP.ts"))
            .map(dup_key)
            .collect();
        assert_eq!(dup_keys.len(), 1, "case-only duplicate should be recorded exactly once");
        let dup_entry =
            load(&session, &dup_keys[0]).expect("duplicate entry should exist in the parse cache");
        assert_eq!(ref_count(&dup_entry), 1);

        // Force a full program rebuild (adding an import changes the file's module
        // structure). The old snapshot is disposed, releasing each of its source and
        // duplicate files exactly once. If the duplicate were recorded twice, the
        // shared cache entry would be released to zero and deleted here even though
        // the new program still references it.
        change_entry(
            &session,
            2,
            "import { dep } from \"./sub/dep\";\nimport \"./a\";\nimport \"./b\";\nimport \"./c\";\nexport const e = dep;",
        );
        let rebuilt_program = language_service(&session, ENTRY_URI).get_program();
        session.wait_for_background_tasks();

        // Every parse-cache key referenced by the live program must still exist.
        let assert_key_alive = |key: ParseCacheKey| {
            assert!(
                load(&session, &key).is_some(),
                "live program references a deleted parse-cache entry: {}",
                key.file_name
            );
        };
        for file in rebuilt_program.source_files() {
            assert_key_alive(key(file));
        }
        for dup in rebuilt_program.duplicate_source_files() {
            assert_key_alive(dup_key(dup));
        }

        // An incremental (clone) update re-references the duplicate files; this must
        // not panic with "cache entry not found".
        change_entry(
            &session,
            3,
            "import { dep } from './sub/dep';\nimport './a';\nimport './b';\nimport './c';\nexport const e = dep + 0;",
        );
        let _ = language_service(&session, ENTRY_URI);
        session.wait_for_background_tasks();

        // Closing the project releases everything cleanly.
        // (The configured project is not disposed until another file in another project is opened,
        // so we open an untitled file to trigger that.)
        close(&session, ENTRY_URI);
        open(&session, "untitled:Untitled-1", "");
        session.wait_for_background_tasks();

        assert_eq!(project_entries(&session), 0);
    }
}

// Go: refcountcache_test.go:355 files (extendedConfigCache)
fn extended_config_files() -> FileMap {
    files(&[
        (
            "/user/username/projects/myproject/tsconfig.json",
            r#"{
				"extends": "./tsconfig.base.json"
			}"#,
        ),
        (
            "/user/username/projects/myproject/tsconfig.base.json",
            r#"{
				"compilerOptions": {}
			}"#,
        ),
        (MAIN, "const x = 1;"),
    ])
}

fn extended_owners(session: &Session, p: &str) -> Option<usize> {
    session
        .extended_config_cache
        .entries
        .borrow()
        .get(&path(p))
        .map(|entry| entry.owners.borrow().len())
}

child_test! {
    // Go: refcountcache_test.go:365 TestRefCountingCaches/extendedConfigCache/release extended configs with project close
    fn extended_config_cache_release_extended_configs_with_project_close() {
        let session = setup(extended_config_files());
        open(&session, MAIN_URI, "const x = 1;");
        let config = session
            .snapshot()
            .config_file_registry
            .get_config(&path("/user/username/projects/myproject/tsconfig.json"))
            .expect("config");
        assert_eq!(
            config.extended_source_files()[0],
            "/user/username/projects/myproject/tsconfig.base.json"
        );
        assert_eq!(
            extended_owners(&session, "/user/username/projects/myproject/tsconfig.base.json"),
            Some(1)
        );

        close(&session, MAIN_URI);
        open(&session, "untitled:Untitled-1", "");
        session.wait_for_background_tasks();
        assert_eq!(
            extended_owners(&session, "/user/username/projects/myproject/tsconfig.base.json"),
            None
        );
    }
}

child_test! {
    // Go: refcountcache_test.go:383 TestRefCountingCaches/extendedConfigCache/release cache entries for unretained clone
    fn extended_config_cache_release_cache_entries_for_unretained_clone() {
        let session = setup(extended_config_files());
        let u = uri(MAIN_URI);
        let base_snapshot = session.snapshot();
        let extended_config_path = "/user/username/projects/myproject/tsconfig.base.json";
        let clone = base_snapshot.clone_(
            &bg(),
            SnapshotChange {
                reason: UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_NOT_LOADED,
                resource_request: ResourceRequest {
                    documents: vec![u.clone()],
                    ..Default::default()
                },
                ..Default::default()
            },
            &base_snapshot.fs.overlays,
            &session,
        );

        let project = clone.get_default_project(&u).expect("default project");
        assert_eq!(project.borrow().program_last_update, clone.id);

        let main = project.borrow().program.expect("program").get_source_file(MAIN).unwrap();
        let main_key = key(&main);
        let main_entry = load(&session, &main_key).expect("main entry");
        assert_eq!(ref_count(&main_entry), 1);

        assert_eq!(extended_owners(&session, extended_config_path), Some(1));

        clone.deref(&session);

        assert!(load(&session, &main_key).is_none());

        assert_eq!(extended_owners(&session, extended_config_path), None);
    }
}
