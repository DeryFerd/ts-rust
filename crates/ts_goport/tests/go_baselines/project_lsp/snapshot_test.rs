//! Port of Go `internal/project/snapshot_test.go` (`TestSnapshot`; the
//! benchmark is not ported).

use std::rc::{Rc, Weak};

use ts_goport::frontend::compiler::{self, NewProgram};
use ts_goport::lsp::lsproto;
use ts_goport::program::ls_program;
use ts_goport::project::{
    CompilerHost, FileChange, FileChangeKind, FileSource, ProgramUpdateKind, Session, Snapshot,
};

use super::projecttestutil::{FileMap, files, with_request_id};
use super::util::*;

// Go: snapshot_test.go:21 setup
fn setup(files: FileMap) -> Rc<Session> {
    bare_session(files)
}

child_test! {
    // Go: snapshot_test.go:38 TestSnapshot/compilerHost gets frozen with snapshot's FS only once
    fn compiler_host_gets_frozen_with_snapshots_fs_only_once() {
        let session = setup(files(&[
            ("/home/projects/TS/p1/tsconfig.json", "{}"),
            ("/home/projects/TS/p1/index.ts", "console.log('Hello, world!');"),
        ]));
        open(&session, "file:///home/projects/TS/p1/index.ts", "console.log('Hello, world!');");
        open(&session, "untitled:Untitled-1", "");
        let snapshot_before = session.snapshot();

        edit(&session, "file:///home/projects/TS/p1/index.ts", 2, (0, 24), (0, 24), "\n");
        let _ = language_service(&session, "file:///home/projects/TS/p1/index.ts");
        let snapshot_after = session.snapshot();

        // Configured project was updated by a clone
        let configured = snapshot_after
            .project_collection
            .configured_project(&path("/home/projects/ts/p1/tsconfig.json"))
            .expect("configured project");
        assert_eq!(configured.borrow().program_update_kind, ProgramUpdateKind::CLONED);
        // Inferred project wasn't updated last snapshot change, so its program update kind is still NewFiles
        let inferred_before = snapshot_before.project_collection.inferred_project().expect("inferred before");
        let inferred_after = snapshot_after.project_collection.inferred_project().expect("inferred after");
        assert!(Rc::ptr_eq(&inferred_before, &inferred_after));
        assert_eq!(inferred_after.borrow().program_update_kind, ProgramUpdateKind::NEW_FILES);
        // host for inferred project should not change
        let host = inferred_after.borrow().host.clone().expect("inferred host");
        let source = host.source_fs.source.borrow().clone();
        assert_eq!(
            Rc::as_ptr(&source) as *const u8,
            Rc::as_ptr(&snapshot_before.fs) as *const u8
        );
    }
}

child_test! {
    // Go: snapshot_test.go:73 TestSnapshot/cached disk files are cleaned up
    fn cached_disk_files_are_cleaned_up() {
        let session = setup(files(&[
            ("/home/projects/TS/p1/tsconfig.json", "{}"),
            ("/home/projects/TS/p1/index.ts", "import { a } from './a'; console.log(a);"),
            ("/home/projects/TS/p1/a.ts", "export const a = 1;"),
            ("/home/projects/TS/p2/tsconfig.json", "{}"),
            ("/home/projects/TS/p2/index.ts", "import { b } from './b'; console.log(b);"),
            ("/home/projects/TS/p2/b.ts", "export const b = 2;"),
        ]));
        open(&session, "file:///home/projects/TS/p1/index.ts", "import { a } from './a'; console.log(a);");
        open(&session, "file:///home/projects/TS/p2/index.ts", "import { b } from './b'; console.log(b);");
        let snapshot_before = session.snapshot();

        // a.ts and b.ts are cached
        assert!(snapshot_before.fs.disk_files.contains_key(&path("/home/projects/ts/p1/a.ts")));
        assert!(snapshot_before.fs.disk_files.contains_key(&path("/home/projects/ts/p2/b.ts")));

        // Close p1's only open file
        close(&session, "file:///home/projects/TS/p1/index.ts");
        // Next open file is unrelated to p1, triggers p1 closing and file cache cleanup
        open(&session, "untitled:Untitled-1", "");
        let snapshot_after = session.snapshot();

        // a.ts is cleaned up, b.ts is still cached
        assert!(!snapshot_after.fs.disk_files.contains_key(&path("/home/projects/ts/p1/a.ts")));
        assert!(snapshot_after.fs.disk_files.contains_key(&path("/home/projects/ts/p2/b.ts")));
    }
}

child_test! {
    // Go: snapshot_test.go:103 TestSnapshot/GetFile returns nil for non-existent files
    fn get_file_returns_nil_for_non_existent_files() {
        let session = setup(files(&[
            ("/home/projects/TS/p1/tsconfig.json", "{}"),
            ("/home/projects/TS/p1/index.ts", "console.log('Hello, world!');"),
        ]));
        open(&session, "file:///home/projects/TS/p1/index.ts", "console.log('Hello, world!');");
        let snapshot = session.snapshot();

        let handle = snapshot.get_file("/home/projects/TS/p1/nonexistent.ts");
        assert!(handle.is_none(), "GetFile should return nil for non-existent file");

        // Test that ReadFile returns false for non-existent file
        let (_, ok) = snapshot.read_file("/home/projects/TS/p1/nonexistent.ts");
        assert!(!ok, "ReadFile should return false for non-existent file");
    }
}

child_test! {
    // Go: snapshot_test.go:121 TestSnapshot/program change loads node_modules dependency and auto-imports includes it
    fn program_change_loads_node_modules_dependency_and_auto_imports_includes_it() {
        let session = setup(files(&[
            (
                "/home/projects/otherproject/tsconfig.json",
                r#"{
				"compilerOptions": {
					"module": "commonjs"
				}
			}"#,
            ),
            ("/home/projects/otherproject/index.ts", ""),
            (
                "/home/projects/node_modules/foo/package.json",
                r#"{
				"types": "index.d.ts",
				"typesVersions": {
					"*": {
						"bar/*": ["dist/*"],
						"exact-match": ["dist/index.d.ts"],
						"foo/*": ["dist/*"],
						"*": ["dist/*"]
					}
				}
			}"#,
            ),
            ("/home/projects/node_modules/foo/nope.d.ts", "export const nope = 0;"),
            ("/home/projects/node_modules/foo/dist/index.d.ts", "export const index = 0;"),
            ("/home/projects/node_modules/foo/dist/blah.d.ts", "export const blah = 0;"),
            ("/home/projects/node_modules/foo/dist/foo/onlyInFooFolder.d.ts", "export const foo = 0;"),
            ("/home/projects/node_modules/foo/dist/subfolder/one.d.ts", "export const one = 0;"),
        ]));
        let other_index_uri = "file:///home/projects/otherproject/index.ts";

        // Open the file
        open(&session, other_index_uri, "");

        // Insert import statement:
        // This will trigger both a program rebuild which will include the node_modules files,
        // and an auto-import collection which should find the exports from those files.
        edit(
            &session,
            other_index_uri,
            2,
            (0, 0),
            (0, 0),
            r#"import {} from "foo/foo/subfolder/one";"#,
        );

        // Now trigger snapshot clone with both program update and auto-imports registry building.
        session
            .get_current_language_service_with_auto_imports(&bg(), &uri(other_index_uri))
            .unwrap_or_else(|err| panic!("{}", err.error()));
        session.close();
    }
}

/// Go `lsproto.TextDocumentContentChangePartialOrWholeDocument{WholeDocument: ...}`.
fn whole(text: &str) -> lsproto::TextDocumentContentChangePartialOrWholeDocument {
    lsproto::TextDocumentContentChangePartialOrWholeDocument {
        partial: None,
        whole_document: Some(lsproto::TextDocumentContentChangeWholeDocument {
            text: text.to_string(),
        }),
    }
}

child_test! {
    // Go: snapshot_test.go:175 TestSnapshot/fallback rebuild with recomputed parse options is safe for later clone
    fn fallback_rebuild_with_recomputed_parse_options_is_safe_for_later_clone() {
        let session = setup(files(&[
            ("/project/node_modules/pkg/index.ts", "export const pkg = 0;"),
            ("/project/src/other.ts", "export const other = 1;"),
        ]));
        let pkg_uri = "file:///project/node_modules/pkg/index.ts";
        let other_uri = "file:///project/src/other.ts";

        open(&session, pkg_uri, "export const pkg = 0;");
        open(&session, other_uri, "export const other = 1;");
        let _ = language_service(&session, pkg_uri);

        session
            .fs
            .fs
            .write_file("/project/node_modules/pkg/package.json", r#"{ "type": "module" }"#)
            .unwrap();
        session.did_change_file(
            &bg(),
            &uri(pkg_uri),
            2,
            &[whole(r#"import "./missing"; export const pkg = 1;"#)],
        );
        let _ = language_service(&session, pkg_uri);

        session.did_change_file(&bg(), &uri(other_uri), 2, &[whole("export const other = 2;")]);
        let _ = language_service(&session, other_uri);
    }
}

child_test! {
    // Go: snapshot_test.go:214 TestSnapshot/auto-import snapshot is adopted when session snapshot is unchanged
    fn auto_import_snapshot_is_adopted_when_session_snapshot_is_unchanged() {
        let index_text = "const value = foo;";
        let session = setup(files(&[
            ("/home/projects/TS/p1/tsconfig.json", "{}"),
            ("/home/projects/TS/p1/index.ts", index_text),
            ("/home/projects/TS/p1/foo.ts", "export const foo = 1;"),
        ]));
        let ctx = bg();
        let index_uri = "file:///home/projects/TS/p1/index.ts";

        open(&session, index_uri, index_text);
        let _ = language_service(&session, index_uri);

        let base_snapshot = session.snapshot();
        let prepared_snapshot =
            session.get_snapshot_with_auto_imports(&ctx, &base_snapshot, &uri(index_uri));

        session.wait_for_background_tasks();
        assert!(Rc::ptr_eq(&session.snapshot(), &prepared_snapshot));

        // Go: defer preparedSnapshot.Deref(session); t.Cleanup(session.Close)
        Snapshot::deref(&prepared_snapshot, &session);
        session.close();
    }
}

child_test! {
    // Go: snapshot_test.go:238 TestSnapshot/no-op watch change does not rebuild program
    fn no_op_watch_change_does_not_rebuild_program() {
        let index_text = "import { a } from './a'; console.log(a);";
        let session = setup(files(&[
            ("/home/projects/TS/p1/tsconfig.json", "{}"),
            ("/home/projects/TS/p1/index.ts", index_text),
            ("/home/projects/TS/p1/a.ts", "export const a = 1;"),
        ]));
        let index_uri = "file:///home/projects/TS/p1/index.ts";
        let config_path = path("/home/projects/ts/p1/tsconfig.json");
        let configured_program = |session: &Rc<Session>| -> &'static NewProgram {
            session
                .snapshot()
                .project_collection
                .configured_project(&config_path)
                .expect("configured project")
                .borrow()
                .program
                .expect("program")
        };

        open(&session, index_uri, index_text);
        let _ = language_service(&session, index_uri);

        let program_before = configured_program(&session);

        // Send a watch change event for a project file whose content on disk is unchanged.
        // This should not invalidate the program or trigger a recheck.
        session.pending_file_changes.borrow_mut().push(FileChange {
            kind: FileChangeKind::WATCH_CHANGE,
            uri: uri("file:///home/projects/TS/p1/a.ts"),
            ..Default::default()
        });
        let _ = language_service(&session, index_uri);

        let program_after = configured_program(&session);
        assert!(
            same_program(program_before, program_after),
            "no-op watch change should not rebuild the program"
        );

        // A watch change that reflects an actual content change on disk must still
        // rebuild the program.
        session
            .fs
            .fs
            .write_file("/home/projects/TS/p1/a.ts", "export const a = 2;")
            .unwrap();
        session.pending_file_changes.borrow_mut().push(FileChange {
            kind: FileChangeKind::WATCH_CHANGE,
            uri: uri("file:///home/projects/TS/p1/a.ts"),
            ..Default::default()
        });
        let _ = language_service(&session, index_uri);

        let program_changed = configured_program(&session);
        assert!(
            !same_program(program_before, program_changed),
            "real watch change should rebuild the program"
        );
        session.close();
    }
}

// The memory tests below: one configured project. A body edit of index.ts
// clones the program; an edit that adds an import loads it again.
const P1_INDEX_URI: &str = "file:///home/projects/TS/p1/index.ts";
const P1_INDEX_TEXT: &str = "import { a } from './a';\nexport const x = a + 1;";

fn p1_files() -> FileMap {
    files(&[
        ("/home/projects/TS/p1/tsconfig.json", "{}"),
        ("/home/projects/TS/p1/index.ts", P1_INDEX_TEXT),
        ("/home/projects/TS/p1/a.ts", "export const a = 1;"),
        ("/home/projects/TS/p1/b.ts", "export const b = 1;"),
    ])
}

/// Replaces the `1` of `P1_INDEX_TEXT` (a body edit) and loads the program.
fn p1_body_edit(session: &Rc<Session>, version: i32, digit: &str) {
    edit(session, P1_INDEX_URI, version, (1, 21), (1, 22), digit);
    let _ = language_service(session, P1_INDEX_URI);
}

/// Adds an import to index.ts (a new program load) and loads the program.
fn p1_import_edit(session: &Rc<Session>, version: i32) {
    edit(
        session,
        P1_INDEX_URI,
        version,
        (0, 0),
        (0, 0),
        "import { b } from './b';\n",
    );
    let _ = language_service(session, P1_INDEX_URI);
}

/// The number of module resolutions that the resolver of `p`'s load keeps.
fn cached_resolutions(p: &NewProgram) -> usize {
    p.resolver
        .as_ref()
        .expect("program resolver")
        .caches
        .module_resolution_cache
        .cache
        .borrow()
        .len()
}

/// The compiler host and the program update kind of the p1 project in the
/// current snapshot.
fn p1_host(session: &Rc<Session>) -> (Rc<CompilerHost>, ProgramUpdateKind) {
    let project = session
        .snapshot()
        .project_collection
        .configured_project(&path("/home/projects/ts/p1/tsconfig.json"))
        .expect("configured project");
    let project = project.borrow();
    (
        project.host.clone().expect("project host"),
        project.program_update_kind,
    )
}

/// True when `host` dropped its data (`compiler::CompilerHost::release`).
/// Until then a frozen host keeps the config registry, and a tracking host
/// its seen files.
fn is_released(host: &CompilerHost) -> bool {
    host.config_file_registry.borrow().is_none() && host.source_fs.seen_files.borrow().is_none()
}

child_test! {
    // PORT: no Go counterpart (Go has no parse workers). Only the first
    // program load of a project lets parse workers parse ahead
    // (`compiler::CompilerHost::prefetch_parses`). A later load gets its
    // files from the parse cache, which uses a worker parse only on a miss,
    // so the workers parsed the whole program again for nothing, and those
    // parses stayed in the workers' AST arenas.
    fn only_first_program_load_of_project_prefetches_parses() {
        let session = setup(p1_files());
        open(&session, P1_INDEX_URI, P1_INDEX_TEXT);
        let _ = language_service(&session, P1_INDEX_URI);
        let (first, _) = p1_host(&session);
        assert!(compiler::CompilerHost::prefetch_parses(&*first));

        // Adding an import loads the program again (no clone).
        p1_import_edit(&session, 2);
        let (second, kind) = p1_host(&session);
        assert!(!Rc::ptr_eq(&first, &second));
        assert_ne!(kind, ProgramUpdateKind::CLONED);
        assert!(!compiler::CompilerHost::prefetch_parses(&*second));
    }
}

child_test! {
    // PORT: no Go counterpart (Go's GC frees a host and a resolver with
    // their last program). A host drops its data when no live program uses
    // it (`ls_program::release_now`). A clone shares the processed files of
    // the program it was cloned from (Go `UpdateProgram`), and their
    // resolver reads the first host's file system, so that host and the
    // resolver's caches stay until the last clone is released. The test
    // holds the `Rc` of the second program after its release, as a stale Go
    // holder would; its host still drops its data.
    fn released_program_hosts_drop_their_data() {
        let session = setup(p1_files());
        open(&session, P1_INDEX_URI, P1_INDEX_TEXT);
        let _ = language_service(&session, P1_INDEX_URI);
        let (h1, _) = p1_host(&session);

        p1_body_edit(&session, 2, "2");
        let (h2, kind) = p1_host(&session);
        let p2 = program(&session, P1_INDEX_URI);
        assert_eq!(kind, ProgramUpdateKind::CLONED);
        p1_body_edit(&session, 3, "3");
        let (h3, kind) = p1_host(&session);
        assert_eq!(kind, ProgramUpdateKind::CLONED);

        // The first two programs are released. The first host stays for the
        // second clone; the first clone's own host goes.
        assert!(!is_released(&h1));
        assert!(is_released(&h2));
        assert!(!is_released(&h3));
        // A released program still finds its files by name (Go
        // `GetSourceFile` reads the host's case sensitivity).
        assert!(has_file(&p2, "/home/projects/TS/p1/a.ts"));
        // The second clone still uses the first load's resolver.
        assert!(cached_resolutions(&p2) > 0);

        // Adding an import loads the program again. The last clone is
        // released, and with it the first host and the first load's
        // resolver caches.
        p1_import_edit(&session, 4);
        let (h4, kind) = p1_host(&session);
        assert_ne!(kind, ProgramUpdateKind::CLONED);
        assert!(is_released(&h1));
        assert!(is_released(&h3));
        assert!(!is_released(&h4));
        assert_eq!(cached_resolutions(&p2), 0);
        assert!(cached_resolutions(&program(&session, P1_INDEX_URI)) > 0);
    }
}

child_test! {
    // PORT: no Go counterpart. The snapshot file system that a released
    // program's host kept (overlays, the disk file map, cachedvfs results)
    // is freed with the host's data, as Go frees it with the host.
    fn released_program_host_frees_its_snapshot_fs() {
        let session = setup(p1_files());
        open(&session, P1_INDEX_URI, P1_INDEX_TEXT);
        let _ = language_service(&session, P1_INDEX_URI);
        p1_body_edit(&session, 2, "2");
        let (h2, _) = p1_host(&session);
        let fs2: Weak<dyn FileSource> = Rc::downgrade(&*h2.source_fs.source.borrow());

        // The next edit releases the program of `h2`. The background tasks
        // of the snapshot changes hold the old snapshots until they run.
        p1_body_edit(&session, 3, "3");
        session.wait_for_background_tasks();
        assert!(is_released(&h2));
        assert!(fs2.upgrade().is_none());
    }
}

child_test! {
    // PORT: no Go counterpart (the GC frees the nodes). A released program
    // version frees the synthetic nodes that the dispatch thread made for
    // it. Declaration diagnostics make node builder nodes for each version,
    // and the live synthetic slots stay flat across edits.
    fn released_program_frees_its_synthetic_nodes() {
        let file = "/home/projects/TS/p1/index.ts";
        let file_uri = "file:///home/projects/TS/p1/index.ts";
        let props: String = (0..80).map(|i| format!("p{i}: {i}, ")).collect();
        let text = format!(
            "function make() {{ return {{ {props}}}; }}\n\
             export const lsMix0 = make();\n\
             export const lsMix1 = class {{ private p = 12; }};\n"
        );
        let session = setup(files(&[
            ("/home/projects/TS/p1/tsconfig.json", r#"{ "compilerOptions": { "declaration": true } }"#),
            (file, text.as_str()),
        ]));
        open(&session, file_uri, &text);
        // Code, start and end of the declaration diagnostics of the file.
        let declaration_diagnostics = |p: &NewProgram| -> Vec<(i32, i32, i32)> {
            let root = p.get_source_file(file).expect("index.ts is in the program").root;
            ls_program::get_declaration_diagnostics(p, &with_request_id(&bg()), root)
                .iter()
                .map(|d| (d.code, d.pos, d.end))
                .collect()
        };
        let live = ts_goport::ast::synthetic_live_slot_count;

        let p1 = program(&session, file_uri);
        let before = live();
        let first = declaration_diagnostics(&p1);
        let made = live() - before;
        // TS4094: the private member of the exported class expression.
        assert!(first.iter().any(|&(code, _, _)| code == 4094), "{first:?}");

        // Each edit makes a new program version, and the snapshot update
        // releases the one before. An edit after the last line keeps the
        // diagnostic positions.
        let end_line = text.lines().count() as u32;
        let mut live_after_release = Vec::new();
        for version in 2..=5 {
            edit(&session, file_uri, version, (end_line, 0), (end_line, 0), "\n");
            let p = program(&session, file_uri);
            live_after_release.push(live());
            assert_eq!(declaration_diagnostics(&p), first);
        }
        let growth = live_after_release[3].saturating_sub(live_after_release[0]);
        assert!(
            growth < made / 2,
            "live synthetic slots grew by {growth} over 3 released versions, one version made {made}: {live_after_release:?}"
        );
    }
}
