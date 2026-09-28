//! Port of Go `internal/project/snapshot_test.go` (`TestSnapshot`; the
//! benchmark is not ported).

use std::rc::Rc;

use ts_goport::frontend::compiler::NewProgram;
use ts_goport::lsp::lsproto;
use ts_goport::program::ls_program;
use ts_goport::project::{ProgramUpdateKind, Session};

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
        let declaration_diagnostics = |p: &'static NewProgram| -> Vec<(i32, i32, i32)> {
            let root = p.get_source_file(file).expect("index.ts is in the program").root;
            ls_program::get_declaration_diagnostics(p, &with_request_id(&bg()), root)
                .iter()
                .map(|d| (d.code, d.pos, d.end))
                .collect()
        };
        let live = ts_goport::ast::synthetic_live_slot_count;

        let p1 = program(&session, file_uri);
        let before = live();
        let first = declaration_diagnostics(p1);
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
            assert_eq!(declaration_diagnostics(p), first);
        }
        let growth = live_after_release[3].saturating_sub(live_after_release[0]);
        assert!(
            growth < made / 2,
            "live synthetic slots grew by {growth} over 3 released versions, one version made {made}: {live_after_release:?}"
        );
    }
}
