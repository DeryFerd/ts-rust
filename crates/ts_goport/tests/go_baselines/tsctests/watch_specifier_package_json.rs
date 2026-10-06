//! Port-only test of the seen files of `tsc --watch` (watchcfg1, R170
//! reviewer item 1).
//!
//! PORT: Go's module specifier lookups read package.json files through the
//! program's resolver, whose file system is the watcher's tracking file
//! system (module/resolver.go:1755 getPackageJsonInfo). So a package.json
//! that only such a lookup read is a seen file, and a change to it starts
//! a full build (execute/watcher.go:326). The port makes these lookups on
//! the checker threads on the OS file system (modulespecifiers/host.rs),
//! and the watcher adds them to its seen files after each full build.
//!
//! The expected builds and errors are those of `tsgo-oracle-673a5f17d713
//! -w -p tsconfig.json` on the same files with the OS watcher: the edit of
//! `node_modules/lib/package.json` starts a build with no errors, and the
//! next edit of `src/index.ts` reports TS2883.

use ts_goport::execute;
use ts_goport::execute::tsc::Watcher;
use ts_goport::fswatch::{Event, EventKind};
use ts_goport::gostd::context;

use crate::support::child::{command_line_in_process, new_in_process_test_sys, run_test_in_child};
use crate::support::runner::TscInput;

const PROJECT: &str = "/home/src/workspaces/project";

/// The full and fast path builds of `w` (Go `w.FullBuilds()`,
/// `w.FastPathBuilds()`).
fn builds(w: &dyn Watcher) -> (i32, i32) {
    let w = w
        .as_any()
        .downcast_ref::<execute::watcher::Watcher>()
        .expect("the watcher is an *execute.Watcher");
    (w.full_builds(), w.fast_path_builds())
}

#[test]
fn a_package_json_that_only_a_module_specifier_reads_is_watched() {
    run_test_in_child(
        "tsctests::watch_specifier_package_json::a_package_json_that_only_a_module_specifier_reads_is_watched",
        || {
            let file = |name: &str, text: &str| (format!("{PROJECT}/{name}"), text.into());
            let input = TscInput {
                files: [
                    file(
                        "tsconfig.json",
                        r#"{"compilerOptions":{"declaration":true,"emitDeclarationOnly":true,"outDir":"out","rootDir":".","module":"esnext","moduleResolution":"bundler","strict":true,"skipLibCheck":true},"include":["src"]}"#,
                    ),
                    // The reference reaches foo.d.ts without a module
                    // resolution, and dist/package.json ends the package
                    // scope lookup of the file loader. So only the module
                    // specifier of `Foo` in the declaration of `v` reads
                    // lib/package.json.
                    file(
                        "src/index.ts",
                        "/// <reference path=\"../node_modules/lib/dist/foo.d.ts\" />\nexport const v = makeFoo();\n",
                    ),
                    file(
                        "node_modules/lib/package.json",
                        r#"{ "name": "lib", "version": "1.0.0" }"#,
                    ),
                    file(
                        "node_modules/lib/dist/package.json",
                        r#"{ "sideEffects": false }"#,
                    ),
                    file(
                        "node_modules/lib/dist/foo.d.ts",
                        "export interface Foo { a: number }\ndeclare global {\n  function makeFoo(): Foo;\n}\n",
                    ),
                ]
                .into_iter()
                .collect(),
                command_line_args: vec!["--watch".to_string()],
                ..Default::default()
            };
            let sys = new_in_process_test_sys(&input);
            let args = ["--watch", "--pretty", "false"].map(String::from);
            let result = command_line_in_process(&context::background(), &sys, &args);
            let mut w = result
                .watcher
                .expect("expected Watcher to be non-nil in watch mode");
            let fs = sys.fs_from_file_map();
            let (declaration, _) = fs.read_file(&format!("{PROJECT}/out/src/index.d.ts"));
            assert!(
                declaration.contains(r#"import("lib/dist/foo").Foo"#),
                "the first build names Foo through lib/package.json: {declaration}"
            );

            let send = |path: &str| {
                sys.mock_watch_backend().send_events(vec![Event {
                    kind: EventKind::Update,
                    path: format!("{PROJECT}/{path}"),
                }]);
            };

            // lib/package.json now exports only ".": Go builds again.
            let (full, fast) = builds(w.as_ref());
            let _ = fs.write_file(
                &format!("{PROJECT}/node_modules/lib/package.json"),
                r#"{ "name": "lib", "version": "1.0.0", "exports": { ".": "./dist/index.d.ts" } }"#,
            );
            send("node_modules/lib/package.json");
            w.do_cycle();
            assert_eq!(
                builds(w.as_ref()),
                (full + 1, fast),
                "a change to a package.json that a module specifier lookup read is a full build"
            );

            // The next declaration of `v` reads the new package.json.
            sys.set_output_bytes(Vec::new());
            let _ = fs.write_file(
                &format!("{PROJECT}/src/index.ts"),
                "/// <reference path=\"../node_modules/lib/dist/foo.d.ts\" />\nexport const v = makeFoo();\nexport const w = 1;\n",
            );
            send("src/index.ts");
            w.do_cycle();
            let out = sys.output_text();
            assert!(
                out.contains("error TS2883"),
                "the module specifier lookup reads the new package.json, got: {out}"
            );
        },
    );
}
