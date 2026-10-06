//! Port-only tests of the file versions that `tsc -b --watch` keeps
//! (watchfix1 part 2): a config change that changes the module indicator
//! options drops the kept parses that read them, and one that does not
//! keeps them (item 3), and a task whose status is reset lets go of the
//! versions that its errors held (item 4).
//!
//! Go has no file versions: its GC frees a file when no program, cache or
//! diagnostic holds it. The output of each cycle is Go's: the lines that
//! the tests check are those of `tsgo-oracle-673a5f17d713 -b -w` on the same
//! files and edits with the OS watcher
//! (target/continuation-r97-goport/watchfix1/runs, mdrop and held2, and
//! watchfix1/rb/runs/mjx).
//! The first version of each file is static; each later parse of it is a
//! freeable version (`ast::file_versions_made`, `ast::dead_file_versions`).

use std::time::{Duration, Instant};

use ts_goport::fswatch::{Event, EventKind};
use ts_goport::gostd::context;

use crate::support::child::{command_line_in_process, new_in_process_test_sys, run_test_in_child};
use crate::support::runner::TscInput;

const PROJECT: &str = "/home/src/workspaces/project";

/// A watch session of `args` on `files` (paths relative to `PROJECT`). Each
/// `edit` writes one file, sends its event and runs one cycle, then `check`
/// gets the edit's index and the cycle's output.
fn session(
    files: &[(&str, &str)],
    args: &[&str],
    edits: &[(&str, &str)],
    mut check: impl FnMut(usize, &str),
) {
    let input = TscInput {
        files: files
            .iter()
            .map(|(name, text)| (format!("{PROJECT}/{name}"), (*text).into()))
            .collect(),
        ..Default::default()
    };
    let sys = new_in_process_test_sys(&input);
    let args: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
    let result = command_line_in_process(&context::background(), &sys, &args);
    let mut w = result
        .watcher
        .expect("expected Watcher to be non-nil in watch mode");
    let fs = sys.fs_from_file_map();
    let out = sys.output_text();
    assert!(
        out.contains("Found 0 errors. Watching for file changes."),
        "first build: {out}"
    );
    for (i, (name, text)) in edits.iter().enumerate() {
        sys.set_output_bytes(Vec::new());
        let path = format!("{PROJECT}/{name}");
        let _ = fs.write_file(&path, text);
        sys.mock_watch_backend().send_events(vec![Event {
            kind: EventKind::Update,
            path,
        }]);
        w.do_cycle();
        check(i, &sys.output_text());
    }
}

/// `(made, dead)` file versions once the dead count reaches `dead` or 10 s
/// pass: the free thread frees the dropped versions
/// (`BuildHost::drop_kept_parses_that_read_module_indicator_options`).
fn file_versions(dead: usize) -> (usize, usize) {
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        ts_goport::program::wait_for_background_releases();
        let now = (
            ts_goport::ast::file_versions_made(),
            ts_goport::ast::dead_file_versions(),
        );
        if now.1 >= dead || Instant::now() > deadline {
            return now;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// Two script files, so each parse reads its module indicator options.
fn config(detection: &str, new_line: &str, files: &str) -> String {
    format!(
        r#"{{"compilerOptions":{{"strict":true,"outDir":"out","rootDir":"src","types":[],"lib":["es5"],"moduleDetection":"{detection}"{new_line}}},"files":[{files}]}}"#
    )
}

#[test]
fn build_watch_drops_kept_parses_whose_module_indicator_options_changed() {
    run_test_in_child(
        "tsctests::watch_build_kept_versions::build_watch_drops_kept_parses_whose_module_indicator_options_changed",
        || {
            let both = r#""src/s1.ts","src/s2.ts""#;
            let first = config("auto", "", both);
            let new_line = config("auto", r#","newLine":"lf""#, both);
            let force = config("force", r#","newLine":"lf""#, r#""src/s1.ts""#);
            session(
                &[
                    ("tsconfig.json", &first),
                    ("src/s1.ts", "const one: number = 1;\n"),
                    ("src/s2.ts", "const two: number = 2;\n"),
                ],
                &["--build", "--watch", "--pretty", "false"],
                &[
                    ("src/s2.ts", "const two: number = 22;\n"),
                    ("tsconfig.json", &new_line),
                    ("tsconfig.json", &force),
                ],
                |i, out| {
                    assert!(
                        out.contains("Found 0 errors. Watching for file changes."),
                        "edit {i}: {out}"
                    );
                    let expected = match i {
                        // s2.ts v2.
                        0 => (1, 0),
                        // The module indicator inputs stay: both kept
                        // parses are used again, nothing is parsed.
                        1 => (1, 0),
                        // `force` changes them: s1.ts is parsed again, and
                        // the kept s2.ts v2, which no build of the cycle
                        // takes, goes. Before, it went back to the kept
                        // parses for the rest of the session.
                        _ => (2, 1),
                    };
                    assert_eq!(file_versions(expected.1), expected, "edit {i}");
                },
            );
        },
    );
}

#[test]
fn build_watch_keeps_kept_parses_whose_module_indicator_inputs_stay() {
    run_test_in_child(
        "tsctests::watch_build_kept_versions::build_watch_keeps_kept_parses_whose_module_indicator_inputs_stay",
        || {
            // A script file, whose parse reads its module indicator
            // options, and a module file, whose parse does not.
            let config = |module: &str, jsx: &str| {
                format!(
                    r#"{{"compilerOptions":{{"strict":true,"outDir":"out","rootDir":"src","types":[],"lib":["es5"],"module":"{module}","jsx":"{jsx}"}},"files":["src/s1.ts","src/m1.ts"]}}"#
                )
            };
            session(
                &[
                    ("tsconfig.json", &config("es2020", "preserve")),
                    ("src/s1.ts", "const one: number = 1;\n"),
                    ("src/m1.ts", "export const m: number = 1;\n"),
                ],
                &["--build", "--watch", "--pretty", "false"],
                &[
                    ("src/s1.ts", "const one: number = 11;\n"),
                    ("tsconfig.json", &config("esnext", "preserve")),
                    ("tsconfig.json", &config("esnext", "react")),
                    ("tsconfig.json", &config("esnext", "react-jsx")),
                ],
                |i, out| {
                    assert!(
                        out.contains("Found 0 errors. Watching for file changes."),
                        "edit {i}: {out}"
                    );
                    let expected = match i {
                        // s1.ts v2.
                        0 => (1, 0),
                        // The `module` and `jsx` edits give no file other
                        // module indicator options (Go
                        // `GetExternalModuleIndicatorOptions`): both kept
                        // parses are used again, nothing is parsed. Before,
                        // each of these edits dropped the kept s1.ts.
                        1 | 2 => (1, 0),
                        // react-jsx gives every file the `jsx` option:
                        // s1.ts is parsed again and its kept v2 goes. The
                        // kept m1.ts did not read it, so it stays.
                        _ => (2, 1),
                    };
                    assert_eq!(file_versions(expected.1), expected, "edit {i}");
                },
            );
        },
    );
}

#[test]
fn build_watch_reset_status_lets_go_of_held_versions() {
    run_test_in_child(
        "tsctests::watch_build_kept_versions::build_watch_reset_status_lets_go_of_held_versions",
        || {
            let project = |references: &str| {
                format!(
                    r#"{{"compilerOptions":{{"composite":true,"strict":true,"target":"es2015","module":"esnext","lib":["es5"],"types":[],"rootDir":"src","outDir":"out"}}{references},"include":["src"]}}"#
                )
            };
            let core = project("");
            let app = project(r#","references":[{"path":"../core"}]"#);
            let b_error = "app/src/b.ts(1,14): error TS2322: Type 'string' is not assignable to type 'number'.";
            let a_error = "core/src/a.ts(1,14): error TS2322: Type 'string' is not assignable to type 'number'.";
            session(
                &[
                    (
                        "tsconfig.json",
                        r#"{"files":[],"references":[{"path":"./core"},{"path":"./app"}]}"#,
                    ),
                    ("core/tsconfig.json", &core),
                    ("app/tsconfig.json", &app),
                    ("core/src/a.ts", "export const a: number = 1;\n"),
                    ("app/src/b.ts", "export const b: number = 1;\n"),
                ],
                &[
                    "--build",
                    "--watch",
                    "--pretty",
                    "false",
                    "--stopBuildOnErrors",
                ],
                &[
                    ("app/src/b.ts", "export const b: number = \"one\";\n"),
                    ("core/src/a.ts", "export const a: number = \"one\";\n"),
                    ("app/src/b.ts", "export const b: number = \"two\";\n"),
                ],
                |i, out| {
                    // Go: b.ts v2 has the error of `app`, then `core` has
                    // one too, then `app` is reset by the b.ts edit and
                    // skipped (its dependency has errors), so its errors
                    // and b.ts are not read again.
                    let (a, b, found) = match i {
                        0 => (false, true, "Found 1 error."),
                        1 => (true, true, "Found 2 errors."),
                        _ => (true, false, "Found 1 error."),
                    };
                    assert_eq!(out.contains(a_error), a, "edit {i}: {out}");
                    assert_eq!(out.contains(b_error), b, "edit {i}: {out}");
                    assert!(out.contains(found), "edit {i}: {out}");
                    // b.ts v2, then a.ts v2. The edit of b.ts drops its
                    // kept parse, and `reset_status` the errors of `app`
                    // that held it, so it dies.
                    let expected = [(1, 0), (2, 0), (2, 1)][i];
                    assert_eq!(file_versions(expected.1), expected, "edit {i}");
                },
            );
        },
    );
}
