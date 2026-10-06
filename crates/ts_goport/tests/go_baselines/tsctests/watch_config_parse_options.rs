//! Port-only test of the parses that `tsc --watch` and `tsc -b --watch`
//! keep after a config change that changes module indicator options
//! (watchcfg1 round b).
//!
//! PORT: Go parses every file again after a config change (execute/watcher.go
//! doBuild, build/orchestrator.go resetCaches). The port keeps a parse whose
//! text is the same and whose parse did not read the module indicator
//! options that changed (`parser::parse_with_options`): a file with an
//! import or export. It keeps it as a copy with the new options, because a
//! later fast path parses the edited file with them (Go
//! `oldFile.ParseOptions()`, execute/watcher.go:558). A file with no import
//! or export reads them, so it is parsed again.
//!
//! The expected errors are those of `tsgo-oracle-673a5f17d713 -w` and
//! `-b -w` on the same files with the OS watcher (watchcfg1 lane dir,
//! `fixtures/mdreuse`, `ops/mdreuse.json`): only the build after the
//! second config change reports the two TS2451 errors.

use ts_goport::fswatch::{Event, EventKind};
use ts_goport::gostd::context;

use crate::support::child::{command_line_in_process, new_in_process_test_sys, run_test_in_child};
use crate::support::runner::TscInput;

const PROJECT: &str = "/home/src/workspaces/project";

fn config(module_detection: &str) -> String {
    format!(
        r#"{{"compilerOptions":{{"moduleDetection":"{module_detection}","module":"esnext","outDir":"out","rootDir":"src","strict":true}},"include":["src"]}}"#
    )
}

/// Runs the session with `args` and checks the errors of each build.
fn run(args: &[&str]) {
    let file = |name: &str, text: &str| (format!("{PROJECT}/{name}"), text.into());
    let input = TscInput {
        files: [
            file("tsconfig.json", &config("legacy")),
            file("src/c.ts", "export {};\nconst x = 2;\n"),
            file("src/d.ts", "export {};\nconst x = 3;\n"),
        ]
        .into_iter()
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
    let redeclared = "error TS2451: Cannot redeclare block-scoped variable 'x'.";
    let force = config("force");
    let legacy = config("legacy");
    // (file, text, the errors of the build)
    let edits: [(&str, &str, usize); 5] = [
        // c.ts and d.ts keep their parses, as copies with `force`.
        ("tsconfig.json", &force, 0),
        // The fast path parses the edited files with `force` (a copy with
        // the old options would make both scripts and report TS2451).
        ("src/c.ts", "const x = 2;\n", 0),
        ("src/d.ts", "const x = 3;\n", 0),
        // Their parses read the module indicator options now, so they are
        // parsed again: two scripts.
        ("tsconfig.json", &legacy, 2),
        ("tsconfig.json", &force, 0),
    ];
    for (i, (path, text, errors)) in edits.into_iter().enumerate() {
        sys.set_output_bytes(Vec::new());
        let _ = fs.write_file(&format!("{PROJECT}/{path}"), text);
        sys.mock_watch_backend().send_events(vec![Event {
            kind: EventKind::Update,
            path: format!("{PROJECT}/{path}"),
        }]);
        w.do_cycle();
        let out = sys.output_text();
        let summary = match errors {
            0 => "Found 0 errors. Watching for file changes.".to_string(),
            n => format!("Found {n} errors. Watching for file changes."),
        };
        assert!(
            out.contains(&summary) && out.matches(redeclared).count() == errors,
            "edit {i} ({path}) reports {errors} TS2451 errors: {out}"
        );
    }
}

#[test]
fn watch_keeps_parses_that_did_not_read_module_indicator_options() {
    run_test_in_child(
        "tsctests::watch_config_parse_options::watch_keeps_parses_that_did_not_read_module_indicator_options",
        || run(&["--watch", "--pretty", "false"]),
    );
}

#[test]
fn build_watch_keeps_parses_that_did_not_read_module_indicator_options() {
    run_test_in_child(
        "tsctests::watch_config_parse_options::build_watch_keeps_parses_that_did_not_read_module_indicator_options",
        || run(&["--build", "--watch", "--pretty", "false"]),
    );
}
