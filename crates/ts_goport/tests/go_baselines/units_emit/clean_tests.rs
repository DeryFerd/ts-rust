//! Port of internal/execute/build/clean_test.go (ts#64158): the API clean
//! of the build orchestrator (`Orchestrator::clean_exported`).
//!
//! PORT: Go `cleanTestSystem` embeds `*tsctests.TestSys` and sends its
//! `Writer` and `ErrorWriter` to its own `strings.Builder`, which no test
//! reads. Here the test system writes to its own buffer, which no test
//! reads either. The clean makes no program, so the tests run in this
//! process, as the graph tests do (execute_tests.rs).

use super::{Subtests, assert_equal};
use crate::support::runner::FileMap;
use crate::support::test_sys::{TestSys, new_tsc_system};
use std::rc::Rc;
use ts_goport::execute::build::command_line::parse_build_command_line;
use ts_goport::execute::build::orchestrator::{Options, Orchestrator, new_orchestrator};
use ts_goport::execute::tsc::compile::{ExitStatus, System, SystemParseConfigHost};
use ts_goport::frontend::vfs::Fs;

/// Go `assert.Assert(t, cond)` inside a subtest.
fn check(cond: bool, what: &str) -> Result<(), String> {
    if cond {
        Ok(())
    } else {
        Err(format!("assertion failed: {what}"))
    }
}

/// Go `sys.FS().FileExists(path)`.
fn file_exists(sys: &Rc<TestSys>, path: &str) -> bool {
    System::fs(&**sys).file_exists(path)
}

// Go: execute/build/clean_test.go:15 TestClean
#[test]
fn test_clean() {
    let mut t = Subtests::new("TestClean");

    t.run("cleans selected project and references", || {
        let sys = new_clean_test_system();
        let mut orchestrator = new_clean_test_orchestrator(&sys, &["a", "c"]);

        let result = orchestrator.clean_exported("a");
        assert_equal(
            result.result.status,
            ExitStatus::Success,
            "result.Result.Status",
        )?;
        assert_equal(result.statistics.projects, 2, "result.Statistics.Projects")?;
        check(
            !file_exists(&sys, "/project/a/dist/index.js"),
            "!sys.FS().FileExists(\"/project/a/dist/index.js\")",
        )?;
        check(
            !file_exists(&sys, "/project/b/dist/index.js"),
            "!sys.FS().FileExists(\"/project/b/dist/index.js\")",
        )?;
        check(
            file_exists(&sys, "/project/c/dist/index.js"),
            "sys.FS().FileExists(\"/project/c/dist/index.js\")",
        )
    });

    t.run("dry run preserves outputs", || {
        let sys = new_clean_test_system();
        let mut orchestrator = new_clean_test_orchestrator(&sys, &["--dry", "a"]);

        let result = orchestrator.clean_exported("a");
        assert_equal(
            result.result.status,
            ExitStatus::Success,
            "result.Result.Status",
        )?;
        assert_equal(result.statistics.projects, 2, "result.Statistics.Projects")?;
        check(
            !result.files_to_delete.is_empty(),
            "len(result.FilesToDelete) > 0",
        )?;
        check(
            file_exists(&sys, "/project/a/dist/index.js"),
            "sys.FS().FileExists(\"/project/a/dist/index.js\")",
        )?;
        check(
            file_exists(&sys, "/project/b/dist/index.js"),
            "sys.FS().FileExists(\"/project/b/dist/index.js\")",
        )
    });

    t.run("rejects project outside build", || {
        let sys = new_clean_test_system();
        let mut orchestrator = new_clean_test_orchestrator(&sys, &["a"]);

        let result = orchestrator.clean_exported("c");
        assert_equal(
            result.result.status,
            ExitStatus::InvalidProjectOutputsSkipped,
            "result.Result.Status",
        )?;
        check(
            file_exists(&sys, "/project/a/dist/index.js"),
            "sys.FS().FileExists(\"/project/a/dist/index.js\")",
        )?;
        check(
            file_exists(&sys, "/project/b/dist/index.js"),
            "sys.FS().FileExists(\"/project/b/dist/index.js\")",
        )?;
        check(
            file_exists(&sys, "/project/c/dist/index.js"),
            "sys.FS().FileExists(\"/project/c/dist/index.js\")",
        )
    });

    t.run("rejects circular build", || {
        let sys = new_clean_test_system();
        let mut orchestrator = new_clean_test_orchestrator(&sys, &["cycle1"]);

        let result = orchestrator.clean_exported("cycle1");
        assert_equal(
            result.result.status,
            ExitStatus::ProjectReferenceCycleOutputsSkipped,
            "result.Result.Status",
        )?;
        check(!result.errors.is_empty(), "len(result.Errors) > 0")?;
        check(
            file_exists(&sys, "/project/cycle1/dist/index.js"),
            "sys.FS().FileExists(\"/project/cycle1/dist/index.js\")",
        )?;
        check(
            file_exists(&sys, "/project/cycle2/dist/index.js"),
            "sys.FS().FileExists(\"/project/cycle2/dist/index.js\")",
        )
    });

    t.finish();
}

// Go: execute/build/clean_test.go:79 newCleanTestSystem
fn new_clean_test_system() -> Rc<TestSys> {
    let files: FileMap = [
        (
            "/project/a/tsconfig.json",
            r#"{
			"compilerOptions": { "composite": true, "noLib": true, "outDir": "dist" },
			"files": ["index.ts"],
			"references": [{ "path": "../b" }]
		}"#,
        ),
        ("/project/a/index.ts", "export const a = 1;"),
        ("/project/a/dist/index.js", "export const a = 1;"),
        ("/project/a/dist/index.d.ts", "export declare const a = 1;"),
        (
            "/project/b/tsconfig.json",
            r#"{ "compilerOptions": { "composite": true, "noLib": true, "outDir": "dist" }, "files": ["index.ts"] }"#,
        ),
        ("/project/b/index.ts", "export const b = 1;"),
        ("/project/b/dist/index.js", "export const b = 1;"),
        ("/project/b/dist/index.d.ts", "export declare const b = 1;"),
        (
            "/project/c/tsconfig.json",
            r#"{ "compilerOptions": { "composite": true, "noLib": true, "outDir": "dist" }, "files": ["index.ts"] }"#,
        ),
        ("/project/c/index.ts", "export const c = 1;"),
        ("/project/c/dist/index.js", "export const c = 1;"),
        ("/project/c/dist/index.d.ts", "export declare const c = 1;"),
        (
            "/project/cycle1/tsconfig.json",
            r#"{
			"compilerOptions": { "composite": true, "noLib": true, "outDir": "dist" },
			"files": ["index.ts"],
			"references": [{ "path": "../cycle2" }]
		}"#,
        ),
        ("/project/cycle1/index.ts", "export const cycle1 = 1;"),
        ("/project/cycle1/dist/index.js", "export const cycle1 = 1;"),
        (
            "/project/cycle2/tsconfig.json",
            r#"{
			"compilerOptions": { "composite": true, "noLib": true, "outDir": "dist" },
			"files": ["index.ts"],
			"references": [{ "path": "../cycle1" }]
		}"#,
        ),
        ("/project/cycle2/index.ts", "export const cycle2 = 1;"),
        ("/project/cycle2/dist/index.js", "export const cycle2 = 1;"),
    ]
    .into_iter()
    .map(|(path, text)| (path.to_string(), text.into()))
    .collect();
    Rc::new(new_tsc_system(files, true, "/project"))
}

// Go: execute/build/clean_test.go:118 newCleanTestOrchestrator
fn new_clean_test_orchestrator(sys: &Rc<TestSys>, args: &[&str]) -> Orchestrator {
    let mut command_line_args = vec!["--build".to_string()];
    command_line_args.extend(args.iter().map(|arg| arg.to_string()));
    let command = parse_build_command_line(&command_line_args, &SystemParseConfigHost(&**sys));
    new_orchestrator(Options {
        sys: sys.clone() as Rc<dyn System>,
        command: Rc::new(command),
        testing: None,
    })
}
