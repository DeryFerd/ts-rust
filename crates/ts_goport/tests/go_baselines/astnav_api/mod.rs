//! Ports of the typescript-go astnav and api tests. They use the
//! `ts_goport::astnav`, `ts_goport::api::encoder` and `ts_goport::api::proto`
//! modules and the `frontend::json_ext` helpers.
//!
//! - `jstest`: internal/testutil/jstest/node.go (runs Node.js scripts).
//! - `astnav_tokens`: internal/astnav/tokens_test.go (astnav baselines).
//! - `api_proto`: internal/api/proto_test.go.
//! - `api_encoder`: internal/api/encoder/{encoder,decoder}_test.go (api baselines).
//!
//! PORT: Go `t.Run` subtests run in order through `Subtests` (Go
//! `t.Parallel()` is dropped). Each Go `Test` function is one `#[test]`.
//! Go `t.Skip` prints a `SKIP` line and returns. Go benchmarks are not
//! ported.

mod api_encoder;
mod api_proto;
mod astnav_tokens;
pub(crate) mod jstest;

use std::any::Any;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// Go `t.Run` subtests of one Go test function. A subtest fails when its
/// closure returns `Err` or panics (Go `t.Fatal`, `t.Errorf`, `assert.*`).
/// `finish` panics once with every failure.
pub(crate) struct Subtests {
    test: &'static str,
    ran: usize,
    failures: Vec<String>,
}

impl Subtests {
    pub(crate) fn new(test: &'static str) -> Subtests {
        Subtests {
            test,
            ran: 0,
            failures: Vec::new(),
        }
    }

    /// Go `t.Run(name, f)`. A nested Go name is joined with "/".
    pub(crate) fn run(&mut self, name: &str, f: impl FnOnce() -> Result<(), String>) {
        self.ran += 1;
        let result = match catch_unwind(AssertUnwindSafe(f)) {
            Ok(result) => result,
            Err(payload) => Err(format!("panic: {}", panic_message(payload.as_ref()))),
        };
        if let Err(message) = result {
            self.failures
                .push(format!("--- FAIL: {}/{name}\n{message}", self.test));
        }
    }

    pub(crate) fn finish(self) {
        if !self.failures.is_empty() {
            panic!(
                "{} of {} subtests of {} failed:\n\n{}",
                self.failures.len(),
                self.ran,
                self.test,
                self.failures.join("\n\n")
            );
        }
    }
}

/// The message of a caught panic.
pub(crate) fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        return (*s).to_string();
    }
    if let Some(s) = payload.downcast_ref::<String>() {
        return s.clone();
    }
    "<non-string panic payload>".to_string()
}

/// The parts of internal/repo/paths.go that these tests use.
pub(crate) mod repo {
    use std::path::PathBuf;

    // Go: repo/paths.go:42 RootPath
    // PORT: Go finds go.mod above the test source file. The port uses the
    // pinned typescript-go checkout (env TS_GO_REPO).
    pub(crate) fn root_path() -> PathBuf {
        crate::support::baseline::go_repo()
    }

    // Go: repo/paths.go:50 TypeScriptSubmodulePath
    pub(crate) fn type_script_submodule_path() -> PathBuf {
        root_path().join("_submodules").join("TypeScript")
    }

    // Go: repo/paths.go:62 typeScriptSubmoduleExists
    pub(crate) fn type_script_submodule_exists() -> bool {
        let p = type_script_submodule_path().join("package.json");
        match std::fs::metadata(&p) {
            Ok(_) => true,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => false,
            Err(err) => panic!("{err}"),
        }
    }

    // Go: repo/paths.go:82 SkipIfNoTypeScriptSubmodule
    /// True (after it prints the skip reason) when the test must return.
    pub(crate) fn skip_if_no_type_script_submodule(test: &str) -> bool {
        if !type_script_submodule_exists() {
            println!("SKIP {test}: TypeScript submodule does not exist");
            return true;
        }
        false
    }
}
