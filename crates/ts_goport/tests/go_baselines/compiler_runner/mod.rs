//! Rust port of the pinned typescript-go compiler runner
//! (`internal/testrunner`): `TestLocal` and `TestSubmodule` compare the
//! `.errors.txt`, `.contentmapper` (tsgo#4712), `.js`, `.js.map`,
//! `.sourcemap.txt`, `.types`, `.symbols` and `.trace.json` baselines of
//! every compiler and conformance case with `testdata/baselines/reference`
//! of the Go checkout, byte for byte.
//!
//! Two layouts (`support::baseline::is_merged_layout`):
//! - typescript-go (pin B and older): `TestLocal` runs the cases of
//!   `testdata/tests/cases`, `TestSubmodule` the cases of
//!   `_submodules/TypeScript/tests/cases` against `reference/submodule`
//!   and writes `.diff` files against the submodule's baselines.
//! - microsoft/TypeScript `tsc/` (5f647a841a, "Apply the TypeScript 7
//!   repository layout"): the submodule cases are in `testdata/tests/cases`,
//!   `TestLocal` runs all of them against `reference/<suite>`, there is no
//!   `TestSubmodule` (`test_submodule` skips) and there are no `.diff` files.
//!
//! Files:
//! - `runner.rs`: compiler_runner.go (the runner, the test cases, the
//!   subtests).
//! - `test_case_parser.rs`: test_case_parser.go and its test.
//! - `harness.rs`: the harnessutil parts that `support::harnessutil` does
//!   not have (`CompileFiles`, options, configurations) and recorderfs.go.
//! - `sourcemap_recorder.rs`: sourcemap_recorder.go and
//!   `GetSourceMapRecord`.
//! - `tsbaseline.rs`: testutil/tsbaseline (error, content mapper, js emit,
//!   source map, source map record, module resolution, the type and symbol
//!   wrappers). The test content mappers are `support::contentmappertest`.
//! - `go_regex.rs`: the Go regular expressions as plain matchers.
//! - `child.rs`: each test configuration runs in a child process; the
//!   environment variables and `known_failures.txt` are described there.
//! - `transpile_runner.rs`: transpile_runner.go (`TestTranspile`, #4849):
//!   the `submodule/transpile` (merged layout: `transpile`) baselines of
//!   `ts_goport::transpile`.
//!
//! Run: `scripts/run-cargo-capped.sh test --release -p ts_goport --test
//! go_baselines -- compiler_runner` (TestLocal and TestTranspile).
//! TestSubmodule is ignored (long): run it with `--include-ignored
//! compiler_runner::test_submodule` and `COMPILER_RUNNER_SHARD=<i>/<n>`.
//! At the merged layout `TestLocal` has every case (about 12,700 files),
//! so run it in shards the same way.

mod child;
mod go_regex;
mod harness;
mod runner;
mod sourcemap_recorder;
mod test_case_parser;
mod transpile_runner;
mod tsbaseline;

// Go: compiler_runner_test.go:14 TestLocal
// Runs the new compiler tests and produces baselines (e.g. `test1.symbols`).
#[test]
fn test_local() {
    child::run_compiler_tests(false);
}

// Go: compiler_runner_test.go:18 TestSubmodule
// Runs the old compiler tests, and produces new baselines (e.g. `test1.symbols`)
// and a diff between the new and old baselines (e.g. `test1.symbols.diff`).
// Typescript-go layout only: it skips at the merged layout.
#[test]
#[ignore = "long: about 15,000 child processes; run in shards (COMPILER_RUNNER_SHARD)"]
fn test_submodule() {
    child::run_compiler_tests(true);
}

// Go: transpile_runner_test.go:5 TestTranspile
#[test]
fn test_transpile() {
    transpile_runner::run_transpile_tests();
}

/// Child process entry of the compiler runner. Returns at once unless the
/// runner started it.
#[test]
fn __compiler_runner_child() {
    child::child_entry();
}
