//! Rust port of the pinned typescript-go baseline tests: execute/tsctests
//! (tsc, tsbuild, tscWatch, tsbuildWatch), tsoptions, config, astnav and
//! api. Each generated baseline is compared byte for byte with
//! `testdata/baselines/reference` of the Go checkout.
//!
//! Run: `scripts/run-cargo-capped.sh test --release -p ts_goport --test go_baselines`.
//! `test = false` keeps it out of `cargo test --workspace`: it needs the Go
//! checkout (`TS_GO_REPO`, see `support::baseline`).
//! `TS_GOPORT_BASELINE_LOCAL=1` also writes each generated baseline under
//! `support::baseline::DEFAULT_LOCAL_ROOT`. `TSCTEST_FILTER` and
//! `TSCTEST_JOBS` select and run tsc inputs (see `support::runner`).

// The support modules port whole Go packages; the tests use only part of
// them. The Go-shaped code does not follow the workspace's pedantic lints,
// and keeps Go's nested `if`s and inline function types.
#![allow(
    clippy::pedantic,
    clippy::collapsible_if,
    clippy::type_complexity,
    dead_code
)]
mod astnav_api;
mod compiler_runner;
mod project_lsp;
mod support;
mod tsctests;
mod tsoptions;
mod units_emit;
mod units_platform;

/// Child process entry of the tsc runner. Returns at once unless the runner started it.
#[test]
fn __tsctest_child() {
    support::child::command_child_entry();
}
