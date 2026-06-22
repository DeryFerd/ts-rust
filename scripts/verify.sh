#!/usr/bin/env bash
set -euo pipefail

cargo fmt --all -- --check
cargo run --quiet -p ts_ast_codegen -- check crates/ts_ast/src/syntax_kind.rs
cargo run --quiet -p ts_ast_codegen -- check-ast crates/ts_ast/src/ast_generated.rs
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings

if [[ -n "${TS_GO_REPO:-}" ]]; then
    cargo test -p ts_fixture --test upstream_cases
fi
