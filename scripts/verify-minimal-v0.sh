#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cargo_capped="${script_dir}/run-cargo-capped.sh"

git diff --check
"$cargo_capped" fmt -p ts_cli -- --check
"$cargo_capped" run --quiet -p ts_ast_codegen -- check crates/ts_ast/src/syntax_kind.rs
"$cargo_capped" run --quiet -p ts_ast_codegen -- check-ast crates/ts_ast/src/ast_generated.rs
"$cargo_capped" test --workspace --exclude ts_compiler --exclude ts_parser --exclude ts_printer
"$cargo_capped" test -p ts_parser parses_remaining_core_statements_and_expressions
"$cargo_capped" test -p ts_compiler no_check_skips_semantic_diagnostics
"$cargo_capped" clippy -p ts_cli --all-targets --no-deps -- -D warnings
"$cargo_capped" build --release -p ts_cli --bin tsgo
"${script_dir}/benchmark-minimal-v0.sh"
