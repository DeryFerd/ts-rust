#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cargo_capped="${script_dir}/run-cargo-capped.sh"

"$cargo_capped" fmt --all -- --check
"$cargo_capped" run --quiet -p ts_ast_codegen -- check crates/ts_ast/src/syntax_kind.rs
"$cargo_capped" run --quiet -p ts_ast_codegen -- check-ast crates/ts_ast/src/ast_generated.rs
"$cargo_capped" test --workspace
"$cargo_capped" clippy --workspace --all-targets -- -D warnings

if [[ -n "${TS_GO_REPO:-}" ]]; then
    "$cargo_capped" test -p ts_fixture --test upstream_cases
fi
