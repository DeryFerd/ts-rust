#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cargo_capped="${script_dir}/run-cargo-capped.sh"

"$cargo_capped" fmt --all -- --check
"$cargo_capped" run --quiet -p ts_ast_codegen -- check crates/ts_goport/src/astdata/syntax_kind.rs
"$cargo_capped" run --quiet -p ts_ast_codegen -- check-ast crates/ts_goport/src/astdata/ast_generated.rs
"$cargo_capped" test --workspace
"$cargo_capped" clippy --workspace --all-targets -- -D warnings
