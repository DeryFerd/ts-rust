#!/usr/bin/env bash
set -euo pipefail

: "${TS_GO_REPO:?TS_GO_REPO must point to the typescript-go checkout}"

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export TS_CARGO_MEMORY_LIMIT_KIB="${TS_FIXTURE_MEMORY_LIMIT_KIB:-1048576}"
timeout_seconds="${TS_FIXTURE_TIMEOUT_SECONDS:-120}"

exec timeout "${timeout_seconds}s" "${script_dir}/run-cargo-capped.sh" \
  run --quiet -p ts_fixture \
  --bin ts_fixture_baseline -- "$@"
