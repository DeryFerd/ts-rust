#!/usr/bin/env bash
set -euo pipefail

: "${TS_GO_REPO:?TS_GO_REPO must point to the typescript-go checkout}"

# Fixture recovery bugs can otherwise grow until the machine OOMs. Keep this
# hard ceiling below the host limit so a bad case fails locally and predictably.
ulimit -v 8388608

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
timeout_seconds="${TS_FIXTURE_TIMEOUT_SECONDS:-120}"

exec timeout "${timeout_seconds}s" cargo run --quiet -p ts_fixture \
  --bin ts_fixture_baseline -- "$@"
