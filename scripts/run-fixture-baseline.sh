#!/usr/bin/env bash
set -euo pipefail

: "${TS_GO_REPO:?TS_GO_REPO must point to the typescript-go checkout}"

# Fixture recovery bugs can otherwise grow until the machine OOMs. Keep every
# run at or below 1 GiB so a bad case fails locally and predictably. The
# environment variable may lower the limit, but cannot raise the hard ceiling.
max_memory_limit_kib=1048576
memory_limit_kib="${TS_FIXTURE_MEMORY_LIMIT_KIB:-$max_memory_limit_kib}"
if [[ ! "$memory_limit_kib" =~ ^[1-9][0-9]*$ ]]; then
  echo "TS_FIXTURE_MEMORY_LIMIT_KIB must be a positive integer" >&2
  exit 2
fi
if (( memory_limit_kib > max_memory_limit_kib )); then
  memory_limit_kib=$max_memory_limit_kib
fi
ulimit -v "${memory_limit_kib}"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }-C link-arg=-Wl,--threads=1"
timeout_seconds="${TS_FIXTURE_TIMEOUT_SECONDS:-120}"

exec timeout "${timeout_seconds}s" cargo run --quiet -p ts_fixture \
  --bin ts_fixture_baseline -- "$@"
