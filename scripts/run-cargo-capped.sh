#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/.." && pwd)"

# A virtual-memory limit applies per process. Serializing Cargo and forcing one
# build/test worker keeps separate rustc and test processes from multiplying
# that limit across this repository.
max_memory_limit_kib=1048576
memory_limit_kib="${TS_CARGO_MEMORY_LIMIT_KIB:-$max_memory_limit_kib}"
if [[ ! "$memory_limit_kib" =~ ^[1-9][0-9]*$ ]]; then
  echo "TS_CARGO_MEMORY_LIMIT_KIB must be a positive integer" >&2
  exit 2
fi
if ((memory_limit_kib > max_memory_limit_kib)); then
  memory_limit_kib=$max_memory_limit_kib
fi

lock_id="$(printf '%s' "$repo_root" | cksum | awk '{print $1}')"
exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
flock 9

ulimit -v "$memory_limit_kib"
export CARGO_BUILD_JOBS=1
export RUST_TEST_THREADS=1
export CARGO_PROFILE_DEV_DEBUG=0
export CARGO_PROFILE_TEST_DEBUG=0
export CARGO_PROFILE_DEV_CODEGEN_UNITS="${CARGO_PROFILE_DEV_CODEGEN_UNITS:-256}"
export CARGO_PROFILE_TEST_CODEGEN_UNITS="${CARGO_PROFILE_TEST_CODEGEN_UNITS:-256}"
unset CARGO_ENCODED_RUSTFLAGS
export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }-C debuginfo=0 -C link-arg=-Wl,--threads=1"

exec cargo "$@"
