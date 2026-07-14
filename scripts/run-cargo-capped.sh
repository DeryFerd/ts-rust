#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/.." && pwd)"

# A virtual-memory limit applies per process. Serializing Cargo and forcing one
# build/test worker keeps separate rustc and test processes from multiplying
# that limit across this repository.
max_memory_limit_kib=1048576
# LLVM reserves substantially more address space than it commits as resident
# memory. Keep that reservation bounded without making it compete with the
# cgroup's stricter 1 GiB aggregate RAM limit.
max_virtual_memory_limit_kib=4194304
memory_limit_kib="${TS_CARGO_MEMORY_LIMIT_KIB:-$max_memory_limit_kib}"
if [[ ! "$memory_limit_kib" =~ ^[1-9][0-9]*$ ]]; then
  echo "TS_CARGO_MEMORY_LIMIT_KIB must be a positive integer" >&2
  exit 2
fi
if ((memory_limit_kib > max_memory_limit_kib)); then
  memory_limit_kib=$max_memory_limit_kib
fi

# Worktrees share object storage but have different repository roots. Derive the
# lock from their common Git directory so parallel agents cannot accidentally
# start one 1 GiB Cargo scope per worktree. An explicit ID remains useful for
# non-Git copies that should join the same build queue.
if [[ -n "${TS_CARGO_LOCK_ID:-}" ]]; then
  lock_seed="$TS_CARGO_LOCK_ID"
elif git_common_dir="$(
  git -C "$repo_root" rev-parse --path-format=absolute --git-common-dir 2>/dev/null
)"; then
  lock_seed="$git_common_dir"
else
  lock_seed="$repo_root"
fi
lock_id="$(printf '%s' "$lock_seed" | cksum | awk '{print $1}')"

# Limit the aggregate memory of Cargo and every process it starts. The existing
# virtual-memory limit below remains as a second line of defense for individual
# rustc and test processes.
if [[ "${TS_CARGO_CGROUP_ACTIVE:-0}" != 1 ]]; then
  exec systemd-run --user --scope --quiet --collect \
    -p "MemoryMax=${memory_limit_kib}K" \
    -p MemorySwapMax=0 \
    env TS_CARGO_CGROUP_ACTIVE=1 TS_CARGO_MEMORY_LIMIT_KIB="$memory_limit_kib" \
    "$0" "$@"
fi

exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
flock 9

ulimit -v "$max_virtual_memory_limit_kib"
ulimit -c 0
export CARGO_BUILD_JOBS=1
export CARGO_INCREMENTAL=0
export RUST_TEST_THREADS=1
export CARGO_PROFILE_DEV_DEBUG=0
export CARGO_PROFILE_TEST_DEBUG=0
export CARGO_PROFILE_DEV_CODEGEN_UNITS="${CARGO_PROFILE_DEV_CODEGEN_UNITS:-256}"
export CARGO_PROFILE_TEST_CODEGEN_UNITS="${CARGO_PROFILE_TEST_CODEGEN_UNITS:-256}"
unset CARGO_ENCODED_RUSTFLAGS
export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }-C debuginfo=0 -C llvm-args=--threads=1 -C link-arg=-Wl,--threads=1"

exec cargo "$@"
