#!/usr/bin/env bash
set -euo pipefail

if (($# != 4)); then
  printf 'Usage: %s GO UPSTREAM OUTPUT MODULE_CACHE\n' "$0" >&2
  exit 2
fi
go=$1
upstream=$2
out=$3
modules=$4
for path in "$go" "$upstream" "$out" "$modules"; do
  if [[ "$path" != /* ]]; then exit 2; fi
done
upstream="$(realpath -- "$upstream")"
modules="$(realpath -- "$modules")"
out_real="$(realpath -m -- "$out")"
case "$out_real/" in "$upstream/"*) exit 2 ;; esac
case "$modules/" in "$upstream/"*) exit 2 ;; esac
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root="$(git -C "$script_dir" rev-parse --show-toplevel)"
pin=dc37b5249ab60e2bbce936f71b883e6c8136167e
memory=${TS_CARGO_MEMORY_LIMIT_KIB:-16777216}
if [[ ! "$memory" =~ ^[1-9][0-9]*$ ]]; then exit 2; fi
if [[ "${TS_CLASS_ADMISSION_SCOPE:-0}" != 1 ]]; then
  exec systemd-run --user --scope --quiet --collect \
    -p "MemoryMax=${memory}K" -p MemorySwapMax=0 \
    env TS_CLASS_ADMISSION_SCOPE=1 bash "$0" "$@"
fi
lock_seed="${TS_CARGO_LOCK_ID:-$(git -C "$root" rev-parse --path-format=absolute --git-common-dir)}"
lock_id="$(printf '%s' "$lock_seed" | cksum | awk '{print $1}')"
exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
flock 9
ulimit -c 0
ulimit -s 16384

test "$(git -C "$upstream" rev-parse HEAD)" = "$pin"
test -z "$(git -C "$upstream" status --porcelain=v1)"
test ! -e "$upstream/internal/compiler/class_admission_expectations_test.go"
if [[ -e "$out" || -L "$out" ]]; then
  printf 'Output must be new: %s\n' "$out" >&2
  exit 2
fi
mkdir -p "$out/go-cache" "$out/go-tmp"
cp "$upstream/go.mod" "$out/go.mod"
cp "$upstream/go.sum" "$out/go.sum"
jq -n --arg upstream "$upstream" --arg source "$script_dir/admission_test.go" \
  '{Replace:{($upstream+"/internal/compiler/class_admission_expectations_test.go"):$source}}' \
  > "$out/overlay.json"
sha256sum "$go" "$script_dir/admission_test.go" "$script_dir/run.sh" \
  "$upstream/go.mod" "$upstream/go.sum" > "$out/inputs.sha256"
version="$("$go" version)"
test "$version" = "go version go1.26.5 linux/amd64"
printf '%s\n' "$version" > "$out/go-version.txt"
git -C "$upstream" rev-parse HEAD > "$out/upstream.sha"
git -C "$root" rev-parse HEAD > "$out/rust.sha"
git -C "$root" status --porcelain=v1 > "$out/rust-status.txt"

status=0
timeout --signal=TERM --kill-after=10s 600s \
  env GOTOOLCHAIN=local GOTELEMETRY=off GOPROXY=off GOSUMDB=off GOWORK=off GOFLAGS= \
    GOMAXPROCS=1 "GOMEMLIMIT=$((memory * 3 / 4))KiB" \
    "GOCACHE=$out/go-cache" "GOTMPDIR=$out/go-tmp" "GOMODCACHE=$modules" \
    "$go" -C "$upstream" test -overlay="$out/overlay.json" -modfile="$out/go.mod" \
    -mod=readonly -p=1 -count=1 -timeout=2m -run='^TestClassAdmissionRootExpectations$' \
    -v ./internal/compiler || status=$?
sha256sum --check --strict "$out/inputs.sha256"
cmp "$upstream/go.mod" "$out/go.mod"
cmp "$upstream/go.sum" "$out/go.sum"
test "$(git -C "$upstream" rev-parse HEAD)" = "$pin"
test -z "$(git -C "$upstream" status --porcelain=v1)"
exit "$status"
