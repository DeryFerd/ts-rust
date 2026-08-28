#!/usr/bin/env bash
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
common="$(git -C "$root" rev-parse --path-format=absolute --git-common-dir)"
shared_root="$(dirname -- "$common")"
upstream="${TS_GO_REPO:-/home/theo/.explore/repos/microsoft__typescript-go}"
go="$shared_root/target/toolchains/go1.26.5/bin/go"
out="$root/target/review-merged-class-exports"
cases="$root/docs/probes/merged_class_export_cases.json"
probe="$root/docs/probes/merged_class_export_semantics_test.go"

if [[ "${TS_MERGED_EXPORT_GO_SCOPE:-0}" != 1 ]]; then
  exec systemd-run --user --scope --quiet --collect \
    -p MemoryMax=16777216K -p MemorySwapMax=0 \
    env TS_MERGED_EXPORT_GO_SCOPE=1 bash "$0"
fi

lock_seed="${TS_CARGO_LOCK_ID:-$common}"
lock_id="$(printf '%s' "$lock_seed" | cksum | awk '{print $1}')"
exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
flock 9
ulimit -c 0
ulimit -s 16384
ulimit -v 67108864

check_upstream() {
  [[ "$(git -C "$upstream" rev-parse HEAD)" == dc37b5249ab60e2bbce936f71b883e6c8136167e ]]
  [[ -z "$(git -C "$upstream" status --porcelain=v1)" ]]
  [[ -z "$(git -C "$upstream/_submodules/TypeScript" status --porcelain=v1)" ]]
}

check_upstream
mkdir -p "$out/go-cache" "$out/go-tmp"
sha256sum "$0" "$cases" "$probe" "$go" "$upstream/go.mod" "$upstream/go.sum" \
  > "$out/go-inputs.sha256"
jq -n --arg target "$upstream/internal/checker/zz_wave152_merged_class_exports_test.go" \
  --arg source "$probe" '{Replace:{($target):$source}}' > "$out/go-overlay.json"

export GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off GOWORK=off GOFLAGS=
export GOMAXPROCS=1 GOMEMLIMIT=15032385536 GOTELEMETRY=off
export GOCACHE="$out/go-cache" GOMODCACHE=/home/theo/go/pkg/mod GOTMPDIR="$out/go-tmp"
export TS_MERGED_EXPORT_CASES="$cases"
export TS_MERGED_EXPORT_GO_REPORT="$out/go-observations.json"

build_status=0
timeout 900s "$go" -C "$upstream" test -mod=readonly -vet=off -p 1 \
  -overlay "$out/go-overlay.json" -c -o "$out/go-observer" ./internal/checker \
  > "$out/go-build.log" 2>&1 || build_status=$?
if ((build_status != 0)); then
  sha256sum --check "$out/go-inputs.sha256" > "$out/go-input-check.log"
  check_upstream
  exit "$build_status"
fi
run_status=0
timeout 900s "$out/go-observer" -test.run '^TestWave152MergedClassExportSemantics$' \
  -test.count=1 -test.parallel=1 -test.v -test.timeout=900s \
  > "$out/go-run.log" 2>&1 || run_status=$?
sha256sum --check "$out/go-inputs.sha256" > "$out/go-input-check.log"
check_upstream
sha256sum "$out/go-observer" "$out/go-observations.json" > "$out/go-results.sha256"
printf 'Pinned Go merged-class observations completed. Upstream remains clean.\n'
exit "$run_status"
