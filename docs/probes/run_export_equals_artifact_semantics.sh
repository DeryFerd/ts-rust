#!/usr/bin/env bash
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
common_dir="$(git -C "$root" rev-parse --path-format=absolute --git-common-dir)"
shared_root="$(dirname -- "$common_dir")"
upstream="${TS_GO_REPO:-/home/theo/.explore/repos/microsoft__typescript-go}"
go="$shared_root/target/toolchains/go1.26.5/bin/go"
author="$shared_root/target/agent-worktrees/wave146/invocation-recovery-artifacts"
target="$shared_root/target/worktrees/wave146-invocation-recovery-artifacts/debug"
bins="$target/deps"
seed="$shared_root/target/agent-worktrees/wave147/index-warm-source-final-semantics/target/review"
out="$root/target/review"
probes="$root/docs/probes"
repair=f265222b60340c2a4de8ab8e62512b9398dc86db

if [[ "${TS_WAVE147_EXPORT_REVIEW_SCOPE:-0}" != 1 ]]; then
  exec systemd-run --user --scope --quiet --collect -p MemoryMax=4194304K -p MemorySwapMax=0 \
    env TS_WAVE147_EXPORT_REVIEW_SCOPE=1 bash "$0"
fi
# The focused Rust probe links existing libraries. No Cargo build runs here.
ulimit -c 0
ulimit -s 16384
ulimit -v 16777216
export RUST_MIN_STACK=16777216 RUST_TEST_THREADS=1
export TS_EXPORT_REVIEW_CASES="$probes/export_equals_artifact_cases.json"

check_checkout() {
  local directory="$1" expected="$2" head status
  head="$(git -C "$directory" rev-parse HEAD)"
  status="$(git -C "$directory" status --porcelain=v1)"
  [[ "$head" == "$expected" && -z "$status" ]]
}
check_sources() {
  check_checkout "$upstream" dc37b5249ab60e2bbce936f71b883e6c8136167e
  check_checkout "$upstream/_submodules/TypeScript" c3bd12d888b86f676718b16e64d7d2abcb423514
  check_checkout "$author" "$repair"
  local diff
  diff="$(git -C "$root" diff "$repair" -- crates tools tests Cargo.toml Cargo.lock)"
  [[ -z "$diff" ]]
}
check_sources
mkdir -p "$out/go-tmp"
declare -A binaries=(
  [ts_checker-2e25eb919c9ab101]=b81597ef86ce11cc935b2db9cb6a71213835da4982416d156d53fd71982c8fea
  [canonical_artifact_queries-fbcb395f7b1fbe20]=f9c2cbd1e0f7a593382a05042ce4988b02f080b7775645d15aa8e5b2f230a521
  [canonical_duplicate_member_artifacts-f441a09a14907018]=42d6020ec953a8e7c5dcdb3ef672d1ed99827cf6377f260129673bbec5e5fbc2
)
for binary in "${!binaries[@]}"; do
  actual="$(sha256sum "$bins/$binary")"
  [[ "${actual%% *}" == "${binaries[$binary]}" ]]
done
actual="$(sha256sum "$target/ts_fixture_baseline")"
[[ "${actual%% *}" == 060d7fffd445c21bc18bca781af1673f2c40fea76974b67077ee76f853ea5e50 ]]
sha256sum "$0" "$probes/export_equals_artifact_cases.json" \
  "$probes/export_equals_artifact_semantics.rs" "$probes/export_equals_artifact_semantics_test.go" \
  "$go" "$target/ts_fixture_baseline" "$bins/ts_checker-2e25eb919c9ab101" \
  "$bins/canonical_artifact_queries-fbcb395f7b1fbe20" "$bins/canonical_duplicate_member_artifacts-f441a09a14907018" \
  "$bins/libts_compiler-f60c9f72d3e3299c.rlib" "$bins/libts_checker-8b5c0f1467db51ff.rlib" \
  "$bins/libts_binder-0186bd675fcf3ec2.rlib" "$bins/libts_parser-3779bc3dbdf58c10.rlib" \
  "$author/crates/ts_checker/src/semantic/artifact_queries.rs" \
  "$author/crates/ts_checker/src/semantic/source_calls.rs" \
  "$upstream/testdata/tests/cases/compiler/invocationErrorRecovery.ts" \
  "$upstream/testdata/baselines/reference/compiler/invocationErrorRecovery.types" \
  "$upstream/testdata/baselines/reference/compiler/invocationErrorRecovery.symbols" \
  "$upstream/testdata/baselines/reference/compiler/invocationErrorRecovery.errors.txt" \
  > "$out/inputs.sha256"

timeout 900s "$bins/ts_checker-2e25eb919c9ab101" --exact --nocapture \
  semantic::source_calls::tests::namespace_import_of_merged_ambient_callable_reports_exact_ts2349_and_ts7038 \
  > "$out/rust-invocation.log" 2>&1
timeout 900s "$bins/canonical_artifact_queries-fbcb395f7b1fbe20" --nocapture > "$out/rust-artifact-controls.log" 2>&1
timeout 900s "$bins/canonical_duplicate_member_artifacts-f441a09a14907018" --nocapture > "$out/rust-duplicate-control.log" 2>&1
rg -q '^test result: ok\. 1 passed; 0 failed;' "$out/rust-invocation.log"
rg -q '^test result: ok\. 12 passed; 0 failed;' "$out/rust-artifact-controls.log"
rg -q '^test result: ok\. 1 passed; 0 failed;' "$out/rust-duplicate-control.log"
timeout 900s env TS_GO_REPO="$upstream" "$target/ts_fixture_baseline" \
  --diagnostics --canonical-checker --semantic-artifacts --filter invocationErrorRecovery.ts \
  --scorecard-json "$out/invocation.json" > "$out/invocation.log" 2>&1
printf 'Fourteen reused controls and the original full-artifact fixture pass.\n'

timeout 900s rustc --edition=2024 "$probes/export_equals_artifact_semantics.rs" \
  -C debuginfo=0 -C llvm-args=--threads=1 -C link-arg=-Wl,--threads=1 \
  -L "dependency=$bins" --extern "ts_compiler=$bins/libts_compiler-f60c9f72d3e3299c.rlib" \
  --extern "ts_options=$bins/libts_options-b7145f261a256de8.rlib" \
  --extern "ts_ast=$bins/libts_ast-4ed79ba9a0a27d3b.rlib" \
  --extern "ts_checker=$bins/libts_checker-8b5c0f1467db51ff.rlib" \
  --extern "ts_binder=$bins/libts_binder-0186bd675fcf3ec2.rlib" \
  --extern "ts_parser=$bins/libts_parser-3779bc3dbdf58c10.rlib" \
  --extern "ts_vfs=$bins/libts_vfs-ecc8b1ae8eda6cef.rlib" \
  --extern "serde_json=$bins/libserde_json-71bbf7c18e47bc98.rlib" \
  -o "$out/rust-probe" > "$out/rust-probe-build.log" 2>&1
timeout 900s "$out/rust-probe" > "$out/rust-observations.json" 2> "$out/rust-probe.log"

if [[ ! -d "$out/go-cache" ]]; then
  cp -a --reflink=auto "$seed/go-cache" "$out/go-cache"
fi
if [[ ! -d "$out/go-mod-cache" ]]; then
  cp -a --reflink=auto "$seed/go-mod-cache" "$out/go-mod-cache"
fi
cp "$upstream/go.mod" "$out/go.mod"
cp "$upstream/go.sum" "$out/go.sum"
jq -n --arg upstream "$upstream" --arg probes "$probes" '{Replace:{
  ($upstream+"/internal/checker/zz_wave147_export_equals_test.go"):($probes+"/export_equals_artifact_semantics_test.go")
}}' > "$out/overlay.json"
go_env=(GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off GOWORK=off GOFLAGS= GOMAXPROCS=1 \
  GOMEMLIMIT=3145728KiB GOTELEMETRY=off "GOCACHE=$out/go-cache" \
  "GOMODCACHE=$out/go-mod-cache" "GOTMPDIR=$out/go-tmp" "TS_EXPORT_REVIEW_GO_REPORT=$out/go-observations.json")
env "${go_env[@]}" "$go" -C "$upstream" mod verify -modfile "$out/go.mod" > "$out/module-verification.log" 2>&1
timeout 900s env "${go_env[@]}" "$go" -C "$upstream" test \
  -mod=readonly -modfile "$out/go.mod" -c -p 1 -overlay "$out/overlay.json" \
  -o "$out/go-probe" ./internal/checker > "$out/go-build.log" 2>&1
timeout 900s env "${go_env[@]}" "$out/go-probe" \
  -test.run '^TestWave147ExportEqualsArtifacts$' -test.count=1 -test.v -test.timeout=900s \
  > "$out/go-semantics.log" 2>&1
sha256sum "$out/rust-probe" "$out/go-probe" > "$out/executables.sha256"
sha256sum --check "$out/inputs.sha256" > "$out/input-verification.log"
check_sources
printf 'Focused Go and Rust observations complete. Original fixture and source hashes are unchanged.\n'
