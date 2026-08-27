#!/usr/bin/env bash
set -euo pipefail

if (($# < 4 || $# > 5)); then printf 'Usage: %s GO UPSTREAM CONFIG OUT [controls|run]\n' "$0" >&2; exit 2; fi
go=$1
upstream=$2
config=$3
out=$4
mode=${5:-run}
case "$mode" in controls|run) ;; *) exit 2 ;; esac
for argument in "$go" "$upstream" "$config" "$out"; do [[ "$argument" == /* ]] || exit 2; done
# A trailing slash or '.' still names the same final entry.
out_entry=$out
while [[ "$(basename -- "$out_entry")" == "." ]]; do
  out_entry="$(dirname -- "$out_entry")"
done
# Resolve only the parent before testing that entry for a symlink.
out_entry="$(realpath -m -- "$(dirname -- "$out_entry")")/$(basename -- "$out_entry")"
if [[ -L "$out_entry" || -e "$out_entry" ]]; then
  printf 'Output must not already exist: %s\n' "$out_entry" >&2
  exit 2
fi
# Preparation and later writers must use the same destination.
out="$(realpath -m -- "$out_entry")"
phase_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd -- "$phase_dir/../../../.." && pwd)"
memory_kib=${TS_GO_ORACLE_MEMORY_LIMIT_KIB:-16777216}
timeout_seconds=${TS_GO_ORACLE_TIMEOUT_SECONDS:-600}
[[ "$memory_kib" =~ ^[1-9][0-9]*$ && "$timeout_seconds" =~ ^[1-9][0-9]*$ ]] || exit 2
if [[ "${TS_PHASE_ORACLE_CGROUP_ACTIVE:-0}" != 1 ]]; then
  exec systemd-run --user --scope --quiet --collect -p "MemoryMax=${memory_kib}K" -p MemorySwapMax=0 \
    env TS_PHASE_ORACLE_CGROUP_ACTIVE=1 TS_GO_ORACLE_MEMORY_LIMIT_KIB="$memory_kib" bash "$phase_dir/run.sh" "$@"
fi
lock_seed="${TS_CARGO_LOCK_ID:-$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir)}"
lock_id="$(printf '%s' "$lock_seed" | cksum | awk '{print $1}')"
exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
flock 9
ulimit -c 0
hash_file() { local hash ignored; read -r hash ignored < <(sha256sum -- "$1"); printf '%s' "$hash"; }
git -C "$repo" diff --exit-code ace916f6bf0ca2c31cf8bd49a21628eabc4d9b76 -- scripts/run-go-project-oracle.sh
git -C "$repo" diff --exit-code a84de244261ba1389603494fb7b97d510154355a -- \
  tools/ts_fixture/go_project_oracle/project_oracle_test.go.txt tools/ts_fixture/go_project_oracle/project_graph_test.go.txt \
  tools/ts_fixture/go_project_oracle/baseline_hooks.go.txt tools/ts_fixture/go_project_oracle/baseline_hooks.patch \
  tools/ts_fixture/go_project_oracle/checker_replay.go.txt
bash "$repo/scripts/run-go-project-oracle.sh" "$go" "$upstream" "$config" "$out" prepare
cp "$phase_dir/hooks.go.txt" "$out/overlay/phase_hooks.go"
cp "$phase_dir/oracle_test.go.txt" "$out/overlay/phase_oracle_test.go"
cp "$phase_dir/controls_test.go.txt" "$out/overlay/phase_controls_test.go"
base_renderer_hash="$(hash_file "$out/overlay/type_symbol_baseline.go")"
patch --batch --fuzz=0 --reject-file=- --output="$out/overlay/phase_type_symbol_baseline.go" \
  "$out/overlay/type_symbol_baseline.go" "$phase_dir/queries.patch" >"$out/phase-patch.log"
jq --arg upstream "$upstream" --arg out "$out" '
  .Replace[($upstream+"/internal/testutil/tsbaseline/type_symbol_baseline.go")] = ($out+"/overlay/phase_type_symbol_baseline.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_phase_hooks.go")] = ($out+"/overlay/phase_hooks.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_phase_oracle_test.go")] = ($out+"/overlay/phase_oracle_test.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_phase_controls_test.go")] = ($out+"/overlay/phase_controls_test.go")
' "$out/overlay.json" >"$out/overlay-next.json"
mv "$out/overlay-next.json" "$out/overlay.json"
while IFS=$'\t' read -r original replacement; do
  original_sha=null
  if [[ -e "$original" ]]; then original_sha="\"$(hash_file "$original")\""; fi
  jq -n --arg original "$original" --arg replacement "$replacement" --arg sha256 "$(hash_file "$replacement")" --argjson original_sha "$original_sha" \
    '{original_path:$original,replacement_path:$replacement,sha256:$sha256,original_sha256:$original_sha}'
done < <(jq -r '.Replace | to_entries[] | [.key,.value] | @tsv' "$out/overlay.json") | jq -s . >"$out/phase-overlay-sources.json"
mapfile -t build_env < <(jq -r '.build.environment[]' "$out/build.json")
version="$(env "${build_env[@]}" "$go" version)"
[[ "$version" == 'go version go1.26.5 linux/amd64' ]] || exit 2
go_environment="$(env "${build_env[@]}" "$go" env -json GOVERSION GOOS GOARCH GOROOT GOPATH GOMODCACHE GOFLAGS GOTOOLCHAIN GOPROXY GOSUMDB GOWORK GOCACHE GOTMPDIR)"
build_args=("$go" -C "$upstream" test -mod=readonly -modfile "$out/go.mod" -c -p 1 -overlay "$out/overlay.json" -o "$out/phase-oracle.test" ./internal/testutil/tsbaseline)
arguments="$(jq -n --args '$ARGS.positional' -- "${build_args[@]}")"
jq --arg version "$version" --arg go_sha "$(hash_file "$go")" --argjson environment "$go_environment" \
  --arg helper_sha "$(hash_file "$phase_dir/run.sh")" --arg patch_sha "$(hash_file "$phase_dir/queries.patch")" \
  --arg overlay_sha "$(hash_file "$out/overlay.json")" --arg base_sha "$base_renderer_hash" --argjson arguments "$arguments" \
  --slurpfile overlays "$out/phase-overlay-sources.json" '
    .state="building" | .go.version=$version | .go.sha256=$go_sha | .go.environment=$environment |
    .build.arguments=$arguments | .instrumentation.overlays=$overlays[0] | .instrumentation.overlay_manifest_sha256=$overlay_sha |
    .phase_contract={report_schema_version:3,helper_sha256:$helper_sha,patch_sha256:$patch_sha,base_renderer_sha256:$base_sha,
      frozen_renderer_flag:true,independent_source_only_program:true,fresh_diagnostics:"unavailable",pointer_gate:"strict"}
  ' "$out/build.json" >"$out/build-next.json"
mv "$out/build-next.json" "$out/build.json"
build_exit=0
timeout --signal=TERM --kill-after=10s "${timeout_seconds}s" python3 "$repo/tools/ts_fixture/go_project_oracle/measure.py" "$out/build-resources.json" \
  env "${build_env[@]}" "${build_args[@]}" >"$out/build.stdout.log" 2>"$out/build.stderr.log" || build_exit=$?
resources=null
if jq -e . "$out/build-resources.json" >/dev/null 2>&1; then resources="$(jq . "$out/build-resources.json")"; fi
executable=null
state=build_error
if ((build_exit == 0)); then
  state=built
  executable="$(jq -n --arg path "$out/phase-oracle.test" --arg sha256 "$(hash_file "$out/phase-oracle.test")" '{path:$path,sha256:$sha256}')"
fi
jq --arg state "$state" --argjson code "$build_exit" --argjson resources "$resources" --argjson executable "$executable" \
  '.state=$state | .build.exit_code=$code | .build.resources=$resources | .executable=$executable' "$out/build.json" >"$out/build-next.json"
mv "$out/build-next.json" "$out/build.json"
if ((build_exit != 0)); then printf 'Phase oracle build failed: %s\n' "$out/build.stderr.log" >&2; exit "$build_exit"; fi

status=0
run_names=(process-a process-b)
pattern='^TestPhaseCorrectOracle$'
if [[ "$mode" == controls ]]; then run_names=(controls); pattern='^TestPhaseOracle'; fi
for run in "${run_names[@]}"; do
  run_args=("$out/phase-oracle.test" -test.run "$pattern" -test.count=1 -test.v "-test.timeout=${timeout_seconds}s")
  run_env=("${build_env[@]}" "TS_RUST_PHASE_PROJECT=$config" "TS_RUST_PHASE_OUTPUT=$out/$run" "TS_RUST_PHASE_PROVENANCE=$out/build.json" "TS_RUST_PHASE_RUN_ID=$run")
  code=0
  timeout --signal=TERM --kill-after=10s "${timeout_seconds}s" python3 "$repo/tools/ts_fixture/go_project_oracle/measure.py" "$out/$run-resources.json" \
    env "${run_env[@]}" "${run_args[@]}" >"$out/$run.stdout.log" 2>"$out/$run.stderr.log" || code=$?
  resources=null
  if jq -e . "$out/$run-resources.json" >/dev/null 2>&1; then resources="$(jq . "$out/$run-resources.json")"; fi
  arguments="$(jq -n --args '$ARGS.positional' -- "${run_args[@]}")"
  environment="$(jq -n --args '$ARGS.positional' -- "${run_env[@]}")"
  jq -n --arg run "$run" --arg mode "$mode" --argjson code "$code" --argjson resources "$resources" --argjson arguments "$arguments" --argjson environment "$environment" \
    '{scope:"phase_correct_oracle",mode:$mode,run_id:$run,exit_code:$code,resources:$resources,arguments:$arguments,environment:$environment}' >"$out/$run-process.json"
  if ((code != 0)); then status=1; fi
done
jq -n --arg mode "$mode" --argjson status "$status" '{schema_version:3,mode:$mode,exit_code:$status,parity_claimed:false,fresh_diagnostic_equality:null}' >"$out/run-status.json"
printf 'Phase oracle status %s: %s\n' "$status" "$out/run-status.json"
exit "$status"
