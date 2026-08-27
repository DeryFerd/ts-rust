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
if [[ -e "$out" || -L "$out" ]]; then
  printf 'Output must not already exist: %s\n' "$out" >&2
  exit 2
fi
# Preparation and later writers must use the same destination.
out="$(realpath -m -- "$out")"
adapter_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd -- "$adapter_dir/../../../.." && pwd)"
phase_dir="$repo/tools/ts_fixture/go_project_oracle/phase_correct"
provider_dir="$repo/tools/ts_fixture/go_project_oracle"
memory_kib=${TS_GO_ORACLE_MEMORY_LIMIT_KIB:-16777216}
timeout_seconds=${TS_GO_ORACLE_TIMEOUT_SECONDS:-600}
[[ "$memory_kib" =~ ^[1-9][0-9]*$ && "$timeout_seconds" =~ ^[1-9][0-9]*$ ]] || exit 2
if [[ "${TS_OBJECT_PHASE_CGROUP_ACTIVE:-0}" != 1 ]]; then
  exec systemd-run --user --scope --quiet --collect -p "MemoryMax=${memory_kib}K" -p MemorySwapMax=0 \
    env TS_OBJECT_PHASE_CGROUP_ACTIVE=1 TS_GO_ORACLE_MEMORY_LIMIT_KIB="$memory_kib" bash "$adapter_dir/run.sh" "$@"
fi
lock_seed="${TS_CARGO_LOCK_ID:-$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir)}"
lock_id="$(printf '%s' "$lock_seed" | cksum | awk '{print $1}')"
exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
flock 9
ulimit -c 0
hash_file() { local hash ignored; read -r hash ignored < <(sha256sum -- "$1"); printf '%s' "$hash"; }
git -C "$repo" diff --exit-code 0c79366b6ba75a447f920aa48fba77a09991dd4f -- scripts/run-go-project-oracle.sh
git -C "$repo" diff --exit-code a84de244261ba1389603494fb7b97d510154355a -- \
  tools/ts_fixture/go_project_oracle/project_oracle_test.go.txt tools/ts_fixture/go_project_oracle/project_graph_test.go.txt \
  tools/ts_fixture/go_project_oracle/baseline_hooks.go.txt tools/ts_fixture/go_project_oracle/baseline_hooks.patch \
  tools/ts_fixture/go_project_oracle/checker_replay.go.txt
git -C "$repo" diff --exit-code b249b9ed77cc1ff1f55df0ce7db3f5a01f0cf453 -- tools/ts_fixture/go_project_oracle/phase_correct
git -C "$repo" diff --exit-code a84de244261ba1389603494fb7b97d510154355a -- \
  tools/ts_fixture/go_project_oracle/object_query_witness.go.txt \
  tools/ts_fixture/go_project_oracle/object_query_witness_checker.patch \
  tools/ts_fixture/go_project_oracle/object_query_witness_relation.patch \
  tools/ts_fixture/go_project_oracle/object_query_witness_export_test.go.txt \
  tools/ts_fixture/go_project_oracle/object_query_witness_test.go.txt
bash "$repo/scripts/run-go-project-oracle.sh" "$go" "$upstream" "$config" "$out" prepare
cp "$phase_dir/hooks.go.txt" "$out/overlay/phase_hooks.go"
cp "$phase_dir/oracle_test.go.txt" "$out/overlay/phase_oracle_test.go"
cp "$phase_dir/controls_test.go.txt" "$out/overlay/phase_controls_test.go"
cp "$provider_dir/object_query_witness.go.txt" "$out/overlay/object_query_witness.go"
cp "$adapter_dir/hooks.go.txt" "$out/overlay/object_phase_hooks.go"
cp "$adapter_dir/adapter_test.go.txt" "$out/overlay/object_phase_adapter_test.go"
cp "$adapter_dir/controls_test.go.txt" "$out/overlay/object_phase_controls_test.go"
base_renderer_hash="$(hash_file "$out/overlay/type_symbol_baseline.go")"
patch --batch --fuzz=0 --reject-file=- --output="$out/overlay/phase_type_symbol_baseline.go" \
  "$out/overlay/type_symbol_baseline.go" "$phase_dir/queries.patch" >"$out/phase-patch.log"
patch --batch --fuzz=0 --reject-file=- --output="$out/overlay/object_type_symbol_baseline.go" \
  "$out/overlay/phase_type_symbol_baseline.go" "$adapter_dir/walker.patch" >"$out/object-walker-patch.log"
patch --batch --fuzz=0 --reject-file=- --output="$out/overlay/object_phase_oracle_test.go" \
  "$out/overlay/phase_oracle_test.go" "$adapter_dir/phase.patch" >"$out/object-phase-patch.log"
patch --batch --fuzz=0 --reject-file=- --output="$out/overlay/object_checker.go" \
  "$upstream/internal/checker/checker.go" "$provider_dir/object_query_witness_checker.patch" >"$out/object-provider-checker-patch.log"
patch --batch --fuzz=0 --reject-file=- --output="$out/overlay/object_relater.go" \
  "$upstream/internal/checker/relater.go" "$provider_dir/object_query_witness_relation.patch" >"$out/object-provider-relation-patch.log"
jq --arg upstream "$upstream" --arg out "$out" '
  .Replace[($upstream+"/internal/testutil/tsbaseline/type_symbol_baseline.go")] = ($out+"/overlay/object_type_symbol_baseline.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_phase_hooks.go")] = ($out+"/overlay/phase_hooks.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_phase_oracle_test.go")] = ($out+"/overlay/object_phase_oracle_test.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_phase_controls_test.go")] = ($out+"/overlay/phase_controls_test.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_object_phase_hooks.go")] = ($out+"/overlay/object_phase_hooks.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_object_phase_adapter_test.go")] = ($out+"/overlay/object_phase_adapter_test.go") |
  .Replace[($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_object_phase_controls_test.go")] = ($out+"/overlay/object_phase_controls_test.go") |
  .Replace[($upstream+"/internal/checker/checker.go")] = ($out+"/overlay/object_checker.go") |
  .Replace[($upstream+"/internal/checker/relater.go")] = ($out+"/overlay/object_relater.go") |
  .Replace[($upstream+"/internal/checker/zz_ts_rust_object_witness.go")] = ($out+"/overlay/object_query_witness.go")
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
[[ "$(hash_file "$go")" == 8da5fd321795754b994c64e3eb8a5a14ff47bd285559a7e876f3c79abafc67f9 ]] || exit 2
if [[ -n "${TS_OBJECT_PHASE_BUILD_CACHE:-}" ]]; then
  cp -a --reflink=auto "$TS_OBJECT_PHASE_BUILD_CACHE/." "$out/go-cache/"
fi
build_args=("$go" -C "$upstream" test -mod=readonly -modfile "$out/go.mod" -c -p 1 -overlay "$out/overlay.json" -o "$out/object-phase.test" ./internal/testutil/tsbaseline)
arguments="$(jq -n --args '$ARGS.positional' -- "${build_args[@]}")"
jq --arg version "$version" --arg go_sha "$(hash_file "$go")" --argjson environment "$go_environment" \
  --arg helper_sha "$(hash_file "$phase_dir/run.sh")" --arg patch_sha "$(hash_file "$phase_dir/queries.patch")" \
  --arg overlay_sha "$(hash_file "$out/overlay.json")" --arg base_sha "$base_renderer_hash" --argjson arguments "$arguments" \
  --arg adapter_sha "$(hash_file "$adapter_dir/run.sh")" --arg walker_sha "$(hash_file "$adapter_dir/walker.patch")" \
  --arg phase_adapter_sha "$(hash_file "$adapter_dir/phase.patch")" --arg provider_sha "$(hash_file "$provider_dir/object_query_witness.go.txt")" \
  --arg provider_checker_sha "$(hash_file "$provider_dir/object_query_witness_checker.patch")" --arg provider_relation_sha "$(hash_file "$provider_dir/object_query_witness_relation.patch")" \
  --slurpfile overlays "$out/phase-overlay-sources.json" '
    .state="building" | .go.version=$version | .go.sha256=$go_sha | .go.environment=$environment |
    .build.arguments=$arguments | .instrumentation.overlays=$overlays[0] | .instrumentation.overlay_manifest_sha256=$overlay_sha |
    .phase_contract={report_schema_version:3,helper_sha256:$helper_sha,patch_sha256:$patch_sha,base_renderer_sha256:$base_sha,
      frozen_renderer_flag:true,independent_source_only_program:true,fresh_diagnostics:"unavailable",pointer_gate:"strict"} |
    .object_witness_adapter={provider_commit:"b650cedf78cccd0e20782bc5df482cd6103059de",phase_base:"c0c729459fe2e6cc4c3b991dd7581aaa4bd33f23",
      helper_sha256:$adapter_sha,walker_patch_sha256:$walker_sha,phase_patch_sha256:$phase_adapter_sha,
      provider_sha256:$provider_sha,provider_checker_patch_sha256:$provider_checker_sha,provider_relation_patch_sha256:$provider_relation_sha,
      queries:"one_provider_call_per_actual_type_query",verification:"after_both_closed_artifact_passes",acceptance:"unchanged"}
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
  executable="$(jq -n --arg path "$out/object-phase.test" --arg sha256 "$(hash_file "$out/object-phase.test")" '{path:$path,sha256:$sha256}')"
fi
jq --arg state "$state" --argjson code "$build_exit" --argjson resources "$resources" --argjson executable "$executable" \
  '.state=$state | .build.exit_code=$code | .build.resources=$resources | .executable=$executable' "$out/build.json" >"$out/build-next.json"
mv "$out/build-next.json" "$out/build.json"
if ((build_exit != 0)); then printf 'Object phase build failed: %s\n' "$out/build.stderr.log" >&2; exit "$build_exit"; fi

status=0
run_names=(process-a process-b)
pattern='^TestObjectWitnessPhaseProject$'
if [[ "$mode" == controls ]]; then run_names=(controls); pattern='^(TestObjectPhaseControls|TestPhaseOracle.*)$'; fi
for run in "${run_names[@]}"; do
  run_args=("$out/object-phase.test" -test.run "$pattern" -test.count=1 -test.v "-test.timeout=${timeout_seconds}s")
  run_env=("${build_env[@]}" "TS_OBJECT_PHASE_CONFIG=$config" "TS_OBJECT_PHASE_OUTPUT=$out/$run" "TS_OBJECT_PHASE_PROVENANCE=$out/build.json" "TS_OBJECT_PHASE_RUN_ID=$run")
  code=0
  timeout --signal=TERM --kill-after=10s "${timeout_seconds}s" python3 "$repo/tools/ts_fixture/go_project_oracle/measure.py" "$out/$run-resources.json" \
    env "${run_env[@]}" "${run_args[@]}" >"$out/$run.stdout.log" 2>"$out/$run.stderr.log" || code=$?
  resources=null
  if jq -e . "$out/$run-resources.json" >/dev/null 2>&1; then resources="$(jq . "$out/$run-resources.json")"; fi
  arguments="$(jq -n --args '$ARGS.positional' -- "${run_args[@]}")"
  environment="$(jq -n --args '$ARGS.positional' -- "${run_env[@]}")"
  jq -n --arg run "$run" --arg mode "$mode" --argjson code "$code" --argjson resources "$resources" --argjson arguments "$arguments" --argjson environment "$environment" \
    '{scope:"object_witness_phase_adapter",mode:$mode,run_id:$run,exit_code:$code,resources:$resources,arguments:$arguments,environment:$environment}' >"$out/$run-process.json"
  if ((code != 0)); then status=1; fi
done
jq -n --arg mode "$mode" --argjson status "$status" '{schema_version:3,mode:$mode,exit_code:$status,parity_claimed:false,fresh_diagnostic_equality:null}' >"$out/run-status.json"
printf 'Object phase status %s: %s\n' "$status" "$out/run-status.json"
exit "$status"
