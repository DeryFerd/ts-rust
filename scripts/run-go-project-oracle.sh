#!/usr/bin/env bash
set -euo pipefail

if (($# < 4 || $# > 5)); then
  printf 'Usage: %s GO UPSTREAM CONFIG OUT [prepare|build|test|run]\n' "$0" >&2
  exit 2
fi
go=$1
upstream=$2
config=$3
out=$4
mode=${5:-run}
case "$mode" in prepare|build|test|run) ;; *) printf 'Unknown mode: %s\n' "$mode" >&2; exit 2 ;; esac
download_pinned=${TS_GO_ORACLE_DOWNLOAD_PINNED:-0}
case "$download_pinned" in 0|1) ;; *) printf 'TS_GO_ORACLE_DOWNLOAD_PINNED must be 0 or 1.\n' >&2; exit 2 ;; esac
for path in "$go" "$upstream" "$config" "$out"; do
  if [[ "$path" != /* ]]; then
    printf 'Every path argument must be absolute: %s\n' "$path" >&2
    exit 2
  fi
done
if [[ -e "$out" || -L "$out" ]]; then
  printf 'Output must not already exist: %s\n' "$out" >&2
  exit 2
fi
out_real="$(realpath -m -- "$out")"
upstream_real="$(realpath -- "$upstream")"
config_directory="$(realpath -m -- "$(dirname -- "$config")")"
# Keep the requested config for Go. Resolve its file target only for path guards.
physical_config="$(realpath -m -- "$config")"
physical_config_directory="$(dirname -- "$physical_config")"
if [[ ! -d "$config_directory" || ! -d "$physical_config_directory" ]]; then
  printf 'Config parent directories must exist.\n' >&2
  exit 2
fi
case "$out_real/" in
  "$upstream_real/"*|"$config_directory/"*|"$physical_config_directory/"*)
    printf 'Output must be outside the upstream and config directories.\n' >&2
    exit 2
    ;;
esac
project_dir=""
project_real=""
if project_dir="$(git -C "$(dirname -- "$config")" rev-parse --show-toplevel 2>/dev/null)"; then
  project_real="$(realpath -- "$project_dir")"
  case "$out_real/" in "$project_real/"*) printf 'Output must be outside the project checkout.\n' >&2; exit 2 ;; esac
fi
physical_project_real=""
if physical_project_dir="$(git -C "$physical_config_directory" rev-parse --show-toplevel 2>/dev/null)"; then
  physical_project_real="$(realpath -- "$physical_project_dir")"
  case "$out_real/" in "$physical_project_real/"*) printf 'Output must be outside the project checkout.\n' >&2; exit 2 ;; esac
fi
gomodcache_requested="${GOMODCACHE:-$out/go-mod-cache}"
out_parent_real="$(dirname -- "$out_real")"
validate_module_cache() {
  if [[ "$gomodcache_requested" != /* ]]; then
    printf 'Module cache must be an absolute path.\n' >&2
    exit 2
  fi
  gomodcache_real="$(realpath -m -- "$gomodcache_requested")"
  for protected in "$upstream_real" "$config_directory" "${project_real:-}" \
    "$physical_config_directory" "$physical_project_real"; do
    if [[ -z "$protected" ]]; then continue; fi
    case "$gomodcache_real/" in "$protected/"*)
      printf 'Module cache must be outside upstream and project sources.\n' >&2
      exit 2
      ;;
    esac
    case "$protected/" in "$gomodcache_real/"*)
      printf 'Module cache must not contain upstream or project sources.\n' >&2
      exit 2
      ;;
    esac
  done
  if [[ "$gomodcache_real" == "$out_parent_real" || "$gomodcache_real" == "$out_real" ]]; then
    printf 'Module cache must be a separate directory under the output parent.\n' >&2
    exit 2
  fi
  case "$gomodcache_real/" in "$out_parent_real/"*) ;;
    *) printf 'Module cache must stay under the output parent.\n' >&2; exit 2 ;;
  esac
}
validate_module_cache
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd -- "$script_dir/.." && pwd)"
sources="$repo/tools/ts_fixture/go_project_oracle"
expected_sha=dc37b5249ab60e2bbce936f71b883e6c8136167e
upstream_sha="$(git -C "$upstream" rev-parse HEAD)"
upstream_dirty="$(git -C "$upstream" status --porcelain=v1)"
if [[ "$upstream_sha" != "$expected_sha" || -n "$upstream_dirty" ]]; then
  printf 'The upstream checkout must be clean at %s.\n' "$expected_sha" >&2
  exit 2
fi
memory_kib=${TS_GO_ORACLE_MEMORY_LIMIT_KIB:-${TS_CARGO_MEMORY_LIMIT_KIB:-16777216}}
timeout_seconds=${TS_GO_ORACLE_TIMEOUT_SECONDS:-600}
if [[ ! "$memory_kib" =~ ^[1-9][0-9]*$ || ! "$timeout_seconds" =~ ^[1-9][0-9]*$ ]]; then
  printf 'Memory and timeout limits must be positive integers.\n' >&2
  exit 2
fi

# Use the Cargo queue so one Go build cannot overlap a large Rust build.
if [[ "$mode" != prepare ]]; then
  if [[ ! -x "$go" ]] || ! command -v python3 >/dev/null; then
    printf 'Build and run modes require the Go executable and Python 3.\n' >&2
    exit 2
  fi
  if [[ "${TS_GO_ORACLE_CGROUP_ACTIVE:-0}" != 1 ]]; then
    exec systemd-run --user --scope --quiet --collect \
      -p "MemoryMax=${memory_kib}K" -p MemorySwapMax=0 \
      env TS_GO_ORACLE_CGROUP_ACTIVE=1 TS_GO_ORACLE_MEMORY_LIMIT_KIB="$memory_kib" \
      bash "$script_dir/run-go-project-oracle.sh" "$@"
  fi
  lock_seed="${TS_CARGO_LOCK_ID:-$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir)}"
  lock_id="$(printf '%s' "$lock_seed" | cksum | awk '{print $1}')"
  exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
  flock 9
  ulimit -c 0
fi
validate_module_cache

hash_file() {
  local hash ignored
  read -r hash ignored < <(sha256sum -- "$1")
  printf '%s' "$hash"
}

mkdir -p -- "$(dirname -- "$out")"
mkdir -- "$out"
mkdir -- "$out/overlay" "$out/go-cache" "$out/go-tmp"
cp -- "$upstream/go.mod" "$out/go.mod"
cp -- "$upstream/go.sum" "$out/go.sum"
cp -- "$sources/checker_replay.go.txt" "$out/overlay/checker_replay.go"
cp -- "$sources/baseline_hooks.go.txt" "$out/overlay/baseline_hooks.go"
cp -- "$sources/project_oracle_test.go.txt" "$out/overlay/project_oracle_test.go"
cp -- "$sources/project_graph_test.go.txt" "$out/overlay/project_graph_test.go"
patch --batch --fuzz=0 --reject-file=- \
  --output="$out/overlay/type_symbol_baseline.go" \
  "$upstream/internal/testutil/tsbaseline/type_symbol_baseline.go" \
  "$sources/baseline_hooks.patch" >"$out/patch.log"
jq -n --arg upstream "$upstream" --arg out "$out" '{Replace:{
  ($upstream+"/internal/checker/zz_ts_rust_project_oracle.go"): ($out+"/overlay/checker_replay.go"),
  ($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_project_oracle_hooks.go"): ($out+"/overlay/baseline_hooks.go"),
  ($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_project_oracle_test.go"): ($out+"/overlay/project_oracle_test.go"),
  ($upstream+"/internal/testutil/tsbaseline/zz_ts_rust_project_graph_test.go"): ($out+"/overlay/project_graph_test.go"),
  ($upstream+"/internal/testutil/tsbaseline/type_symbol_baseline.go"): ($out+"/overlay/type_symbol_baseline.go")
}}' >"$out/overlay.json"

while IFS=$'\t' read -r original replacement; do
  original_sha=null
  if [[ -e "$original" ]]; then
    if [[ "$original" != "$upstream/internal/testutil/tsbaseline/type_symbol_baseline.go" ]]; then
      printf 'An added overlay source already exists: %s\n' "$original" >&2
      exit 2
    fi
    original_sha="\"$(hash_file "$original")\""
  fi
  jq -n --arg original "$original" --arg replacement "$replacement" \
    --arg sha256 "$(hash_file "$replacement")" --argjson original_sha "$original_sha" \
    '{original_path:$original,replacement_path:$replacement,sha256:$sha256,original_sha256:$original_sha}'
done < <(jq -r '.Replace | to_entries[] | [.key,.value] | @tsv' "$out/overlay.json") | jq -s . >"$out/overlay-sources.json"

build_args=("$go" -C "$upstream" test -mod=readonly -modfile "$out/go.mod" -c -p 1 -overlay "$out/overlay.json" -o "$out/project-oracle.test" ./internal/testutil/tsbaseline)
build_env=(GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off GOWORK=off GOFLAGS= GOMAXPROCS=1 "GOMEMLIMIT=$((memory_kib * 3 / 4))KiB" "GOCACHE=$out/go-cache" "GOTMPDIR=$out/go-tmp" "TMPDIR=$out/go-tmp" "GOMODCACHE=$gomodcache_real")
args_json="$(jq -n --args '$ARGS.positional' -- "${build_args[@]}")"
env_json="$(jq -n --args '$ARGS.positional' -- "${build_env[@]}")"
rust_sha="$(git -C "$repo" rev-parse HEAD)"
rust_dirty="$(git -C "$repo" status --porcelain=v1)"
project_root=null
project_sha=null
project_dirty=null
project_inputs='[]'
if [[ -n "$project_dir" ]]; then
  project_root="$(jq -Rn --arg value "$project_dir" '$value')"
  project_sha="$(jq -Rn --arg value "$(git -C "$project_dir" rev-parse HEAD)" '$value')"
  project_dirty="$(jq -Rn --arg value "$(git -C "$project_dir" status --porcelain=v1)" '$value')"
  project_inputs="$(
    for name in package.json pnpm-lock.yaml pnpm-workspace.yaml package-lock.json yarn.lock bun.lock bun.lockb LICENSE LICENSE.md LICENSE.txt LICENSE-MIT COPYING; do
      if [[ -f "$project_dir/$name" ]]; then
        jq -n --arg path "$project_dir/$name" --arg sha256 "$(hash_file "$project_dir/$name")" '{path:$path,sha256:$sha256}'
      fi
    done | jq -s .
  )"
fi
jq -n --arg upstream "$upstream" --arg upstream_sha "$upstream_sha" --arg upstream_dirty "$upstream_dirty" \
  --arg helper "$script_dir/run-go-project-oracle.sh" --arg helper_sha "$(hash_file "$script_dir/run-go-project-oracle.sh")" \
  --arg measurement_sha "$(hash_file "$sources/measure.py")" \
  --arg mod_sha "$(hash_file "$out/go.mod")" --arg sum_sha "$(hash_file "$out/go.sum")" \
  --arg patch_sha "$(hash_file "$sources/baseline_hooks.patch")" --arg overlay_sha "$(hash_file "$out/overlay.json")" \
  --arg rust_sha "$rust_sha" --arg rust_dirty "$rust_dirty" --arg go "$go" --arg config "$config" \
  --argjson project_root "$project_root" --argjson project_sha "$project_sha" --argjson project_dirty "$project_dirty" \
  --argjson project_inputs "$project_inputs" \
  --argjson arguments "$args_json" --argjson environment "$env_json" \
  --argjson memory_kib "$memory_kib" --argjson timeout_seconds "$timeout_seconds" \
  --slurpfile overlays "$out/overlay-sources.json" '{
    schema_version:1,state:"prepared",upstream:{path:$upstream,sha:$upstream_sha,dirty:$upstream_dirty,go_mod_sha256:$mod_sha,go_sum_sha256:$sum_sha},
    instrumentation:{rust_sha:$rust_sha,rust_dirty:$rust_dirty,helper_path:$helper,helper_sha256:$helper_sha,
      patch_sha256:$patch_sha,measurement_sha256:$measurement_sha,overlay_manifest_sha256:$overlay_sha,overlays:$overlays[0]},
    project:{root:$project_root,sha:$project_sha,dirty:$project_dirty,config_path:$config,metadata_inputs:$project_inputs},
    go:{executable:$go,version:null,sha256:null,environment:null},
    dependency_download:null,build:{arguments:$arguments,environment:$environment,exit_code:null,resources:null},
    limits:{memory_kib:$memory_kib,timeout_seconds:$timeout_seconds},executable:null
  }' >"$out/build.json"
if [[ "$mode" == prepare ]]; then
  printf 'Prepared overlays: %s\n' "$out/overlay.json"
  exit 0
fi

go_version="$(env "${build_env[@]}" "$go" version)"
case "$go_version" in *' go1.26.'*) ;; *) printf 'The pinned oracle requires Go 1.26.x: %s\n' "$go_version" >&2; exit 2 ;; esac
go_environment="$(env "${build_env[@]}" "$go" env -json GOVERSION GOOS GOARCH GOROOT GOPATH GOMODCACHE GOFLAGS GOTOOLCHAIN GOPROXY GOSUMDB GOWORK GOCACHE GOTMPDIR)"
jq --arg version "$go_version" --arg sha256 "$(hash_file "$go")" --argjson environment "$go_environment" \
  '.state="building" | .go.version=$version | .go.sha256=$sha256 | .go.environment=$environment' \
  "$out/build.json" >"$out/build-next.json"
mv -- "$out/build-next.json" "$out/build.json"
if [[ "$download_pinned" == 1 ]]; then
  env "${build_env[@]}" "$go" -C "$upstream" mod edit -json -modfile "$out/go.mod" >"$out/module-inputs.json"
  jq -e '((.Replace // []) | length) == 0' "$out/module-inputs.json" >/dev/null
  pinned_modules=()
  while IFS=$'\t' read -r path version; do
    if ! awk -v module="$path" -v version="$version" '$1 == module && $2 == version && $3 ~ /^h1:/ { found=1 } END { exit !found }' "$upstream/go.sum"; then
      printf 'Missing pinned module content checksum: %s@%s\n' "$path" "$version" >&2
      exit 2
    fi
    pinned_modules+=("$path@$version")
  done < <(jq -r '.Require[] | [.Path,.Version] | @tsv' "$out/module-inputs.json")
  dependency_args=("$go" -C "$upstream" mod download -modfile "$out/go.mod" -json "${pinned_modules[@]}")
  dependency_env=("${build_env[@]}" GOPROXY=https://proxy.golang.org)
  dependency_exit=0
  timeout --signal=TERM --kill-after=10s "${timeout_seconds}s" \
    python3 "$sources/measure.py" "$out/dependency-resources.json" \
    env "${dependency_env[@]}" "${dependency_args[@]}" >"$out/dependencies.json" 2>"$out/dependencies.stderr.log" || dependency_exit=$?
  if ! cmp -s "$upstream/go.mod" "$out/go.mod" || ! cmp -s "$upstream/go.sum" "$out/go.sum"; then
    printf 'The copied module inputs changed during the pinned dependency download.\n' >&2
    dependency_exit=1
  fi
  resources=null
  if jq -e . "$out/dependency-resources.json" >/dev/null 2>&1; then resources="$(jq . "$out/dependency-resources.json")"; fi
  dependency_args_json="$(jq -n --args '$ARGS.positional' -- "${dependency_args[@]}")"
  dependency_env_json="$(jq -n --args '$ARGS.positional' -- "${dependency_env[@]}")"
  jq --argjson code "$dependency_exit" --argjson arguments "$dependency_args_json" --argjson environment "$dependency_env_json" --argjson resources "$resources" \
    '.dependency_download={exit_code:$code,arguments:$arguments,environment:$environment,resources:$resources} | if $code != 0 then .state="dependency_error" else . end' \
    "$out/build.json" >"$out/build-next.json"
  mv -- "$out/build-next.json" "$out/build.json"
  if ((dependency_exit != 0)); then exit "$dependency_exit"; fi
fi
build_exit=0
timeout --signal=TERM --kill-after=10s "${timeout_seconds}s" \
  python3 "$sources/measure.py" "$out/build-resources.json" \
  env "${build_env[@]}" "${build_args[@]}" >"$out/build.stdout.log" 2>"$out/build.stderr.log" || build_exit=$?
resources=null
if jq -e . "$out/build-resources.json" >/dev/null 2>&1; then resources="$(jq . "$out/build-resources.json")"; fi
executable=null
state=build_error
if ((build_exit == 0)); then
  state=built
  executable="$(jq -n --arg path "$out/project-oracle.test" --arg sha256 "$(hash_file "$out/project-oracle.test")" '{path:$path,sha256:$sha256}')"
fi
jq --arg state "$state" --argjson code "$build_exit" --argjson resources "$resources" --argjson executable "$executable" \
  '.state=$state | .build.exit_code=$code | .build.resources=$resources | .executable=$executable' \
  "$out/build.json" >"$out/build-next.json"
mv -- "$out/build-next.json" "$out/build.json"
if ((build_exit != 0)); then
  printf 'Go build failed with status %s. See %s.\n' "$build_exit" "$out/build.stderr.log" >&2
  exit "$build_exit"
fi
if [[ "$mode" == build ]]; then
  printf 'Built oracle: %s\n' "$out/project-oracle.test"
  exit 0
fi
if [[ "$mode" == test ]]; then
  test_args=("$out/project-oracle.test" -test.run '^TestProjectOracle.+$' -test.count=1 -test.v "-test.timeout=${timeout_seconds}s")
  test_exit=0
  timeout --signal=TERM --kill-after=10s "${timeout_seconds}s" \
    python3 "$sources/measure.py" "$out/focused-test-resources.json" \
    env "${build_env[@]}" "${test_args[@]}" >"$out/focused-tests.stdout.log" 2>"$out/focused-tests.stderr.log" || test_exit=$?
  resources=null
  if jq -e . "$out/focused-test-resources.json" >/dev/null 2>&1; then resources="$(jq . "$out/focused-test-resources.json")"; fi
  test_args_json="$(jq -n --args '$ARGS.positional' -- "${test_args[@]}")"
  jq -n --argjson code "$test_exit" --argjson arguments "$test_args_json" --argjson environment "$env_json" --argjson resources "$resources" \
    '{scope:"instrumentation_only",exit_code:$code,arguments:$arguments,environment:$environment,resources:$resources}' >"$out/focused-tests.json"
  printf 'Focused Go oracle test status: %s. See %s.\n' "$test_exit" "$out/focused-tests.stdout.log"
  exit "$test_exit"
fi

all_ok=1
for run in go-a go-b; do
  run_args=("$out/project-oracle.test" -test.run '^TestProjectOracle$' -test.count=1 "-test.timeout=${timeout_seconds}s")
  run_env=("${build_env[@]}" "TS_RUST_ORACLE_PROJECT=$config" "TS_RUST_ORACLE_OUTPUT=$out/$run" \
    "TS_RUST_ORACLE_HEADER=${TS_RUST_ORACLE_HEADER:-project}" "TS_RUST_ORACLE_PROVENANCE=$out/build.json" "TS_RUST_ORACLE_RUN_ID=$run")
  run_exit=0
  timeout --signal=TERM --kill-after=10s "${timeout_seconds}s" \
    python3 "$sources/measure.py" "$out/$run-resources.json" \
    env "${run_env[@]}" "${run_args[@]}" >"$out/$run.stdout.log" 2>"$out/$run.stderr.log" || run_exit=$?
  resources=null
  if jq -e . "$out/$run-resources.json" >/dev/null 2>&1; then resources="$(jq . "$out/$run-resources.json")"; fi
  report_present=false
  if [[ -s "$out/$run/report.json" ]]; then report_present=true; fi
  run_args_json="$(jq -n --args '$ARGS.positional' -- "${run_args[@]}")"
  run_env_json="$(jq -n --args '$ARGS.positional' -- "${run_env[@]}")"
  jq -n --arg run "$run" --argjson code "$run_exit" --argjson present "$report_present" \
    --argjson resources "$resources" --argjson arguments "$run_args_json" --argjson environment "$run_env_json" \
    '{run_id:$run,exit_code:$code,report_present:$present,resources:$resources,arguments:$arguments,environment:$environment}' >"$out/$run-process.json"
  if ((run_exit != 0)) || [[ "$report_present" != true ]]; then all_ok=0; fi
done
equal=null
comparison_state=unavailable
if ((all_ok)); then
  equal=false
  comparison_state=different
  jq -S 'del(.runtime,.run_id)' "$out/go-a/report.json" >"$out/go-a-stable.json"
  jq -S 'del(.runtime,.run_id)' "$out/go-b/report.json" >"$out/go-b-stable.json"
  if cmp -s "$out/go-a-stable.json" "$out/go-b-stable.json"; then
    equal=true
    for artifact in cold.errors.txt cold.types cold.symbols warm.errors.txt warm.types warm.symbols; do
      if [[ -e "$out/go-a/$artifact" || -e "$out/go-b/$artifact" ]] && ! cmp -s "$out/go-a/$artifact" "$out/go-b/$artifact"; then equal=false; fi
    done
  fi
  if [[ "$equal" == true ]]; then comparison_state=equal; fi
fi
jq -n --arg state "$comparison_state" --argjson equal "$equal" --slurpfile first "$out/go-a-process.json" --slurpfile second "$out/go-b-process.json" \
  '{schema_version:2,comparison_state:$state,fresh_processes_equal:$equal,processes:[$first[0],$second[0]]}' >"$out/runs.json"
if [[ "$equal" != true ]]; then
  printf 'Go oracle did not complete two equal fresh runs. See %s.\n' "$out/runs.json" >&2
  exit 1
fi
printf 'Go oracle reports: %s/go-a/report.json and %s/go-b/report.json\n' "$out" "$out"
