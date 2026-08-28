#!/usr/bin/env bash
set -euo pipefail

root=/home/theo/Code/sandbox/ts-rust
worktree="$root/target/agent-worktrees/wave150/type-name-symbol-root-composition"
target="$root/target/go-worktrees/wave150-type-name-symbol-root-composition-fresh"
out="$worktree/target/type-name-evidence"
upstream=/home/theo/.explore/repos/microsoft__typescript-go
seed="$root/target/worktrees/wave145-missing-type-error-alias"

if [[ "${TS_WAVE150_GO_SCOPE:-0}" != 1 ]]; then
  exec systemd-run --user --scope --quiet --collect -p MemoryMax=16777216K -p MemorySwapMax=0 \
    env TS_WAVE150_GO_SCOPE=1 bash "$0"
fi

# This lock covers only Go. No Cargo command runs inside this scope.
common="$(git -C "$worktree" rev-parse --path-format=absolute --git-common-dir)"
lock_id="$(printf '%s' "$common" | cksum | awk '{print $1}')"
exec 9>"${TMPDIR:-/tmp}/ts-rust-cargo-${lock_id}.lock"
flock 9
ulimit -c 0
ulimit -s 16384
[[ "$(git -C "$upstream" rev-parse HEAD)" == dc37b5249ab60e2bbce936f71b883e6c8136167e ]]
git -C "$upstream" diff --quiet
mkdir -p "$out" "$target/go-tmp" "$target/go-cache"
# Only dependency source modules are reused. The compiled Go cache starts empty.
module_cache="$seed/go-mod-cache"
cp "$upstream/go.mod" "$out/go.mod"
cp "$upstream/go.sum" "$out/go.sum"
jq -n --arg upstream "$upstream" --arg probes "$worktree/docs/probes" '{Replace:{
  ($upstream+"/internal/ast/zz_wave150_type_name_symbol.go"):($probes+"/type_name_symbol_ast.go"),
  ($upstream+"/internal/checker/zz_wave150_type_name_symbol.go"):($probes+"/type_name_symbol_checker.go"),
  ($upstream+"/internal/checker/zz_wave150_type_name_symbol_test.go"):($probes+"/type_name_symbol_semantics_test.go")
}}' > "$out/overlay.json"
env GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off GOWORK=off GOFLAGS= GOTELEMETRY=off \
  GOMAXPROCS=1 GOMEMLIMIT=12582912KiB \
  GOCACHE="$target/go-cache" GOMODCACHE="$module_cache" GOTMPDIR="$target/go-tmp" \
  TS_WAVE150_GO_REPORT="$out/go-value-meaning-fresh.json" \
  "$root/target/toolchains/go1.26.5/bin/go" -C "$upstream" test \
  -mod=readonly -modfile "$out/go.mod" -p 1 -overlay "$out/overlay.json" \
  -run '^TestWave150TypeNameMeaning$' -count=1 -v -timeout=120s ./internal/checker
git -C "$upstream" diff --quiet
