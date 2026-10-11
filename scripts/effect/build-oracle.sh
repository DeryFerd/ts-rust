#!/usr/bin/env bash
# Builds the effect-tsgo language server (Go tsc with the Effect hooks) on the TypeScript Go source at
# our Go pin. It is the Go side for the Effect LSP checks (scripts/effect/ls-cases.mjs,
# scripts/goport/lsp_battery_effect.py) and the Effect parts of the diagnostics checks.
#
# usage: scripts/effect/build-oracle.sh <out-dir> [effect-src]
#   <out-dir>    new work dir. Result: <out-dir>/bin/tsc, <out-dir>/BUILD.json, logs in <out-dir>/logs.
#                The sources stay in <out-dir>/src (effect-tsgo clone, TypeScript clone in src/typescript).
#   effect-src   effect-tsgo git repo that has EFFECT_REV and EFFECT_OLD_REV
#                (default target/continuation-r97-goport/effect051/effect-tsgo-0511 in the main checkout:
#                the parent of the git common dir, or /home/theo/Code/sandbox/ts-rust from a clone).
# env: EFFECT_REV (default 47cb1ed7, effect-tsgo 0.51.1), EFFECT_OLD_REV (default bddb6230, see below),
#      GOPORT_PIN (default 673a5f17d713), TS_REPO (microsoft/TypeScript clone with the pin; default
#      ~/.explore/repos/microsoft__TypeScript@<pin>).
# Run it under systemd-run --user --collect --wait -p MemoryMax=16G -p MemorySwapMax=0 (go build uses
# several GB). About 5 minutes with a warm Go cache; the first gen_shims package load takes 3 minutes.
#
# The build is reproducible: GOTOOLCHAIN is pinned to go1.27.1 (the toolchain of the 0.51.1 release;
# the pin's go.mod names only "go 1.27") and go build runs with -trimpath, so every out dir gives the
# same tsc. With the default revisions that is KNOWN_SHA below: the e1 goldens are keyed to it
# (lsp_oracle.py golden/<sha12>). A different sha with the default revisions stops the script (exit 3).
# The shared copy that lsp_battery_effect.py uses by default is ls-oracle/effect/oracle/<sha12>/bin/tsc
# (with BUILD.json) in the main checkout's target/continuation-r97-goport.
#
# Why it is not a plain repoctl build: effect-tsgo 0.51.1 targets TypeScript a1ef42b9
# (7.1.0-dev.20261006.1), 55 commits after pin N 673a5f17d713. Between them TypeScript added typed
# paths (#64159) and generated option tables (#64457), so 9 of the 27 patches do not apply at N, and
# 010 (fourslash, test only) applies as text but uses the a1ef42b9 API. effect-tsgo bddb6230 (#779)
# targets 0681ef7fa3, the parent of N. Its versions of those 10 patches apply at N, and each one
# differs from the 0.51.1 version only in the a1ef42b9 API (checked line by line: no Effect behavior
# change). So:
#   1. Patches: the 0.51.1 stack in name order, with OLD_PATCHES from EFFECT_OLD_REV. 032 is skipped:
#      it fixes a TypeScript root-directory include bug, not an Effect feature, and tsc-rs follows N
#      (neither version of it applies at N).
#   2. The diagnostics generator, as repoctl runs it.
#   3. Shims: gen_shims in its provider plus backport mode (the mode effect-tsgo uses for TS 7.0.2), with
#      an overlay made below from effect-tsgo's two provider overlays. N has the old path types (as
#      7.0.2) but the new checker link store, change tracker and LSP converters (as a1ef42b9). The
#      tool's 7.0.2 dependency list lacks contentmapper and spanmap, which N has: use its modern list.
#   4. go build -trimpath ./typescript/tsc/cmd/tsc as the plain oracle (scripts/upstream/pin.py:
#      CGO_ENABLED=0 GOAMD64=v1, lib files embedded). The release is -tags=noembed with lib files beside it; embedded
#      libs keep lib URIs as bundled:///libs/..., as the plain oracle and tsc-rs answer over LSP.
set -euo pipefail

if [[ $# -lt 1 || $1 == help || $1 == -h || $1 == --help ]]; then
  sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'
  exit 0
fi

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
# Work data lives in the main checkout's target dir: the parent of the git common dir from the main
# checkout or any worktree. An independent clone has no work data, so it uses the main checkout path
# (the remote hosts mirror it at the same path).
MAIN=$(dirname "$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir)")
[[ -d $MAIN/target/continuation-r97-goport ]] || MAIN=/home/theo/Code/sandbox/ts-rust
OUT=$(realpath -m "$1")
EFFECT_SRC=$(realpath -m "${2:-$MAIN/target/continuation-r97-goport/effect051/effect-tsgo-0511}")
EFFECT_REV=${EFFECT_REV:-47cb1ed7}
EFFECT_OLD_REV=${EFFECT_OLD_REV:-bddb6230}
PIN=${GOPORT_PIN:-673a5f17d713}
TS_REPO=${TS_REPO:-$HOME/.explore/repos/microsoft__TypeScript@$PIN}
OLD_PATCHES="002 007 010 013 015 018 025 027 028 030"
SKIP_PATCHES="032"
GO_TOOLCHAIN=go1.27.1
# tsc sha256 from the default EFFECT_REV, EFFECT_OLD_REV and GOPORT_PIN (any out dir, any clone).
KNOWN_SHA=93a772ca8d28954b63665c9d699a9f817f574b4bc5109d8fa6a90bea7187aecc
export GOTOOLCHAIN=$GO_TOOLCHAIN

for rev in "$EFFECT_REV" "$EFFECT_OLD_REV"; do
  if ! git -C "$EFFECT_SRC" rev-parse -q --verify "$rev^{commit}" > /dev/null 2>&1; then
    echo "build-oracle: no effect-tsgo repo with $rev at $EFFECT_SRC; pass one as the effect-src argument" >&2
    exit 2
  fi
done
if ! git -C "$TS_REPO" rev-parse -q --verify "$PIN^{commit}" > /dev/null 2>&1; then
  echo "build-oracle: no TypeScript repo with $PIN at $TS_REPO; set TS_REPO" >&2
  exit 2
fi

if [[ -e $OUT/src ]]; then
  echo "build-oracle: $OUT/src exists; use a new out dir" >&2
  exit 2
fi
mkdir -p "$OUT/bin" "$OUT/logs" "$OUT/old-patches"
SRC=$OUT/src
log() { echo "build-oracle: $*"; }

log "effect-tsgo $EFFECT_REV from $EFFECT_SRC"
git clone -q --shared --no-checkout "$EFFECT_SRC" "$SRC"
git -C "$SRC" checkout -q --detach "$EFFECT_REV"
rmdir "$SRC/typescript"
log "TypeScript $PIN from $TS_REPO"
git clone -q --shared --no-checkout "$TS_REPO" "$SRC/typescript"
git -C "$SRC/typescript" checkout -q --detach "$PIN"

log "patches"
applied=()
for p in "$SRC"/_patches/typescript/*.patch; do
  name=$(basename "$p")
  num=${name%%-*}
  if [[ " $SKIP_PATCHES " == *" $num "* ]]; then
    applied+=("\"$name\": \"skipped\"")
    continue
  fi
  from=$EFFECT_REV
  if [[ " $OLD_PATCHES " == *" $num "* ]]; then
    git -C "$EFFECT_SRC" show "$EFFECT_OLD_REV:_patches/typescript/$name" > "$OUT/old-patches/$name"
    p=$OUT/old-patches/$name
    from=$EFFECT_OLD_REV
  fi
  git -C "$SRC/typescript" apply --check "$p"
  git -C "$SRC/typescript" apply "$p"
  applied+=("\"$name\": \"$from\"")
done

log "diagnostics"
(cd "$SRC/typescript/tsc/internal/diagnostics" &&
  GOWORK=off go run generate.go -diagnostics ./diagnostics_generated.go -loc ./loc_generated.go -locdir ./loc \
    -locproject ../../../tools/LocProject.json -locsource ./diagnosticMessages.generated.json) > "$OUT/logs/diagnostics.log" 2>&1

log "shim overlay"
PROV=$SRC/_tools/gen_shims/providers
OV=$OUT/providers-n
mkdir -p "$OV/ls" "$OV/checker" "$OV/ls/change" "$OV/project"
# Old path API (as 7.0.2): tspath, ast, vfs, autoimport module ids, inlay hint preferences.
cp -r "$PROV/typescript-go/ast" "$PROV/typescript-go/tspath" "$PROV/typescript-go/vfs" "$OV/"
cp -r "$PROV/typescript-go/ls/autoimport" "$PROV/typescript-go/ls/lsutil" "$OV/ls/"
# New API (as a1ef42b9): LSP converters and the checker's paged link store.
cp -r "$PROV/typescript/ls/lsconv" "$OV/ls/"
cp "$PROV/typescript/checker/integration.go" "$OV/checker/"
# The change tracker is new at N, but GetChanges keys by file name (string), not tspath.RootedFilePath.
sed 's/map\[tspath.RootedFilePath\]\[\]\*lsproto.TextEdit/map[string][]*lsproto.TextEdit/; /internal\/tspath"/d' \
  "$PROV/typescript/ls/change/integration.go" > "$OV/ls/change/integration.go"
grep -q 'map\[string\]\[\]\*lsproto.TextEdit' "$OV/ls/change/integration.go"
cat > "$OV/project/integration.go" <<'EOF'
package project

import (
	"github.com/microsoft/typescript-go/internal/project"
	"github.com/microsoft/typescript-go/internal/tspath"
)

// Pin N keys API open files by tspath.Path with the file name as the value, and Snapshot.Deref takes
// no session.
func NewOpenFileSnapshotRequest(fileName string, currentDirectory string, useCaseSensitiveFileNames bool) *project.APISnapshotRequest {
	file := tspath.GetNormalizedAbsolutePath(fileName, currentDirectory)
	return &project.APISnapshotRequest{OpenFiles: map[tspath.Path]string{
		tspath.ToPath(file, currentDirectory, useCaseSensitiveFileNames): file,
	}}
}

func DerefSnapshot(snapshot *project.Snapshot, _ *project.Session) {
	snapshot.Deref()
}
EOF
sed -i 's/packagesToShim = normalizeStrings(append(packagesToShim, legacyBackportDependencies\.\.\.))/packagesToShim = normalizeStrings(append(packagesToShim, modernProviderDependencies...))/' \
  "$SRC/_tools/gen_shims/main.go"
[[ $(grep -c 'append(packagesToShim, modernProviderDependencies' "$SRC/_tools/gen_shims/main.go") == 2 ]]

log "shims"
(cd "$SRC/_tools/gen_shims" &&
  GOWORK=off go run . --repository-root "$SRC" --source-root "$SRC/typescript/tsc" \
    --module-prefix github.com/microsoft/TypeScript/tsc \
    --provider-shim-prefix github.com/microsoft/TypeScript/tsc/nshim \
    --extra-shim-root "$OV") > "$OUT/logs/gen_shims.log" 2>&1

log "go build"
(cd "$SRC" && CGO_ENABLED=0 GOAMD64=v1 go build -trimpath -o "$OUT/bin/tsc" ./typescript/tsc/cmd/tsc) > "$OUT/logs/go-build.log" 2>&1

version=$("$OUT/bin/tsc" --version)
sha=$(sha256sum "$OUT/bin/tsc" | cut -d' ' -f1)
{
  echo "{"
  echo "  \"effectRev\": \"$(git -C "$SRC" rev-parse HEAD)\","
  echo "  \"effectOldRev\": \"$(git -C "$EFFECT_SRC" rev-parse "$EFFECT_OLD_REV")\","
  echo "  \"typescriptPin\": \"$(git -C "$SRC/typescript" rev-parse HEAD)\","
  echo "  \"go\": \"$(go env GOVERSION)\","
  echo "  \"goBuild\": \"GOTOOLCHAIN=$GO_TOOLCHAIN CGO_ENABLED=0 GOAMD64=v1 go build -trimpath\","
  echo "  \"version\": \"$version\","
  echo "  \"tscSha256\": \"$sha\","
  echo "  \"patches\": {"
  (IFS=$'\n'; echo "${applied[*]}") | sed 's/^/    /; $!s/$/,/'
  echo "  }"
  echo "}"
} > "$OUT/BUILD.json"
log "$OUT/bin/tsc: $version ($sha)"
if [[ $EFFECT_REV == 47cb1ed7 && $EFFECT_OLD_REV == bddb6230 && $PIN == 673a5f17d713 && $sha != "$KNOWN_SHA" ]]; then
  log "the default revisions gave $sha, not KNOWN_SHA $KNOWN_SHA: the build is not reproducible here"
  exit 3
fi
