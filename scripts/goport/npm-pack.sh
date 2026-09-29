#!/usr/bin/env bash
# Builds a local linux-x64 npm package set in Go's layout at the pin, and never publishes:
#   typescript                        Go's JS launcher (bin/tsc, lib/tsc.js) and JS API (dist).
#                                     Rust: plus the postinstall npm/install.js, which swaps bin/tsc
#                                     for a symlink to the native tsc on POSIX.
#   @typescript/typescript-linux-x64  lib/tsc (the native tsc) and the lib files next to it.
# The layout follows the Go checkout's Herebyfile.mjs (npm/pack.mjs has the details).
#
# usage: npm-pack.sh <out-dir> <tsc>
#          Rust. <tsc> is a noembed tsgo stamped with the package version: for a quick build
#          GOPORT_BUILD_VERSION=<v> scripts/run-cargo-capped.sh build --release -p ts_goport
#          --bin tsgo --features noembed; for a shipped one RELEASE_VERSION=<v>
#          crates/ts_goport/scripts/build-release.sh. The package version is the version it reports.
#        npm-pack.sh --go <version> <out-dir>
#          Go. Builds tsgo at the pin as Go's release build does (Herebyfile.mjs getReleaseBuildFlags
#          and buildTsgo: -trimpath, -ldflags "-s -w -X core.version=<version>", tag noembed,
#          CGO_ENABLED=0; the Go toolchain of the pin's oracle) and packs it with Go's launcher only.
# The pin is GOPORT_PIN, else the current pin (scripts/upstream/pin.py path goCheckout).
# Output: <out-dir>/typescript, <out-dir>/typescript-linux-x64 and their tarballs
# (<out-dir>/typescript-<v>.tgz, <out-dir>/typescript-typescript-linux-x64-<v>.tgz).
set -euo pipefail
repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
usage() { sed -n '9,19p' "$0" >&2; exit 2; }

go_version=""
if [[ ${1:-} == --go ]]; then
  [[ $# == 3 ]] || usage
  go_version=$2 out=$3
else
  [[ $# == 2 ]] || usage
  out=$1 exe=$(realpath "$2")
fi
mkdir -p "$out"
out=$(realpath "$out")
go_dir=$("$repo/scripts/upstream/pin.py" path goCheckout)
build="$out/.build"
rm -rf "$build"
mkdir -p "$build"

if [[ -n $go_version ]]; then
  go_toolchain=$("$repo/scripts/upstream/pin.py" show | node -e 'process.stdout.write(JSON.parse(require("fs").readFileSync(0, "utf8")).oracle.go)')
  exe="$build/tsc"
  (cd "$go_dir" && CGO_ENABLED=0 GOTOOLCHAIN=$go_toolchain go build -trimpath \
    "-ldflags=-s -w -X github.com/microsoft/typescript-go/internal/core.version=$go_version" \
    -tags=noembed -o "$exe" ./cmd/tsgo)
  libs="$go_dir/internal/bundled/libs"
  git_head=$(git -C "$go_dir" rev-parse HEAD 2>/dev/null || "$repo/scripts/upstream/pin.py" path commit)
else
  [[ -x $exe ]] || { echo "not executable: $exe" >&2; exit 2; }
  libs="$build/libs"
  "$repo/crates/ts_goport/scripts/copy-libs.sh" "$libs"
  diff -rq "$libs" "$go_dir/internal/bundled/libs" > /dev/null ||
    { echo "the lib files of $repo differ from the pin's ($go_dir): wrong pin?" >&2; exit 1; }
  if [[ -f $(dirname "$exe")/COMMIT ]]; then git_head=$(cat "$(dirname "$exe")/COMMIT"); else git_head=$(git -C "$repo" rev-parse HEAD); fi
fi

# A noembed tsc starts only with the lib files next to it, as in the platform package.
bin="$build/bin"
cp -r "$libs" "$bin"
cp "$exe" "$bin/tsc"
reported=$("$bin/tsc" --version)
version=${reported#Version }
[[ $reported == "Version $version" && -n $version ]] || { echo "$exe --version printed '$reported'" >&2; exit 1; }
[[ -z $go_version || $version == "$go_version" ]] || { echo "$exe reports $version, not $go_version" >&2; exit 1; }
# It must be a noembed build: it lists the lib files next to it, not bundled:/// paths.
echo > "$build/a.ts"
listed=$("$bin/tsc" --listFilesOnly --lib es5 "$build/a.ts")
grep -q "^$bin/lib.es5.d.ts$" <<< "$listed" ||
  { echo "$exe is not a noembed build: it lists $(head -1 <<< "$listed")" >&2; exit 1; }

# The JS API (dist), as Go's `npm run build` of _packages/native-preview makes it (tsc -b).
src="$build/dist-src"
mkdir -p "$src"
for f in "$go_dir"/_packages/native-preview/*; do
  [[ $f == */node_modules || $f == */dist ]] || cp -r "$f" "$src/"
done
ln -s "$go_dir/_packages/native-preview/node_modules" "$src/node_modules"
node "$go_dir/node_modules/typescript/bin/tsc" -b "$src"

native_bin=()
[[ -n $go_version ]] || native_bin=(--native-bin)
node "$repo/npm/pack.mjs" --go-dir "$go_dir" --exe "$bin/tsc" --libs "$libs" --dist "$src/dist" \
  --version "$version" --git-head "$git_head" --out "$out/pkg" "${native_bin[@]}"


rm -rf "$out/typescript" "$out/typescript-linux-x64" "$out"/*.tgz
mv "$out/pkg/typescript" "$out/pkg/typescript-linux-x64" "$out/"
rmdir "$out/pkg"
for d in typescript typescript-linux-x64; do
  (cd "$out/$d" && npm pack --silent --pack-destination "$out" > /dev/null)
done
rm -rf "$build"
echo "packed $version ($([[ -n $go_version ]] && echo Go || echo Rust), pin $(basename "$go_dir")):"
ls -1 "$out"/*.tgz
