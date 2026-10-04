#!/usr/bin/env bash
# Installs an npm-pack.sh package set into a fresh project and checks that tsc through npm gives
# the same output as the native tsc run directly.
#
# usage: npm-test.sh [--name tsc-rs] <pkg-dir> <work-dir>
#   --name      the package set of npm-pack.sh --name (default typescript). tsc-rs: the main package
#               tsc-rs, bin tsc-rs, platform package @tsc-rs/linux-x64.
#   <pkg-dir>   npm-pack.sh output (the main and the linux-x64 .tgz files)
#   <work-dir>  made fresh: <work-dir>/proj (the npm project) and <work-dir>/out (tsc output)
# Checks:
#   - bin/tsc: a symlink to the platform package's tsc when the package has the postinstall
#     (Rust), else Go's JS launcher.
#   - --version, and --listFilesOnly lists the lib files of the platform package's lib dir.
#   - query and hono, tsc -p <cfg> --outDir <out>: stdout, exit code and the emitted files are the
#     same for the direct run (platform lib/tsc), node_modules/.bin/tsc and the JS launcher
#     (node node_modules/typescript/lib/tsc.js, the fallback when the postinstall did not run).
# Prints one line per check and ends with "npm-test: PASS" or "npm-test: FAIL (<n>)".
set -uo pipefail
repo=/home/theo/Code/sandbox/ts-rust
usage() { sed -n '5,9p' "$0" >&2; exit 2; }
name=typescript
if [[ ${1:-} == --name ]]; then [[ $# -ge 2 ]] || usage; name=$2; shift 2; fi
case $name in
  typescript) plat=@typescript/typescript-linux-x64 bin=tsc ;;
  tsc-rs) plat=@tsc-rs/linux-x64 bin=tsc-rs ;;
  *) usage ;;
esac
[[ $# == 2 ]] || usage
pkg=$(realpath "$1") work=$(realpath -m "$2")
proj="$work/proj" out="$work/out"
rm -rf "$work"
mkdir -p "$proj" "$out"
plat_tgz=${plat#@}
tgz=("$pkg/${plat_tgz/\//-}"-*.tgz "$pkg/$name"-[0-9]*.tgz)
[[ ${#tgz[@]} == 2 && -f ${tgz[0]} && -f ${tgz[1]} ]] || { echo "no package set in $pkg" >&2; exit 2; }
echo '{"name":"npm-test","private":true}' > "$proj/package.json"
(cd "$proj" && npm install --offline --no-audit --no-fund --silent "${tgz[@]}") || { echo "npm install failed" >&2; exit 1; }

fails=0
check() { # check <name> <ok 0|1> [detail]
  if [[ $2 == 0 ]]; then echo "ok   $1"; else echo "FAIL $1${3:+: $3}"; fails=$((fails + 1)); fi
}
nm="$proj/node_modules"
direct="$nm/$plat/lib/tsc"
declare -A ways=([direct]="$direct" [npm]="$nm/.bin/$bin" [js]="node $nm/$name/lib/tsc.js")

if grep -q '"postinstall"' "$nm/$name/package.json"; then
  [[ -L $nm/$name/bin/$bin && $(realpath "$nm/$name/bin/$bin") == "$(realpath "$direct")" ]]
  check "bin/$bin is a symlink to the platform tsc" $? "$(ls -l "$nm/$name/bin/$bin")"
else
  [[ ! -L $nm/$name/bin/$bin ]] && head -1 "$nm/$name/bin/$bin" | grep -q node
  check "bin/$bin is Go's JS launcher" $?
fi

want=$("$direct" --version)
for w in npm js; do
  [[ $(${ways[$w]} --version) == "$want" ]]
  check "$w --version: $want" $?
done

echo > "$out/a.ts"
lib_dir=$(realpath "$(dirname "$direct")")
for w in direct npm js; do
  listed=$(cd "$out" && ${ways[$w]} --listFilesOnly --lib es5 a.ts)
  grep -q "^$lib_dir/lib.es5.d.ts$" <<< "$listed"
  check "$w lists $lib_dir/lib.es5.d.ts" $? "$(head -1 <<< "$listed")"
done

P=$repo/target/project-inputs
declare -A cfgs=([query]=$P/query/source/packages/query-core/tsconfig.prod.json [hono]=$P/hono/source/tsconfig.build.json)
for p in query hono; do
  for w in direct npm js; do
    (cd "$out" && ${ways[$w]} -p "${cfgs[$p]}" --outDir "$out/$p-$w" --pretty false > "$out/$p-$w.stdout" 2>&1)
    echo "exit $?" >> "$out/$p-$w.stdout"
  done
  for w in npm js; do
    cmp -s "$out/$p-direct.stdout" "$out/$p-$w.stdout"
    check "$p $w stdout and exit code equal direct ($(tail -1 "$out/$p-direct.stdout"), $(($(wc -l < "$out/$p-direct.stdout") - 1)) lines)" $?
    diff -rq "$out/$p-direct" "$out/$p-$w" > /dev/null
    check "$p $w emit equals direct ($(find "$out/$p-direct" -type f | wc -l) files)" $?
  done
done

if ((fails)); then echo "npm-test: FAIL ($fails)"; exit 1; fi
echo "npm-test: PASS"
