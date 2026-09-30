#!/usr/bin/env bash
# Installs an npm-pack.sh package set into a fresh project and checks that tsc through npm gives
# the same output as the native tsc run directly.
#
# usage: npm-test.sh <pkg-dir> <work-dir>
#   <pkg-dir>   npm-pack.sh output (the two .tgz files)
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
[[ $# == 2 ]] || { sed -n '5,7p' "$0" >&2; exit 2; }
pkg=$(realpath "$1") work=$(realpath -m "$2")
proj="$work/proj" out="$work/out"
rm -rf "$work"
mkdir -p "$proj" "$out"
tgz=("$pkg"/typescript-typescript-linux-x64-*.tgz "$pkg"/typescript-[0-9]*.tgz)
[[ ${#tgz[@]} == 2 && -f ${tgz[0]} && -f ${tgz[1]} ]] || { echo "no package set in $pkg" >&2; exit 2; }
echo '{"name":"npm-test","private":true}' > "$proj/package.json"
(cd "$proj" && npm install --offline --no-audit --no-fund --silent "${tgz[@]}") || { echo "npm install failed" >&2; exit 1; }

fails=0
check() { # check <name> <ok 0|1> [detail]
  if [[ $2 == 0 ]]; then echo "ok   $1"; else echo "FAIL $1${3:+: $3}"; fails=$((fails + 1)); fi
}
nm="$proj/node_modules"
direct="$nm/@typescript/typescript-linux-x64/lib/tsc"
declare -A ways=([direct]="$direct" [npm]="$nm/.bin/tsc" [js]="node $nm/typescript/lib/tsc.js")

if grep -q '"postinstall"' "$nm/typescript/package.json"; then
  [[ -L $nm/typescript/bin/tsc && $(realpath "$nm/typescript/bin/tsc") == "$(realpath "$direct")" ]]
  check "bin/tsc is a symlink to the platform tsc" $? "$(ls -l "$nm/typescript/bin/tsc")"
else
  [[ ! -L $nm/typescript/bin/tsc ]] && head -1 "$nm/typescript/bin/tsc" | grep -q node
  check "bin/tsc is Go's JS launcher" $?
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
