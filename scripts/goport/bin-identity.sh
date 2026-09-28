#!/usr/bin/env bash
# Output identity of two builds of the same source (for example stable and nightly rustc).
# For Query core, Hono, zod and effect it runs, with each bin dir:
#   tsgo -p <emit config> <emit flags> --outDir ... (diagnostics, exit code, emitted tree)
#   goport -p <check config>                         (diagnostics, exit code)
# and compares the two sides byte for byte. Writes only under <out-dir>; project inputs are
# only read (emit goes to --outDir and --tsBuildInfoFile under <out-dir>).
# usage: bin-identity.sh <out-dir> <bins-a> <bins-b>
# Exit 0 when every output is equal.
set -uo pipefail
[[ $# -eq 3 ]] || { sed -n '2,9p' "$0"; exit 2; }
OUT=$(realpath -m "$1") A=$(realpath "$2") B=$(realpath "$3")
P=/home/theo/Code/sandbox/ts-rust/target/project-inputs
for d in "$A" "$B"; do for b in tsgo goport; do [[ -x $d/$b ]] || { echo "missing $d/$b" >&2; exit 2; }; done; done
rm -rf "$OUT"; mkdir -p "$OUT"
# name|cwd|check config|emit config|emit flags (as in emit/compare-emit.sh)
projects=(
  "query|$P/query/source/packages/query-core|tsconfig.prod.json|tsconfig.prod.json|--emitDeclarationOnly false --sourceMap --declarationMap"
  "hono|$P/hono/source|tsconfig.build.json|tsconfig.build.json|--emitDeclarationOnly false --sourceMap --declarationMap"
  "zod|$P/zod/source/packages/zod|tsconfig.json|tsconfig.build.json|"
  "effect|$P/effect/source/packages/effect|tsconfig.json|tsconfig.json|--noEmit false"
)
fail=0
for p in "${projects[@]}"; do
  IFS='|' read -r name cwd check emit flags <<< "$p"
  for side in a b; do
    bins=$A; [[ $side == b ]] && bins=$B
    o=$OUT/$side/$name; mkdir -p "$o"
    # shellcheck disable=SC2086
    (cd "$cwd" && "$bins/tsgo" -p "$emit" $flags --pretty false --outDir "$o/emit" \
      --tsBuildInfoFile "$o/tsbuildinfo" > "$o/tsgo.out" 2> "$o/tsgo.err"; echo $? > "$o/tsgo.rc")
    (cd "$cwd" && "$bins/goport" -p "$check" > "$o/goport.out" 2> "$o/goport.err"; echo $? > "$o/goport.rc")
  done
  a=$OUT/a/$name b=$OUT/b/$name
  res=()
  for f in tsgo.out tsgo.rc goport.out goport.rc; do cmp -s "$a/$f" "$b/$f" || res+=("$f"); done
  diff -r --exclude=tsbuildinfo "$a/emit" "$b/emit" > "$OUT/$name.emit.diff" 2>&1 || res+=(emit)
  files=$(find "$a/emit" -type f 2>/dev/null | wc -l)
  if ((${#res[@]} == 0)); then st=EQUAL; else st="DIFF(${res[*]})"; fail=1; fi
  echo "$name $st emit_files=$files tsgo_rc=$(cat "$a/tsgo.rc")/$(cat "$b/tsgo.rc") tsgo_diag_lines=$(wc -l < "$a/tsgo.out") goport_rc=$(cat "$a/goport.rc")/$(cat "$b/goport.rc") goport_diag_lines=$(wc -l < "$a/goport.out")" | tee -a "$OUT/summary.txt"
done
exit $fail
