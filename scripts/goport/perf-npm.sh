#!/usr/bin/env bash
# Times tsc run directly and through npm, for a Rust and a Go package set (npm-pack.sh) installed
# with npm (npm-test.sh makes <work-dir>/proj). Cells, with hyperfine -N (mean of the runs):
#   rs-direct   <rs-proj>/node_modules/@typescript/typescript-linux-x64/lib/tsc
#   rs-npm      <rs-proj>/node_modules/.bin/tsc (the native tsc, after the postinstall)
#   rs-npm-js   /usr/bin/env node <rs-proj>/node_modules/typescript/lib/tsc.js (Go's JS launcher, as
#               without the postinstall: the same exec chain as a shebang bin/tsc)
#   go-direct   <go-proj>/node_modules/@typescript/typescript-linux-x64/lib/tsc
#   go-npm      <go-proj>/node_modules/.bin/tsc (Go's JS launcher)
# on these cells (the ratios are Go time / Rust time):
#   version     --version
#   query       a full check: tsc -p query-core/tsconfig.prod.json --noEmit
#   hono        a full check: tsc -p hono/tsconfig.build.json --noEmit --composite false
#               --incremental false (the inputs are read-only, and hono is composite)
#   hono-noop   as hono, but composite with a .tsbuildinfo per side (in the output dir) that the
#               warmup runs write: the no-change run that repeats in a watch-free dev loop
# Timing on a loaded host is noise: the script refuses to start when the 1-minute load is over
# PERF_MAX_LOAD (default 1.5). Run it on a quiet host (dbook-lan or a mini) through remote.sh, with
# both projects pushed there. PERF_RUNS sets the runs per cell (default 30).
#
# usage: perf-npm.sh <label> <rs-proj> <go-proj>
# Output: target/continuation-r97-goport/perf-npm/<label>/ (hyperfine JSON and text, table.txt).
set -euo pipefail
cd /home/theo/Code/sandbox/ts-rust
[[ $# == 3 ]] || { sed -n '15p' "$0" >&2; exit 2; }
label=$1 rs=$(realpath "$2") go=$(realpath "$3")
out=target/continuation-r97-goport/perf-npm/$label
mkdir -p "$out"
for p in "$rs" "$go"; do [[ -x $p/node_modules/.bin/tsc ]] || { echo "no npm project: $p" >&2; exit 2; }; done

max=${PERF_MAX_LOAD:-1.5}
load=$(cut -d' ' -f1 /proc/loadavg)
awk -v l="$load" -v m="$max" 'BEGIN { exit !(l <= m) }' ||
  { echo "load $load > $max on $(hostname): timing would be noise" >&2; exit 3; }

plat=node_modules/@typescript/typescript-linux-x64/lib/tsc
names=(rs-direct rs-npm rs-npm-js go-direct go-npm)
cmds=("$rs/$plat" "$rs/node_modules/.bin/tsc" "/usr/bin/env node $rs/node_modules/typescript/lib/tsc.js"
      "$go/$plat" "$go/node_modules/.bin/tsc")
P=target/project-inputs
hono="-p $P/hono/source/tsconfig.build.json --noEmit --pretty false"
declare -A args=([version]="--version"
  [query]="-p $P/query/source/packages/query-core/tsconfig.prod.json --noEmit --pretty false"
  [hono]="$hono --composite false --incremental false"
  [hono-noop]="$hono --tsBuildInfoFile $(realpath "$out")/SIDE.tsbuildinfo")
rm -f "$out"/*.tsbuildinfo
runs=${PERF_RUNS:-30}
echo "host $(hostname) load $load node $(node --version) runs $runs" > "$out/host.txt"
cells=(version query hono hono-noop)
for cell in "${cells[@]}"; do
  hf=()
  for i in "${!names[@]}"; do hf+=(-n "${names[i]}" "${cmds[i]} ${args[$cell]//SIDE/${names[i]%%-*}}"); done
  hyperfine -N --warmup 3 --runs "$runs" --export-json "$out/$cell.json" "${hf[@]}" > "$out/$cell.txt" 2>&1
done
echo "load at end $(cut -d' ' -f1 /proc/loadavg)" >> "$out/host.txt"

node - "$out" > "$out/table.txt" <<'EOF'
// A Markdown table: the means in ms, then the ratios Go / Rust.
const fs = require("fs");
const out = process.argv[2];
const names = ["rs-direct", "rs-npm", "rs-npm-js", "go-direct", "go-npm"];
const rows = [
    `| cell | ${names.join(" | ")} | direct | npm | npm, both JS launcher | saved |`,
    "|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|",
];
for (const cell of ["version", "query", "hono", "hono-noop"]) {
    const results = JSON.parse(fs.readFileSync(`${out}/${cell}.json`, "utf8")).results;
    const mean = Object.fromEntries(results.map(r => [r.command, r.mean * 1000]));
    const ratio = (go, rs) => (mean[go] / mean[rs]).toFixed(2);
    const cols = [...names.map(n => mean[n].toFixed(1)), ratio("go-direct", "rs-direct"), ratio("go-npm", "rs-npm"),
        ratio("go-npm", "rs-npm-js"), (mean["rs-npm-js"] - mean["rs-npm"]).toFixed(1)];
    rows.push(`| ${cell} | ${cols.join(" | ")} |`);
}
console.log(rows.join("\n"));
EOF
cat "$out/host.txt" "$out/table.txt"
