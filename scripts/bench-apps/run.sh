#!/usr/bin/env bash
# Times a full type check of each app with tsc 6, tsc 7, tsc-rs, tsc-rs --fast and bun check (hyperfine, 1 warmup,
# RUNS runs, default 5). Before the timing, one run per tool writes its exit code and errors.
# usage: scripts/bench-apps/run.sh <work-dir> [app...]   (after setup.sh; default: every app)
# Output: <work-dir>/results/<app>.json (hyperfine), <app>.errors and <app>.<tool>.diag.
# TOOLS limits a run, for example TOOLS=tsc-rs to time a new tsc-rs only. The hyperfine and errors
# files then get the tools in their name (<app>.tsc-rs.json), and summary.py puts them over the
# full run's times.
# Time on a quiet machine: the numbers are noise while something else uses the CPU.
set -euo pipefail
[[ $# -ge 1 ]] || { sed -n '4p' "$0" >&2; exit 2; }
work=$(cd "$1" && pwd); shift
# app, repo dir, tsconfig
APPS='vscode vscode src/tsconfig.json
sentry sentry tsconfig.json
playwright playwright tsconfig.json
typeorm typeorm packages/typeorm/tsconfig.bench.json
excalidraw excalidraw tsconfig.bench.json
trpc-server trpc packages/server/tsconfig.json'

# Native binaries, without the npm launchers. tsc 6 runs out of memory on VS Code and Sentry with
# Node's default heap.
# shellcheck source=scripts/bench-apps/common.sh
source "$(cd -- "$(dirname -- "$0")" && pwd)/common.sh"
bench_tools "$work"
TS6="node --max-old-space-size=16384 $work/node_modules/ts6/lib/tsc.js"
names=(tsc6 tsc7 tsc-rs tsc-rs-fast bun)
sel=()
for i in "${!names[@]}"; do [[ " ${TOOLS:-${names[*]}} " == *" ${names[$i]} "* ]] && sel+=("$i"); done
tag=${TOOLS:+.${TOOLS// /+}}
mkdir -p "$work/results"

while read -r app dir cfg; do
  [[ $# == 0 || " $* " == *" $app "* ]] || continue
  flags="-p $cfg --noEmit --incremental false"
  cmds=("$TS6 $flags --pretty false" "$GO $flags --pretty false" "$RS $flags --pretty false"
        "$RS $flags --fast --pretty false" "$BUN check $flags --no-pretty --all")
  cd "$work/repos/$dir"
  bench_measure "$work/results/$app$tag" "${cmds[@]}"
done <<<"$APPS"
