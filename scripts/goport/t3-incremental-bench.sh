#!/usr/bin/env bash
# t3-incremental-bench.sh: cold vs incremental tsc times on a T3 Code checkout (t3inc1, 2026-10-21).
#
# Usage:
#   t3-incremental-bench.sh [-n RUNS] [-c CHANGE] [-p PROJECT] [-x FLAGS] <t3code-dir> <tsc> [<tsc>...]
#   t3-incremental-bench.sh help
#
#   -n RUNS     runs per cell (default 3; the table shows the median and min-max)
#   -c CHANGE   which edit to make (default server-config):
#                 server-config     apps/server/src/config.ts: add an optional field to the
#                                   ServerConfig service shape (about 200 server files import it)
#                 contracts-literal packages/contracts/src/baseSchemas.ts: add a DpopFailureReason literal
#                 contracts-brand   packages/contracts/src/baseSchemas.ts: ThreadId brand "ThreadId" -> "ThreadIdX"
#                 contracts-field   packages/contracts/src/orchestrationV2.ts: optional field in OrchestrationV2AppThread
#   -p PROJECT  project dir to check (default: apps/server for server-config, packages/contracts
#               for the contracts-* edits). The contracts files are external library files
#               (found through node_modules) in every other project, so only packages/contracts
#               signs them.
#   -x FLAGS    more tsc flags for every run, for example -x --isolatedModules
#   <tsc>       a tsc binary (tsc-rs lib/tsc, a Go lib/tsc or a ts-rust target/release/tsgo).
#               Use LABEL=PATH to name a column.
#
# Each tsc runs `<tsc> -p <project> --noEmit --incremental --tsBuildInfoFile <tmp> --extendedDiagnostics`
# in these cells. The checkout's tsconfig files are not changed.
#   cold      no build info
#   incr      first run after a cold run plus the edit (Theo's case)
#   revert    the run after `incr`, with the edit undone
#   nochange  a run right after a cold run, no edit
# It prints wall seconds, the incr/cold ratio, the "Emit time" of incr (the nested d.ts signature
# emits) and whether incr printed the same diagnostics as a cold run with the edit.
# The edited file is restored at exit (also on error or Ctrl-C).
#
# Go's d.ts walk against the tsc-rs noEmit fallback (affected_files.rs use_versions_for_wide_change)
# on one tsgo build: GOPORT_DTS_WALK_FALLBACK=0 turns the fallback off. Pass a wrapper script as one
# <tsc>, e.g. walk=/path/walk.sh with `GOPORT_DTS_WALK_FALLBACK=0 exec /path/tsgo "$@"`.
# Run it on a quiet machine (a boat sandbox or dbook-lan), not on zbook; compare only cells of one run.
set -euo pipefail

usage() { sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; }
[ "${1:-}" = help ] && { usage; exit 0; }

RUNS=3 CHANGE=server-config PROJECT= FLAGS=
while getopts n:c:p:x:h o; do
	case $o in
	n) RUNS=$OPTARG ;;
	c) CHANGE=$OPTARG ;;
	p) PROJECT=$OPTARG ;;
	x) FLAGS=$OPTARG ;;
	*) usage; exit 2 ;;
	esac
done
shift $((OPTIND - 1))
[ $# -ge 2 ] || { usage; exit 2; }
T3=$(cd "$1" && pwd)
shift

case $CHANGE in
server-config)
	FILE=apps/server/src/config.ts
	FROM='    readonly traceTimingEnabled: boolean;'
	TO='    readonly traceTimingEnabled: boolean;\n    readonly xBenchField?: string | undefined;'
	DEFPROJ=apps/server ;;
contracts-literal)
	FILE=packages/contracts/src/baseSchemas.ts
	FROM='  "time_window",'
	TO='  "time_window",\n  "x_bench_reason",'
	DEFPROJ=packages/contracts ;;
contracts-brand)
	FILE=packages/contracts/src/baseSchemas.ts
	FROM='makeEntityId("ThreadId")'
	TO='makeEntityId("ThreadIdX")'
	DEFPROJ=packages/contracts ;;
contracts-field)
	FILE=packages/contracts/src/orchestrationV2.ts
	FROM='export const OrchestrationV2AppThread = Schema.Struct({'
	TO='export const OrchestrationV2AppThread = Schema.Struct({\n  xBenchField: Schema.optional(Schema.String),'
	DEFPROJ=packages/contracts ;;
*) echo "unknown change: $CHANGE" >&2; exit 2 ;;
esac
PROJECT=${PROJECT:-$DEFPROJ}
[ -f "$T3/$FILE" ] || { echo "no $T3/$FILE" >&2; exit 2; }
grep -qF -- "$FROM" "$T3/$FILE" || { echo "$FILE has no line: $FROM" >&2; exit 2; }

WORK=$(mktemp -d "${TMPDIR:-/tmp}/t3-incr-bench.XXXXXX")
cp "$T3/$FILE" "$WORK/orig"
restore() { cp "$WORK/orig" "$T3/$FILE"; rm -rf "$WORK"; }
trap restore EXIT
trap 'exit 130' INT TERM

edit() {
	python3 -I -c 'import sys; p, a, b = sys.argv[1:4]; s = open(p).read(); assert a in s; open(p, "w").write(s.replace(a, b.replace("\\n", "\n"), 1))' "$T3/$FILE" "$FROM" "$TO"
}
unedit() { cp "$WORK/orig" "$T3/$FILE"; }

# run <tsc> <out-file>: one tsc run in the project; prints wall seconds.
run() {
	local s e
	s=$(date +%s.%N)
	(cd "$T3" && "$1" -p "$PROJECT" --noEmit --incremental --tsBuildInfoFile "$WORK/bi.tsbuildinfo" --extendedDiagnostics $FLAGS >"$2" 2>&1) || true
	e=$(date +%s.%N)
	awk -v s="$s" -v e="$e" 'BEGIN { printf "%.3f\n", e - s }'
}
# diags <out-file>: the diagnostic lines of a run, sorted.
diags() { grep -E '\): (error|warning|suggestion|message) TS' "$1" | sort; }
cell() { sort -n | awk '{ v[NR] = $1 } END { printf "%.2f (%.2f-%.2f)", v[int((NR + 1) / 2)], v[1], v[NR] }'; }
median() { sort -n | awk '{ v[NR] = $1 } END { printf "%.2f", v[int((NR + 1) / 2)] }'; }

printf '# %s, project %s, change %s (%s), flags [%s], %s runs, %s\n' "$T3" "$PROJECT" "$CHANGE" "$FILE" "$FLAGS" "$RUNS" "$(date -u +%FT%TZ)"
printf '%-14s %-20s %-20s %-20s %-20s %-6s %-10s %s\n' tsc cold incr revert nochange ratio incr-emit same-diags
for arg in "$@"; do
	label=${arg%%=*} tsc=${arg#*=}
	[ "$label" = "$arg" ] && label=${tsc: -14}
	: >"$WORK/cold" ; : >"$WORK/incr" ; : >"$WORK/revert" ; : >"$WORK/nochange" ; : >"$WORK/emit"
	same=yes
	for _ in $(seq "$RUNS"); do
		unedit; rm -f "$WORK/bi.tsbuildinfo"
		run "$tsc" "$WORK/o.cold" >>"$WORK/cold"
		run "$tsc" "$WORK/o.nochange" >>"$WORK/nochange"
		edit
		run "$tsc" "$WORK/o.incr" >>"$WORK/incr"
		grep -E '^Emit time' "$WORK/o.incr" | awk '{ sub("s", "", $3); print $3 }' >>"$WORK/emit"
		unedit
		run "$tsc" "$WORK/o.revert" >>"$WORK/revert"
	done
	# Same diagnostics as a cold run with the edit?
	edit; rm -f "$WORK/bi.tsbuildinfo"
	run "$tsc" "$WORK/o.coldedit" >/dev/null
	cmp -s <(diags "$WORK/o.incr") <(diags "$WORK/o.coldedit") || same=no
	unedit
	c=$(median <"$WORK/cold") i=$(median <"$WORK/incr")
	printf '%-14s %-20s %-20s %-20s %-20s %-6s %-10s %s\n' "$label" \
		"$(cell <"$WORK/cold")" "$(cell <"$WORK/incr")" "$(cell <"$WORK/revert")" "$(cell <"$WORK/nochange")" \
		"$(awk -v i="$i" -v c="$c" 'BEGIN { printf "%.2f", i / c }')" "$(median <"$WORK/emit")s" "$same"
done
