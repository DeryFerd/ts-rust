#!/bin/bash
# usage: perf.sh <label> <goport-bin>...   (old form: perf.sh <goport-bin> <label>)
# Median of 3 wall time and peak RSS on query, hono, zod and effect for each binary.
# Runs are interleaved (run 1 of every binary, then run 2, ...), so load drift hits every
# side the same way. Compare binaries only within one perf.sh run.
# Timing on a loaded host is noise: the script refuses to start when the 1-minute load
# is over PERF_MAX_LOAD (default 1.5). PERF_WAIT=1 waits up to 30 minutes for a quiet
# host instead. zbook is rarely quiet while agents build: run it on dbook-lan or
# mini-abf9 through remote.sh, with every side on the same host.
# Output: target/continuation-r97-goport/perf/<label>/ (per-run .time files, load.txt).
set -uo pipefail
cd /home/theo/Code/sandbox/ts-rust
# tsgo on 4 KiB pages hands the work to a worker (R137), so wait4 RSS and CPU would show only the
# launcher. Measure the process that does the work.
export GOPORT_LAUNCH=0
if [[ $# -eq 2 && -x $1 && ! -x $2 ]]; then set -- "$2" "$1"; fi
[[ $# -ge 2 ]] || { sed -n '2,10p' "$0"; exit 2; }
L=$1; shift; BINS=("$@")
for b in "${BINS[@]}"; do [[ -x $b ]] || { echo "not executable: $b" >&2; exit 2; }; done
O=target/continuation-r97-goport/perf/$L; mkdir -p "$O"; P=target/project-inputs

exec 8> /tmp/goport-perf.lock
flock -n 8 || { echo "another perf.sh run holds /tmp/goport-perf.lock; waiting"; flock 8; }
max=${PERF_MAX_LOAD:-1.5}
load() { cut -d' ' -f1 /proc/loadavg; }
quiet() { awk -v l="$(load)" -v m="$max" 'BEGIN { exit !(l <= m) }'; }
if ! quiet; then
  [[ ${PERF_WAIT:-0} == 1 ]] || { echo "load $(load) > $max on $(hostname): timing would be noise. Use a quiet host or PERF_WAIT=1." >&2; exit 3; }
  for _ in $(seq 180); do quiet && break; sleep 10; done
  quiet || { echo "load still $(load) after 30 minutes" >&2; exit 3; }
fi

PAIRS=("query:$P/query/source/packages/query-core/tsconfig.prod.json" "hono:$P/hono/source/tsconfig.build.json"
       "zod:$P/zod/source/packages/zod/tsconfig.json" "effect:$P/effect/source/packages/effect/tsconfig.json")
for i in 1 2 3; do
  for pair in "${PAIRS[@]}"; do
    n=${pair%%:*} c=${pair#*:}
    for k in "${!BINS[@]}"; do
      echo "$i $n bin$k load $(load)" >> "$O/load.txt"
      /usr/bin/time -f "%e %M" -o "$O/$n-bin$k-$i.time" "${BINS[k]}" -p "$c" > /dev/null 2>&1
    done
  done
done
echo "host $(hostname), load at end $(load), max seen $(awk '{print $5}' "$O/load.txt" | sort -n | tail -1)"
for pair in "${PAIRS[@]}"; do
  n=${pair%%:*}
  for k in "${!BINS[@]}"; do
    med=$(for f in "$O/$n-bin$k"-*.time; do tail -1 "$f"; done | sort -n | sed -n 2p)
    # One binary keeps the old line format ("<project> <seconds> <KiB>").
    if [[ ${#BINS[@]} -eq 1 ]]; then echo "$n $med"; else echo "$n ${BINS[k]} $med"; fi
  done
done
