#!/bin/bash
# usage: sweep-hono-runtime.sh <round>. Oracle (cached) vs goport -p on the Hono runtime-tests
# configs and the other Hono root references. Line format matches /tmp/port/sweep.sh.
# Oracle output is saved once under oracle-sweep/<label>.txt and never overwritten.
# Tracked copy of target/continuation-r97-goport/tools-port/sweep-hono-runtime.sh, which stays unchanged (historical runner rule).
# Only the exit rule below differs.
. "$(dirname "$(realpath "$0")")/exit-rule.sh"
[ -n "$1" ] || { echo "usage: $0 <round>" >&2; exit 2; }
cd /home/theo/Code/sandbox/ts-rust
B=${GOPORT_BIN:-target/continuation-r97-goport/runtime/cargo-target/release/goport}
P=target/project-inputs/hono/source
O=target/continuation-r97-goport/measure/$1; OR=target/continuation-r97-goport/oracle-sweep; mkdir -p $O $OR
# A run is complete when incomplete() of exit-rule.sh is false: exit 0 or 1 and no "unported" line on
# stderr, and at the Go pins in its EXIT2_PINS also exit 2 with no Go "panic: " line.
for pair in \
 "hono-rt-bun:$P/runtime-tests/bun/tsconfig.json" \
 "hono-rt-fastly:$P/runtime-tests/fastly/tsconfig.json" \
 "hono-rt-lambda:$P/runtime-tests/lambda/tsconfig.json" \
 "hono-rt-lambda-edge:$P/runtime-tests/lambda-edge/tsconfig.json" \
 "hono-rt-node:$P/runtime-tests/node/tsconfig.json" \
 "hono-rt-workerd:$P/runtime-tests/workerd/tsconfig.json" \
 "hono-perf-scripts:$P/perf-measures/type-check/scripts/tsconfig.json" ; do
  n=${pair%%:*}; c=${pair#*:}
  if [ ! -f $OR/$n.txt ]; then t=$(mktemp -d); timeout 900 ~/.local/bin/tsgo-oracle -p $c --noEmit --pretty false --tsBuildInfoFile $t/$n.tsbuildinfo > $OR/$n.txt 2>&1; rm -rf $t; fi
  s=$(date +%s.%N); timeout 900 $B -p $c > $O/$n.out 2> $O/$n.err; e=$?
  t=$(python3 -c "import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),1))" $s $(date +%s.%N))
  if incomplete $e $O/$n.err; then m=INCOMPLETE; elif diff -q $OR/$n.txt $O/$n.out >/dev/null; then m=MATCH; else m="DIFF(+$(diff $OR/$n.txt $O/$n.out | grep -c '^>') -$(diff $OR/$n.txt $O/$n.out | grep -c '^<'))"; fi
  echo "$n exit=$e diags=$(grep -c 'error TS' $O/$n.out) oracle=$(grep -c 'error TS' $OR/$n.txt) $m ${t}s panics=$(grep -c 'panic' $O/$n.err) unported=$(grep -c '^unported' $O/$n.err)"
done
