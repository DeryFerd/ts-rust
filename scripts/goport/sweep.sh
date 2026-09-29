#!/bin/bash
# usage: sweep.sh <round>. Oracle (cached) vs goport on more real project configs.
. "$(dirname "$(realpath "$0")")/exit-rule.sh" || exit 2
cd /home/theo/Code/sandbox/ts-rust
B=${GOPORT_BIN:-target/continuation-r97-goport/runtime/cargo-target/release/goport}
P=target/project-inputs
O=target/continuation-r97-goport/measure/$1; OR=target/continuation-r97-goport/oracle-sweep; mkdir -p $O $OR
# A run is complete when incomplete() of exit-rule.sh is false: exit 0 or 1 and no "unported" line on
# stderr, and at the Go pins in its EXIT2_PINS also exit 2 with no Go "panic: " line.
for pair in \
 "query-core-tests:$P/query/source/packages/query-core/tsconfig.json" \
 "query-core-legacy:$P/query/source/packages/query-core/tsconfig.legacy.json" \
 "hono-spec:$P/hono/source/tsconfig.spec.json" \
 "hono-full:$P/hono/source/tsconfig.json" \
 "ts-pattern-tests:$P/ts-pattern/source/tests/tsconfig.json" \
 "svelte:$P/svelte/source/packages/svelte/tsconfig.json" \
 "svelte-runtime:$P/svelte/source/packages/svelte/tsconfig.runtime.json" \
 "effect:$P/effect/source/packages/effect/tsconfig.json" \
 "pathe:$P/wave202-pathe-inputs-1/project/tsconfig.json" \
 "ufo:$P/wave202-ufo-inputs-1/project/tsconfig.json" \
 "tiny-invariant:$P/wave202-tiny-invariant-inputs-1/project/tsconfig.json" \
 "rhf-app:$P/react-hook-form/source/app/tsconfig.json" ; do
  n=${pair%%:*}; c=${pair#*:}
  if [ ! -f $OR/$n.txt ]; then timeout 900 ~/.local/bin/tsgo-oracle -p $c --noEmit --pretty false --tsBuildInfoFile /tmp/goport-tsbi-$n > $OR/$n.txt 2>&1; fi
  s=$(date +%s.%N); timeout 900 $B -p $c > $O/$n.out 2> $O/$n.err; e=$?
  t=$(python3 -c "import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),1))" $s $(date +%s.%N))
  if incomplete $e $O/$n.err; then m=INCOMPLETE; elif diff -q $OR/$n.txt $O/$n.out >/dev/null; then m=MATCH; else m="DIFF(+$(diff $OR/$n.txt $O/$n.out | grep -c '^>') -$(diff $OR/$n.txt $O/$n.out | grep -c '^<'))"; fi
  echo "$n exit=$e diags=$(grep -c 'error TS' $O/$n.out) oracle=$(grep -c 'error TS' $OR/$n.txt) $m ${t}s panics=$(grep -c 'panic' $O/$n.err) unported=$(grep -c '^unported' $O/$n.err)"
done
