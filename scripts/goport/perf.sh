#!/bin/bash
# usage: perf.sh <goport-bin> <label>. Median of 3 wall time and peak RSS on query, hono, zod, effect.
cd /home/theo/Code/sandbox/ts-rust
B=$1; O=target/continuation-r97-goport/perf/$2; mkdir -p $O; P=target/project-inputs
for pair in "query:$P/query/source/packages/query-core/tsconfig.prod.json" "hono:$P/hono/source/tsconfig.build.json" "zod:$P/zod/source/packages/zod/tsconfig.json" "effect:$P/effect/source/packages/effect/tsconfig.json"; do
  n=${pair%%:*}; c=${pair#*:}
  for i in 1 2 3; do /usr/bin/time -f "%e %M" -o $O/$n-$i.time $B -p $c > /dev/null 2>&1; done
  echo "$n $(for f in $O/$n-*.time; do tail -1 $f; done | sort -n | sed -n 2p)"
done
