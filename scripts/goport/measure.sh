#!/bin/bash
# usage: measure.sh <round>
cd /home/theo/Code/sandbox/ts-rust
B=${GOPORT_BIN:-target/continuation-r97-goport/runtime/cargo-target/release/goport}
O=target/continuation-r97-goport/measure/$1; mkdir -p $O
run() { n=$1; c=$2
  s=$(date +%s.%N); timeout 600 $B -p $c > $O/$n.out 2> $O/$n.err; e=$?; python3 -c "import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),2),\"s\")" $s $(date +%s.%N) > $O/$n.time
  echo "$n exit=$e diags=$(grep -c 'error TS' $O/$n.out) $(cat $O/$n.time | tail -1)"
  grep -v '^unported' $O/$n.err | sort | uniq -c | sort -nr | head -8
  grep '^unported' $O/$n.err | sort -k3 -nr | head -30
}
run query target/project-inputs/query/source/packages/query-core/tsconfig.prod.json
run hono target/project-inputs/hono/source/tsconfig.build.json
# Deliberate-error copies: goport output must equal the saved oracle output.
cd target/continuation-r97-goport
for id in Q-E1 Q-E2 Q-E3 Q-E4 Q-E5 H-E1; do
  case $id in Q*) c=errcopies/$id/packages/query-core/tsconfig.prod.json;; H*) c=errcopies/$id/tsconfig.build.json;; esac
  timeout 600 $( [[ $B = /* ]] && echo $B || echo ../../$B ) -p $c > measure/$1/$id.out 2> measure/$1/$id.err
  if diff -q errcopies-oracle/$id.txt measure/$1/$id.out >/dev/null; then echo "$id MATCH"; else echo "$id DIFF ($(wc -l < measure/$1/$id.out) lines, unported $(grep -c '^unported' measure/$1/$id.err))"; fi
done
