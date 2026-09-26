#!/bin/bash
# usage: measure-extra.sh <round>. Runs goport on extra real projects and diffs against oracle.
cd /home/theo/Code/sandbox/ts-rust
B=${GOPORT_BIN:-target/continuation-r97-goport/runtime/cargo-target/release/goport}
O=target/continuation-r97-goport/measure/$1; mkdir -p $O
for pair in "zod:target/project-inputs/zod/source/packages/zod/tsconfig.json" "ts-pattern:target/project-inputs/ts-pattern/source/tsconfig.json" "rhf:target/project-inputs/react-hook-form/source/tsconfig.json"; do
  n=${pair%%:*}; c=${pair#*:}
  s=$(date +%s.%N); timeout 900 $B -p $c > $O/$n.out 2> $O/$n.err; e=$?
  t=$(python3 -c "import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),1))" $s $(date +%s.%N))
  if diff -q target/continuation-r97-goport/oracle/$n.txt $O/$n.out >/dev/null; then m=MATCH; else m="DIFF(+$(diff target/continuation-r97-goport/oracle/$n.txt $O/$n.out | grep -c '^>') -$(diff target/continuation-r97-goport/oracle/$n.txt $O/$n.out | grep -c '^<'))"; fi
  echo "$n exit=$e diags=$(grep -c 'error TS' $O/$n.out) oracle=$(grep -c 'error TS' target/continuation-r97-goport/oracle/$n.txt) $m ${t}s panics=$(grep -c 'panic' $O/$n.err)"
  grep '^unported' $O/$n.err | sort -k3 -nr | head -12
done
