#!/bin/bash
# usage: sweep-extra2.sh <round>. Re-runs goport on each prepared extra project (wave 1 + wave 2)
# and diffs against its saved oracle file. sweep-extra.sh (wave 1 only) is kept unchanged.
# Outputs go to measure/<round>/<label>.{out,err}. Saved oracle/goport files are never overwritten.
# Line format matches /tmp/port/sweep.sh and sweep-extra.sh.
# Tracked copy of target/project-inputs-extra/sweep-extra2.sh, which stays unchanged (historical runner rule).
# Only the exit rule below differs.
[ -n "$1" ] || { echo "usage: $0 <round>" >&2; exit 2; }
X=/home/theo/Code/sandbox/ts-rust/target/project-inputs-extra
B=${GOPORT_BIN:-/home/theo/Code/sandbox/ts-rust/target/continuation-r97-goport/bin/goport-r107}
# label|project dir|cwd (relative to project dir)|config (relative to cwd)|oracle file (relative to project dir)
# Same cwd and -p as the saved oracle run, so paths in output match.
# "~variant" labels are separate TS7-compatible configs outside src (see each manifest.json "variant").
# A run is complete with exit 0, 1 or 2 and no "unported" or Go "panic: " line on stderr. tsgo exits 2
# for diagnostics under --noEmit since tsgo #4407 (Go pin 16c25522e123), and goport follows the pin.
# goport also exits 2 for a kept Go panic, so that is judged by its stderr line. Exits over 2 are a crash
# (70: unported code or a Rust panic; 124: timeout; 128+N: a signal).
for entry in \
 "tanstack-table-core|tanstack-table-core|src/packages/table-core|tsconfig.json|oracle.txt" \
 "tanstack-router-core|tanstack-router-core|src/packages/router-core|tsconfig.build.json|oracle.txt" \
 "tanstack-form-core|tanstack-form-core|src/packages/form-core|tsconfig.json|oracle.txt" \
 "tanstack-query-other|tanstack-query-other|source|packages/query-async-storage-persister/tsconfig.prod.json|oracle.txt" \
 "trpc-server|trpc-server|src/packages/server|tsconfig.json|oracle.txt" \
 "valibot|valibot|.|tsconfig.goport.json|oracle.txt" \
 "remeda|remeda|src/packages/remeda|tsconfig.source.json|oracle.txt" \
 "date-fns|date-fns|src-tree|pkgs/core/tsconfig.dist.json|oracle.txt" \
 "neverthrow|neverthrow|.|tsconfig.check.json|oracle.txt" \
 "superjson|superjson|.|tsconfig.check.json|oracle.txt" \
 "drizzle-orm|drizzle-orm|src/drizzle-orm|../../tsconfig.tsgo.json|oracle.txt" \
 "elysia|elysia|src|tsconfig.json|oracle.txt" \
 "tanstack-virtual-core|tanstack-virtual-core|src/packages/virtual-core|tsconfig.json|oracle.txt" \
 "tanstack-store|tanstack-store|src/packages/store|tsconfig.json|oracle.txt" \
 "zustand|zustand|src|tsconfig.json|oracle.txt" \
 "jotai|jotai|src|tsconfig.json|oracle.txt" \
 "immer|immer|src|tsconfig.json|oracle.txt" \
 "rxjs|rxjs|src/packages/rxjs|.tshy/esm.json|oracle.txt" \
 "fp-ts|fp-ts|src|tsconfig.json|oracle.txt" \
 "fp-ts~variant|fp-ts|.|tsconfig.tsgo-variant.json|oracle.variant.txt" \
 "reduxjs-redux-toolkit-packages-toolkit|reduxjs-redux-toolkit-packages-toolkit|src/packages/toolkit|tsconfig.test.json|oracle.txt" \
 "ky|ky|src|tsconfig.test.json|oracle.txt" \
 "mobxjs-mobx-packages-mobx|mobxjs-mobx-packages-mobx|src/packages/mobx|tsconfig.json|oracle.txt" \
 "mobxjs-mobx-packages-mobx~variant|mobxjs-mobx-packages-mobx|variant|tsconfig.json|variant/oracle.txt" \
 "yup|yup|.|tsconfig.goport.json|oracle.txt" \
 "colinhacks-zod|colinhacks-zod|src|tsconfig.json|oracle.txt" \
 "colinhacks-zod~variant|colinhacks-zod|src|../variant-ts7/tsconfig.json|variant-ts7/oracle.txt" \
 "typescript-eslint-typescript-eslint-packages-utils|typescript-eslint-typescript-eslint-packages-utils|src/packages/utils|tsconfig.build.json|oracle.txt" \
 "vitest-dev-vitest-packages-expect|vitest-dev-vitest-packages-expect|src/packages/expect|tsconfig.json|oracle.txt" \
 "h3|h3|src|tsconfig.json|oracle.txt" \
 "honojs-middleware-packages-zod-validator|honojs-middleware-packages-zod-validator|src/packages/zod-validator|tsconfig.spec.json|oracle.txt" ; do
  IFS='|' read -r l n cwd c of <<< "$entry"
  OR=$X/$n/$of; O=$X/measure/$1; mkdir -p $O
  s=$(date +%s.%N); (cd $X/$n/$cwd && timeout 900 $B -p $c > $O/$l.out 2> $O/$l.err); e=$?
  t=$(python3 -c "import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),1))" $s $(date +%s.%N))
  if [ $e -gt 2 ] || grep -q "^unported\|^panic: " $O/$l.err; then m=INCOMPLETE; elif diff -q $OR $O/$l.out >/dev/null; then m=MATCH; else m="DIFF(+$(diff $OR $O/$l.out | grep -c '^>') -$(diff $OR $O/$l.out | grep -c '^<'))"; fi
  echo "$l exit=$e diags=$(grep -c 'error TS' $O/$l.out) oracle=$(grep -c 'error TS' $OR) $m ${t}s panics=$(grep -c 'panic' $O/$l.err) unported=$(grep -c '^unported' $O/$l.err)"
done
