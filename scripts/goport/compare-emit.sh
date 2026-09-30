#!/usr/bin/env bash
# Compare goport_emit output with the tsgo oracle over the emit project list.
# Usage: compare-emit.sh <goport_emit binary> <label> [project-label-filter-regex]
# Oracle output is cached in /tmp/goport-emit-oracle/<project>. goport output
# goes to /tmp/goport-emit-<label>/<project>. Nothing is written into project
# inputs. Prints one line per project and a summary in
# /tmp/goport-emit-<label>/summary.txt. Exit 0 when every project matches.
# Tracked copy of target/continuation-r97-goport/emit/compare-emit.sh (gate.sh and bound2.sh run it) with one
# rule more: a project where Go writes no file (noEmitOnError with diagnostics: redux-toolkit at 673a5f17d713,
# ts#64431) is MATCH when goport writes no file either, the exits are equal and the two logs (the diagnostics)
# are byte-equal. The old copy says DIFF for every project without Go output. Where Go writes files for every
# project (all 45 at 16c25522e123) the lines are the same.
set -uo pipefail
bin="$(realpath "$1")"; label="$2"; filter="${3:-.}"
P=/home/theo/Code/sandbox/ts-rust/target/project-inputs
X=/home/theo/Code/sandbox/ts-rust/target/project-inputs-extra
ORACLE=~/.local/bin/tsgo-oracle
OC=/tmp/goport-emit-oracle; OUT=/tmp/goport-emit-$label
mkdir -p "$OC" "$OUT"
# label|cwd|config (relative to cwd)|extra flags for both tools
projects=(
 "query-core-prod|$P/query/source/packages/query-core|tsconfig.prod.json|"
 "query-core-prod-js|$P/query/source/packages/query-core|tsconfig.prod.json|--emitDeclarationOnly false --sourceMap --declarationMap"
 "hono-build|$P/hono/source|tsconfig.build.json|"
 "hono-build-js|$P/hono/source|tsconfig.build.json|--emitDeclarationOnly false --sourceMap --declarationMap"
 "ts-pattern|$P/ts-pattern/source|tsconfig.json|"
 "zod-build|$P/zod/source/packages/zod|tsconfig.build.json|"
 "pathe|$P/wave202-pathe-inputs-1/project|tsconfig.json|--noEmit false --declaration"
 "ufo|$P/wave202-ufo-inputs-1/project|tsconfig.json|--declaration"
 "tanstack-table-core|$X/tanstack-table-core/src/packages/table-core|tsconfig.json|--noEmit false"
 "tanstack-router-core|$X/tanstack-router-core/src/packages/router-core|tsconfig.build.json|--noEmit false"
 "tanstack-form-core|$X/tanstack-form-core/src/packages/form-core|tsconfig.json|--noEmit false"
 "tanstack-query-other|$X/tanstack-query-other/source|packages/query-async-storage-persister/tsconfig.prod.json|--noEmit false"
 "trpc-server|$X/trpc-server/src/packages/server|tsconfig.json|--noEmit false"
 "valibot|$X/valibot|tsconfig.goport.json|--noEmit false"
 "remeda|$X/remeda/src/packages/remeda|tsconfig.source.json|--noEmit false"
 "date-fns|$X/date-fns/src-tree|pkgs/core/tsconfig.dist.json|--noEmit false"
 "neverthrow|$X/neverthrow|tsconfig.check.json|--noEmit false"
 "superjson|$X/superjson|tsconfig.check.json|--noEmit false"
 "drizzle-orm|$X/drizzle-orm/src/drizzle-orm|../../tsconfig.tsgo.json|--noEmit false"
 "elysia|$X/elysia/src|tsconfig.json|--noEmit false"
 "tanstack-virtual-core|$X/tanstack-virtual-core/src/packages/virtual-core|tsconfig.json|--noEmit false"
 "tanstack-store|$X/tanstack-store/src/packages/store|tsconfig.json|--noEmit false"
 "zustand|$X/zustand/src|tsconfig.json|--noEmit false"
 "jotai|$X/jotai/src|tsconfig.json|--noEmit false"
 "immer|$X/immer/src|tsconfig.json|--noEmit false"
 "rxjs|$X/rxjs/src/packages/rxjs|.tshy/esm.json|--noEmit false"
 "fp-ts|$X/fp-ts/src|tsconfig.json|--noEmit false"
 "redux-toolkit|$X/reduxjs-redux-toolkit-packages-toolkit/src/packages/toolkit|tsconfig.test.json|--noEmit false"
 "ky|$X/ky/src|tsconfig.test.json|--noEmit false"
 "mobx|$X/mobxjs-mobx-packages-mobx/src/packages/mobx|tsconfig.json|--noEmit false"
 "yup|$X/yup|tsconfig.goport.json|--noEmit false"
 "colinhacks-zod|$X/colinhacks-zod/src|tsconfig.json|--noEmit false"
 "ts-eslint-utils|$X/typescript-eslint-typescript-eslint-packages-utils/src/packages/utils|tsconfig.build.json|--noEmit false"
 "vitest-expect|$X/vitest-dev-vitest-packages-expect/src/packages/expect|tsconfig.json|--noEmit false"
 "h3|$X/h3/src|tsconfig.json|--noEmit false"
 "hono-zod-validator|$X/honojs-middleware-packages-zod-validator/src/packages/zod-validator|tsconfig.spec.json|--noEmit false"
 # Source map variants of larger projects.
 "maps-date-fns|$X/date-fns/src-tree|pkgs/core/tsconfig.dist.json|--noEmit false --sourceMap --declarationMap"
 "maps-valibot|$X/valibot|tsconfig.goport.json|--noEmit false --sourceMap --declaration --declarationMap"
 "maps-drizzle-orm|$X/drizzle-orm/src/drizzle-orm|../../tsconfig.tsgo.json|--noEmit false --sourceMap --declaration --declarationMap"
 "maps-rxjs|$X/rxjs/src/packages/rxjs|.tshy/esm.json|--noEmit false --sourceMap --declarationMap"
 "maps-redux-toolkit|$X/reduxjs-redux-toolkit-packages-toolkit/src/packages/toolkit|tsconfig.test.json|--noEmit false --sourceMap --declaration --declarationMap"
 "maps-elysia|$X/elysia/src|tsconfig.json|--noEmit false --sourceMap --declaration --declarationMap"
 "maps-fp-ts|$X/fp-ts/src|tsconfig.json|--noEmit false --inlineSourceMap --inlineSources --declaration"
 "maps-zod-build|$P/zod/source/packages/zod|tsconfig.build.json|--sourceMap --declarationMap --removeComments"
 "maps-mobx|$X/mobxjs-mobx-packages-mobx/src/packages/mobx|tsconfig.json|--noEmit false --sourceMap --declaration --declarationMap"
)
run_one() {
  IFS='|' read -r n cwd cfg flags <<< "$1"
  # shellcheck disable=SC2086
  stamp="$OUT/.stamp-$n"; touch "$stamp"
  if [ ! -f "$OC/$n.done" ]; then
    rm -rf "${OC:?}/$n"; mkdir -p "$OC/$n"
    (cd "$cwd" && timeout 1200 "$ORACLE" -p "$cfg" --outDir "$OC/$n/out" --tsBuildInfoFile "$OC/$n/tsbi" --pretty false $flags > "$OC/$n/log" 2>&1; echo $? > "$OC/$n/rc")
    touch "$OC/$n.done"
  fi
  rm -rf "${OUT:?}/$n"; mkdir -p "$OUT/$n"
  s=$(date +%s)
  (cd "$cwd" && timeout 1200 "$bin" -p "$cfg" --outDir "$OUT/$n/out" --pretty false $flags > "$OUT/$n/log" 2> "$OUT/$n/err"); e=$?
  t=$(( $(date +%s) - s ))
  # Guard: neither tool may write into the project. Report any new file.
  leaked=$(find "$cwd" -newer "$stamp" -type f -not -path '*/node_modules/*' 2>/dev/null | head -5)
  [ -n "$leaked" ] && echo "$n WROTE-INTO-PROJECT: $leaked"
  mkdir -p "$OC/$n/out" "$OUT/$n/out"
  diff -rq "$OC/$n/out" "$OUT/$n/out" > "$OUT/$n/diffq.txt" 2>&1
  diff -r "$OC/$n/out" "$OUT/$n/out" > "$OUT/$n/diff.txt" 2>&1
  no=$(find "$OC/$n/out" -type f | wc -l); ng=$(find "$OUT/$n/out" -type f | wc -l)
  nd=$(grep -c '^Files .* differ$' "$OUT/$n/diffq.txt"); nonly=$(grep -c '^Only in' "$OUT/$n/diffq.txt")
  if [ "$nd" -eq 0 ] && [ "$nonly" -eq 0 ] && { [ "$no" -gt 0 ] || { [ "$ng" -eq 0 ] && [ "$e" = "$(cat "$OC/$n/rc")" ] &&
    cmp -s "$OC/$n/log" "$OUT/$n/log"; }; }; then m=MATCH; else m=DIFF; fi
  echo "$n $m oracle=$no goport=$ng differ=$nd only=$nonly rc=$e oracle_rc=$(cat "$OC/$n/rc") ${t}s panics=$(grep -c panic "$OUT/$n/err") unported=$(grep -c '^unported' "$OUT/$n/err")"
}
export -f run_one; export OC OUT bin ORACLE
printf '%s\n' "${projects[@]}" | grep -E "^($filter)" | xargs -d '\n' -P "${JOBS:-4}" -I{} bash -c 'run_one "$@"' _ {} | tee "$OUT/summary.txt"
! grep -q ' DIFF ' "$OUT/summary.txt"
