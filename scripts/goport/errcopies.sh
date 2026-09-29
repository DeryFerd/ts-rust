#!/bin/bash
# Creates the R97 deliberate-error copies as hardlink trees. Each edited file
# is replaced by a real copy before the edit, so the originals never change.
set -euo pipefail
R=/home/theo/Code/sandbox/ts-rust/target
E=$R/continuation-r97-goport/errcopies
mkdir -p $E
mk() { id=$1; proj=$2; file=$3; text=$4
  [ -d $E/$id ] || cp -al $R/project-inputs/$proj/source $E/$id
  f=$E/$id/$file
  cp --remove-destination "$(readlink -f $R/project-inputs/$proj/source/$file)" $f
  printf '%s\n' "$text" >> $f
  [ "$(stat -c %h $f)" = 1 ] || { echo "hardlink not broken: $f"; exit 1; }
}
QC=packages/query-core/src
mk Q-E1 query $QC/utils.ts 'export const r97E1: number = "x"'
mk Q-E2 query $QC/utils.ts 'export const r97E2 = functionalUpdate(1, 2, 3)'
mk Q-E3 query $QC/queryClient.ts 'export function r97E3(this: QueryClient) { return this.r97Missing }'
mk Q-E4 query $QC/retryer.ts 'export function r97E4() { const r97Unused = 1; return 0 }'
mk Q-E5 query $QC/types.ts 'export type R97E5 = InferDataFromTag<unknown, number>'
mk H-E1 hono src/context.ts 'export const r97E1: string = 1'
echo done
