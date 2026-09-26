#!/usr/bin/env bash
set -euo pipefail

# Clones the protected-regression pipeline of revision FROM for revision TO:
# stage scripts, recorders, corpus scripts, runtime env and the pinned offline
# cargo home. Only revision names, the batch id and the preparation-manifest
# pin change. Outputs of FROM (closures, logs, results, binding) are not copied.
# Then run target/continuation-r<TO>-bind.py once the source is bound in state,
# and target/continuation-r<TO>-drive.sh.
# Usage: scripts/goport/clone-revision.sh <from> <to> <old-batch-id> <new-batch-id>

from=$1 to=$2 old_batch=$3 new_batch=$4
cd "$(dirname -- "${BASH_SOURCE[0]}")/../../target"
F=continuation-r$from T=continuation-r$to
edit() { sed "s/r$from/r$to/g; s/R$from/R$to/g; s/$old_batch/$new_batch/g" "$1"; }

for f in "$F"-*.sh "$F"-*.py "$F"-*.cjs; do
  case $f in *-resume-*|*-failed-*|*-interrupted-*) continue ;; esac
  n=${f/$F/$T}
  [[ -e $n ]] && { echo "exists: $n" >&2; exit 1; }
  edit "$f" > "$n"
done
mkdir "$T-current-source-corpus" "$T-runtime-env"
for f in compare-corpus.cjs compare-guarded.py compare-previous.cjs diagnostics.sh prebuild.sh preflight.py \
  protocol.py run-normal.py semantic.sh verify-producer.py; do
  edit "$F-current-source-corpus/$f" > "$T-current-source-corpus/$f"
done
for f in disabled.toml enabled.toml record-utils.cjs select-config.py preparation-manifest.json; do
  edit "$F-runtime-env/$f" > "$T-runtime-env/$f"
done
cp -a "$F-runtime-env/cargo-home" "$T-runtime-env/cargo-home"
chmod +x "$T"-*.sh "$T-current-source-corpus"/*.sh

# The manifest is pinned in two places. Both move to the new manifest hash.
manifest=$T-runtime-env/preparation-manifest.json
jq --argjson r "$to" '.plannedRevision = $r' "$manifest" > "$manifest.next" && mv "$manifest.next" "$manifest"
old_pin=$(sha256sum "$F-runtime-env/preparation-manifest.json" | cut -c1-64)
new_pin=$(sha256sum "$manifest" | cut -c1-64)
sed -i "s/$old_pin/$new_pin/g" "$T-require-bound.py" "$T-runtime-env/record-utils.cjs"
stale="$old_pin\|r$from"
[[ $old_batch == "$new_batch" ]] || stale="$stale\|$old_batch"
if grep -rl "$stale" "$T"-*.sh "$T"-*.py "$T"-*.cjs "$T-current-source-corpus" "$T-runtime-env"/*.*; then
  echo "stale references remain (listed above)" >&2
  exit 1
fi
echo "cloned $F -> $T, manifest pin $new_pin"
