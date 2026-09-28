#!/usr/bin/env bash
set -euo pipefail

# Clones the protected-regression pipeline of revision FROM for revision TO:
# stage scripts, recorders, corpus scripts, runtime env and the pinned offline
# cargo home. Only revision names, the batch id and the preparation-manifest
# pin change. Outputs of FROM (closures, logs, results, binding) are not copied.
# The raw-result pin in check-result.py is cleared: it names FROM's result.
# Then run target/continuation-r<TO>-bind.py once the source is bound in state,
# target/continuation-r<TO>-drive.sh, and after it `pin-raw <TO>`.
# (scripts/goport/candidate.sh open and drive do all of this.)
#
# Usage: scripts/goport/clone-revision.sh <from> <to> <old-batch-id> <new-batch-id>
#        scripts/goport/clone-revision.sh pin-raw <rev>
#   pin-raw sets `assert sha(RAW) == '...'` in target/continuation-r<rev>-check-result.py to the
#   sha256 of target/continuation-r<rev>-full-result.json. It refuses when the converted result
#   (check-result.json) already exists, so a pin never changes after the conversion.

cd "$(dirname -- "${BASH_SOURCE[0]}")/../../target"
RAW_LINE="^assert sha(RAW) == '[^']*'$"

# pin_raw <rev>: pins the raw full result of <rev> in its check-result.py (the edit root made by hand).
pin_raw() {
  local P=continuation-r$1 s
  [[ -f $P-full-result.json ]] || { echo "missing $P-full-result.json" >&2; exit 1; }
  [[ ! -e $P-check-result.json ]] || { echo "$P-check-result.json exists; the pin is final" >&2; exit 1; }
  [[ $(grep -c "$RAW_LINE" "$P-check-result.py") == 1 ]] || { echo "need exactly one raw pin line in $P-check-result.py" >&2; exit 1; }
  s=$(sha256sum "$P-full-result.json" | cut -c1-64)
  sed -i "s/$RAW_LINE/assert sha(RAW) == '$s'/" "$P-check-result.py"
  echo "pinned $P-full-result.json $s in $P-check-result.py"
}
if [[ ${1:-} == pin-raw ]]; then pin_raw "$2"; exit; fi

from=$1 to=$2 old_batch=$3 new_batch=$4
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

# The raw-result pin names FROM's result. Clear it; pin-raw sets it after the TO drive.
[[ $(grep -c "$RAW_LINE" "$T-check-result.py") == 1 ]] || { echo "need exactly one raw pin line in $T-check-result.py" >&2; exit 1; }
old_raw=$(grep "$RAW_LINE" "$F-check-result.py" | grep -o '[0-9a-f]\{64\}' || true)
sed -i "s|$RAW_LINE|assert sha(RAW) == 'unpinned: run scripts/goport/clone-revision.sh pin-raw $to after the drive'|" "$T-check-result.py"

stale="$old_pin\|r$from"
[[ -z $old_raw ]] || stale="$stale\|$old_raw"
[[ $old_batch == "$new_batch" ]] || stale="$stale\|$old_batch"
if grep -rl "$stale" "$T"-*.sh "$T"-*.py "$T"-*.cjs "$T-current-source-corpus" "$T-runtime-env"/*.*; then
  echo "stale references remain (listed above)" >&2
  exit 1
fi
echo "cloned $F -> $T, manifest pin $new_pin, raw pin cleared"
