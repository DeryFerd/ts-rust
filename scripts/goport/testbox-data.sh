#!/usr/bin/env bash
# zbook's layout on a Blacksmith testbox, so the gate and the LSP and API oracles run there unchanged.
# Their tools read fixed paths under /home/theo (the repo, ~/.local/bin, ~/.explore/repos). The files of
# testbox-data.txt sit on two sticky disks; `testbox.sh seed` fills them from zbook.
# usage: testbox-data.sh paths         the list for main's Go pin: <disk> <path>
#        testbox-data.sh mount DATA    (workflow) bind DATA/<disk><path> on each path, the Go checkout on the
#                                      pin's goCheckout, and the workspace on the repo's zbook path
#        testbox-data.sh umount        (workflow) undo mount, so the sticky disks can unmount and commit
set -euo pipefail
case "${1:-help}" in help | -h | --help) sed -n '2,/^set -euo/p' "$0" | sed '$d'; exit 0 ;; esac

REPO=/home/theo/Code/sandbox/ts-rust
here="$(cd "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
work="$(git -C "$here" rev-parse --show-toplevel)"
cd "$work"
# main's Go pin, as the workflow resolves it (AGENTS.md, "Pin").
key=$(jq -r '.batch.upstreamPin.to // empty' docs/typechecker-state/current.json)
pin=$(python3 scripts/upstream/pin.py show ${key:+"$key"})

paths() {
  local k o
  k=$(jq -r .key <<<"$pin") o=$(jq -r '.oracle.sha256[:12]' <<<"$pin")
  grep -vE '^(#|$)' "$here/testbox-data.txt" | sed "s/@PIN@/$k/g; s/@ORACLE@/$o/g"
}
# A repo path is bound under the workspace, so the bind of the workspace on $REPO shows it too.
local_path() { echo "${1/#$REPO/$work}"; }

case "$1" in
  paths) paths ;;
  mount)
    data=${2:?usage: testbox-data.sh mount DATA}
    sudo install -d -o "$(id -u)" -g "$(id -g)" /home/theo
    while read -r disk path; do
      src=$data/$disk$path dest=$(local_path "$path")
      if [[ $path == */ ]]; then mkdir -p "$src" "$dest"
      else mkdir -p "$(dirname "$src")" "$(dirname "$dest")"; touch "$src" "$dest"; fi
      sudo mount --bind "$src" "$dest"
    done < <(paths)
    # The workflow checks out the whole Go repo at ~/go-pin (np-suite needs packages/ and node_modules).
    go=$(jq -r '(.subdir // "") as $s | .goCheckout | if $s == "" then . else rtrimstr("/" + $s) end' <<<"$pin")
    mkdir -p "$go" "$REPO"
    sudo mount --bind "$HOME/go-pin" "$go"
    sudo mount --rbind "$work" "$REPO"
    ;;
  umount)
    sudo umount -R "$REPO" || true
    while read -r _ path; do sudo umount "$(local_path "$path")" || true; done < <(paths)
    ;;
  *) echo "unknown command: $1 (testbox-data.sh help)" >&2; exit 2 ;;
esac
