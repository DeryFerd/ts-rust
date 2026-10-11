#!/usr/bin/env bash
# Blacksmith testboxes: a warm 32 vCPU Linux x64 runner (.github/workflows/testbox.yml) that runs a command
# against this worktree's files. `run` syncs this worktree to the testbox (the CLI's rsync) and runs the
# command in the synced repo root. target/ and the cargo registry sit on sticky disks.
# usage: testbox.sh help                      this text
#        testbox.sh warmup                    start a testbox; saves its ID to target/testbox-id
#        testbox.sh run <command...>          sync this worktree, then run the command with the testbox env
#                                             (e.g. run scripts/run-cargo-capped.sh build --release -p ts_goport --bins).
#                                             Arguments keep their boundaries; use run bash -c '...' for pipes and &&
#        testbox.sh get <remote> [local]      copy a file or dir back with rsync (remote path absolute or relative
#                                             to the repo root; a trailing / copies a dir's contents)
#        testbox.sh push <path>...            copy zbook files or dirs to the same absolute paths (e.g. a bins dir)
#        testbox.sh seed [inputs|pin]...      copy the files of testbox-data.txt (default both disks) to their
#                                             sticky disks (30 to 35 minutes; a rerun copies only what is
#                                             missing). Then let the testbox end on its
#                                             idle timeout: a stopped job is cancelled, and a cancelled job does
#                                             not commit its sticky disks
#        testbox.sh status | stop | list      the saved testbox's status, stop it (no sticky disk commit), list
# The gate and the oracles run as on zbook: the testbox env sets HOME=/home/theo and the workflow binds the
# workspace on /home/theo/Code/sandbox/ts-rust (testbox-data.sh). Fetch a commit that the bins name before a
# gate: run git fetch --depth=1 origin <sha>.
# TESTBOX_ID overrides the saved ID. TESTBOX_IDLE: idle minutes before the testbox stops (default 15).
# TESTBOX_REF: the ref the workflow runs from (default main: the workflow must be on the default branch).
# Auth: `blacksmith auth login` once per host (`blacksmith auth status` shows it).
set -euo pipefail
case "${1:-help}" in help | -h | --help) sed -n '2,/^set -euo/p' "$0" | sed '$d'; exit 0 ;; esac

repo_root="$(git -C "$(dirname -- "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
id_file="$repo_root/target/testbox-id"
cd "$repo_root"

saved_id() {
  local id="${TESTBOX_ID:-$(cat "$id_file" 2>/dev/null || true)}"
  [[ -n "$id" ]] || { echo "no testbox: run 'testbox.sh warmup' or set TESTBOX_ID" >&2; exit 2; }
  echo "$id"
}

# ssh_route: sets host and ssh for rsync over the CLI's own SSH route (port 64000 and the key that warmup
# saves in ~/.blacksmith/testboxes/<id>; CLI 0.4.70, see `run --debug`). The login dir is /home/runner.
ssh_route() {
  local id key
  id="$(saved_id)"
  host="$(blacksmith testbox status --id "$id" | awk -v id="$id" '$1 == id {print $3}')"
  key="$HOME/.blacksmith/testboxes/$id/id_ed25519"
  [[ -n "$host" && -f "$key" ]] || { echo "no SSH route to $id (host '$host', key $key)" >&2; exit 1; }
  ssh="ssh -p 64000 -i $key -o IdentitiesOnly=yes -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR -o Compression=no"
}

# push_paths <path>...: rsync each path to the same path on the testbox.
push_paths() {
  local host ssh p keep
  ssh_route
  # The idle loop of run-testbox does not see this SSH route: touch its activity marker while we copy.
  while :; do $ssh "runner@$host" touch .testbox-last-activity || true; sleep 60; done &
  keep=$!
  # shellcheck disable=SC2064 # expand now: keep is local, and the trap runs after the function returns
  trap "kill $keep 2>/dev/null || true" EXIT
  for p in "$@"; do
    # -s: a symlink keeps its own path on the testbox; rsync copies what it points to.
    p="$(realpath -s "$p")"
    echo "push $p"
    # A file of testbox-data.txt is a bind mount there: write it in place, not by rename.
    if [[ -d "$p" ]]; then rsync -aH --mkpath --compress --compress-choice=zstd -e "$ssh" "$p/" "runner@$host:$p/"
    else rsync -aHL --mkpath --inplace --compress --compress-choice=zstd -e "$ssh" "$p" "runner@$host:$p"; fi
  done
}

cmd="$1"
shift
case "$cmd" in
  warmup)
    rc=0
    out="$(blacksmith testbox warmup testbox.yml --ref "${TESTBOX_REF:-main}" --idle-timeout "${TESTBOX_IDLE:-15}" 2>&1)" || rc=$?
    echo "$out"
    ((rc == 0)) || exit "$rc"
    id="$(grep -oE 'tbx_[A-Za-z0-9_-]+' <<<"$out" | head -1)"
    [[ -n "$id" ]] || { echo "warmup printed no testbox ID" >&2; exit 1; }
    mkdir -p "$(dirname "$id_file")"
    echo "$id" >"$id_file"
    echo "testbox $id (saved to target/testbox-id)"
    ;;
  run)
    (($#)) || { echo "usage: testbox.sh run <command...>" >&2; exit 2; }
    printf -v remote_cmd '%q ' "$@"
    blacksmith testbox run --id "$(saved_id)" ". ~/testbox.env && $remote_cmd"
    ;;
  get)
    # rsync, not `blacksmith testbox download`: that timed out after 5 minutes on a 124 MB results dir.
    (($# == 1 || $# == 2)) || { echo "usage: testbox.sh get <remote> [local]" >&2; exit 2; }
    ssh_route
    src="$1"
    [[ "$src" == /* ]] || src="_work/ts-rust/ts-rust/$src"
    rsync -aH --compress --compress-choice=zstd -e "$ssh" "runner@$host:$src" "${2:-.}"
    ;;
  push)
    (($#)) || { echo "usage: testbox.sh push <path>..." >&2; exit 2; }
    push_paths "$@"
    ;;
  seed)
    # Read the list first: a failure inside < <(...) would not stop the script.
    manifest="$(scripts/goport/testbox-data.sh paths)"
    mapfile -t paths < <(awk -v want=" ${*:-inputs pin} " 'index(want, " " $1 " ") {print $2}' <<<"$manifest")
    ((${#paths[@]})) || { echo "no seed paths for: ${*:-inputs pin}" >&2; exit 2; }
    push_paths "${paths[@]}"
    ;;
  status) blacksmith testbox status --id "$(saved_id)" "$@" ;;
  stop)
    id="$(saved_id)"
    blacksmith testbox stop --id "$id"
    # Keep the saved ID when TESTBOX_ID stopped another testbox.
    [[ "$(cat "$id_file" 2>/dev/null || true)" != "$id" ]] || rm -f "$id_file"
    ;;
  list) blacksmith testbox list "$@" ;;
  *) echo "unknown command: $cmd (testbox.sh help)" >&2; exit 2 ;;
esac
