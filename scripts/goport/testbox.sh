#!/usr/bin/env bash
# Blacksmith testboxes: a warm 32 vCPU Linux x64 runner (.github/workflows/testbox.yml) that runs a command
# against this worktree's files. `run` syncs this worktree to the testbox (the CLI's rsync) and runs the
# command in the synced repo root. target/, the cargo registry and the files of testbox-data.txt sit on
# sticky disks.
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
#                                             missing), then release: a stopped testbox does not commit them
#        testbox.sh status | list             the saved testbox's status, list active testboxes
#        testbox.sh stop                      end the saved testbox now. stop cancels the job, and the sticky disks
#                                             do not commit after a cancelled step: the writes to them are lost
#        testbox.sh release                   forget the saved testbox: it ends at its idle timeout (TESTBOX_IDLE
#                                             minutes after the last command), and that end requests a commit of the
#                                             sticky disks. Use it after a cold build or a seed. Commits of
#                                             testboxes that lived 2 to 13 minutes landed (up to 2.1 GiB); those of two
#                                             that lived 25 and 27 minutes did not. For a commit, warm up with
#                                             TESTBOX_IDLE=1 and release after the last command. `status` shows the end
#        testbox.sh pin [KEY...]              check out each pin's Go repo at its zbook path, with npm ci node_modules
#                                             (default: the batch pin, which warmup checks out). KEY comes from this
#                                             worktree's UPSTREAM.json
#        testbox.sh tests [--pin KEY] OUT BASE
#                                             the protected test suite at HEAD: build-goport-tests.sh and
#                                             goport-tests.sh on the testbox (pushes the pin oracle first when the
#                                             testbox lacks it), fetch results.json and the logs to OUT (must not
#                                             exist), print compare-tests.py BASE OUT. After a failed build, print its
#                                             compiler errors (OUT/testbin.new/logs).
#                                             HEAD must be pushed; crates/, Cargo.toml and Cargo.lock must be clean
#        testbox.sh np-suite [--pin KEY] LABEL [BASE]
#                                             a stable release tsgo and np-suite.sh run LABEL on the testbox, fetched to
#                                             the main checkout's np-suite dir (LABEL must not exist), then
#                                             np-suite.sh diff BASE LABEL
# The gate and the oracles run as on zbook: the testbox env sets HOME=/home/theo and the workflow binds the
# workspace on /home/theo/Code/sandbox/ts-rust (testbox-data.sh). Fetch a commit that the bins name before a
# gate: run git fetch --depth=1 origin <sha>.
# KEY defaults to the batch pin (docs/typechecker-state/current.json batch.upstreamPin.to).
# TESTBOX_ID overrides the saved ID. TESTBOX_IDLE: idle minutes before the testbox stops (default 15).
# TESTBOX_REF: the ref the workflow runs from (default main: the workflow must be on the default branch).
# Auth: `blacksmith auth login` once per host (`blacksmith auth status` shows it).
# scripts/goport/testbox-remote.sh holds the steps that run on the testbox.
set -euo pipefail
case "${1:-help}" in help | -h | --help) sed -n '2,/^set -euo/p' "$0" | sed '$d'; exit 0 ;; esac

repo_root="$(git -C "$(dirname -- "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
id_file="$repo_root/target/testbox-id"
# The synced repo root on the testbox, relative to the SSH login dir (/home/runner).
remote_root=_work/ts-rust/ts-rust
cd "$repo_root"

saved_id() {
  local id="${TESTBOX_ID:-$(cat "$id_file" 2>/dev/null || true)}"
  [[ -n "$id" ]] || { echo "no testbox: run 'testbox.sh warmup' or set TESTBOX_ID" >&2; exit 2; }
  echo "$id"
}
batch_pin() { jq -r '.batch.upstreamPin.to // empty' docs/typechecker-state/current.json; }

# remote <command...>: sync this worktree, run the command in the testbox's repo root with the testbox env.
remote() {
  local remote_cmd
  printf -v remote_cmd '%q ' "$@"
  blacksmith testbox run --id "$(saved_id)" ". ~/testbox.env && $remote_cmd"
}

# ssh_route: sets host and ssh for rsync over the CLI's own SSH route (port 64000 and the key that warmup
# saves in ~/.blacksmith/testboxes/<id>; CLI 0.4.70, see `run --debug`). The login dir is /home/runner.
# Commands over this route do not source the testbox env, and they read stdin: give them < /dev/null.
ssh_route() {
  local id key
  id="$(saved_id)"
  # --wait: a testbox that is not ready yet has no IP, and its row has the workflow path in that column.
  host="$(blacksmith testbox status --id "$id" --wait --wait-timeout 15m | awk -v id="$id" '$1 == id && $2 == "ready" {print $3}')"
  key="$HOME/.blacksmith/testboxes/$id/id_ed25519"
  # A host with a / would make rsync copy to a local path.
  [[ -n "$host" && $host != */* && -f "$key" ]] || { echo "no SSH route to $id (host '$host', key $key)" >&2; exit 1; }
  ssh="ssh -p 64000 -i $key -o IdentitiesOnly=yes -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR -o Compression=no -o ConnectTimeout=20"
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
  # A caller can run on for minutes (tests): stop the keepalive now.
  kill "$keep" 2>/dev/null || true
  trap - EXIT
}

# push_oracle KEY: push zbook's recorded oracle of pin KEY when the testbox's copy differs. The batch pin's
# oracle path is a bind of the pin disk (testbox-data.txt), so the push lands there; another pin's stays on
# this testbox only. A build on the runner has another sha256 (Go puts absolute paths in the binary).
push_oracle() {
  local path sha host ssh
  path=$(python3 scripts/upstream/pin.py path oracle "$1") || exit 2
  sha=$(python3 scripts/upstream/pin.py show "$1" | jq -r .oracle.sha256)
  [[ $(sha256sum < "$path" | cut -d' ' -f1) == "$sha" ]] ||
    { echo "$path does not match the sha256 in UPSTREAM.json" >&2; exit 1; }
  ssh_route
  if [[ $($ssh "runner@$host" sha256sum "$path" < /dev/null 2> /dev/null | cut -d' ' -f1) == "$sha" ]]; then
    echo "oracle $1 on the testbox"
  else
    push_paths "$path"
  fi
}

# job RUN STEP ARGS...: start testbox-remote.sh STEP ARGS... detached on the testbox, print its log as it grows
# and return its exit code. It polls over the SSH route, which does not sync this worktree.
job() {
  local run=$1 host ssh t size=0 fails=0 rc
  # exit, not return: callers run job in a || list (no set -e there), and then fetch RUN, which must not
  # take another job's run.
  remote scripts/goport/testbox-remote.sh start "$@" || exit
  ssh_route
  t=$(mktemp -d)
  while :; do
    # RUN.rc first: once it is there, the log is complete.
    rc=$($ssh "runner@$host" cat "$remote_root/$run.rc" < /dev/null 2> /dev/null) || rc=
    if $ssh "runner@$host" tail -c "+$((size + 1))" "$remote_root/$run.log" < /dev/null > "$t/new" 2> /dev/null; then
      fails=0
      cat "$t/new"
      size=$((size + $(stat -c %s "$t/new")))
    elif ((++fails >= 10)); then
      echo "testbox $(saved_id): no $run.log after 10 tries" >&2
      rm -rf "$t"
      return 1
    fi
    [[ -z $rc ]] || break
    sleep 15
  done
  rm -rf "$t"
  return "$rc"
}

# fetch RUN DEST: copy RUN/out.tar.gz and RUN.log back, unpack them in DEST, then remove them on the testbox
# (the test binaries would fill the sticky target/). Without RUN/out.tar.gz (the job ended before it packed),
# it keeps RUN.log on the testbox and returns 1.
fetch() {
  local host ssh t
  ssh_route
  t=$(mktemp -d)
  rsync -a -e "$ssh" "runner@$host:$remote_root/$1/out.tar.gz" "$t/" || {
    rm -rf "$t"
    echo "no $1/out.tar.gz on the testbox (the job log above has its error; $1.log stays there)" >&2
    return 1
  }
  rsync -a -e "$ssh" "runner@$host:$remote_root/$1.log" "$t/testbox.log"
  mkdir -p "$2"
  tar -xzf "$t/out.tar.gz" -C "$2"
  mv "$t/testbox.log" "$2/"
  rm -rf "$t"
  $ssh "runner@$host" rm -rf "$remote_root/$1" "$remote_root/$1.log" "$remote_root/$1.rc" < /dev/null
}

cmd="$1"
shift
pin_key=
if [[ $cmd == tests || $cmd == np-suite ]] && [[ ${1:-} == --pin ]]; then
  (($# >= 2)) || { echo "usage: testbox.sh $cmd --pin KEY ..." >&2; exit 2; }
  pin_key=$2
  shift 2
fi
pin_key=${pin_key:-$(batch_pin)}
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
    remote "$@"
    ;;
  pin) remote scripts/goport/testbox-remote.sh pin "$@" ;;
  tests)
    (($# == 2)) || { echo "usage: testbox.sh tests [--pin KEY] OUT BASE" >&2; exit 2; }
    out=$(realpath -m -- "$1") base=$(realpath -- "$2")
    [[ ! -e $out ]] || { echo "$out exists (results are never replaced)" >&2; exit 2; }
    [[ -z $(git status --porcelain --untracked-files=all -- crates Cargo.toml Cargo.lock) ]] ||
      { echo "crates/, Cargo.toml or Cargo.lock has changes: commit them (build-goport-tests.sh builds HEAD)" >&2; exit 2; }
    head=$(git rev-parse HEAD)
    git branch -r --contains "$head" | grep -q . ||
      echo "warning: no remote branch here has HEAD ${head:0:12}; the testbox fetches it from origin" >&2
    push_oracle "$pin_key"
    run=target/testbox-runs/tests-$(date -u +%Y%m%dT%H%M%S)-${head:0:9}
    rc=0
    job "$run" tests "$pin_key" "$head" "$run" || rc=$?
    fetch "$run" "$out"
    if [[ ! -f $out/tests-run/results.json ]]; then
      # A failed build: its compiler errors, from the cargo logs (without the colors).
      sed 's/\x1b\[[0-9;]*m//g' "$out"/testbin.new/logs/build-*.log 2> /dev/null | grep -A 12 -m 10 '^error' | head -80 || true
      echo "no results.json (rc $rc): see $out/build.log, $out/testbin.new/logs and $out/tests.log" >&2
      exit 1
    fi
    python3 scripts/goport/compare-tests.py "$base" "$out/tests-run/results.json" --out "$out/compare.json" || rc=$?
    echo "results $out/tests-run/results.json, compare $out/compare.json"
    exit "$rc"
    ;;
  np-suite)
    (($# == 1 || $# == 2)) || { echo "usage: testbox.sh np-suite [--pin KEY] LABEL [BASE]" >&2; exit 2; }
    np=/home/theo/Code/sandbox/ts-rust/target/continuation-r97-goport/compat-backlog/np-suite
    [[ ! -e $np/$1 ]] || { echo "$np/$1 exists (results are never replaced)" >&2; exit 2; }
    run=target/testbox-runs/np-$(date -u +%Y%m%dT%H%M%S)-$1
    rc=0
    job "$run" np-suite "$pin_key" "$1" "$run" || rc=$?
    mkdir -p "$np" target
    tmp=$(mktemp -d "$repo_root/target/testbox-np.XXXXXX")
    fetch "$run" "$tmp"
    [[ -d $tmp/$1 ]] || { echo "no np-suite result (rc $rc): the tsgo build log is $tmp/build.log" >&2; exit 1; }
    mv "$tmp/$1" "$np/$1"
    mv "$tmp/build.log" "$np/$1/testbox-build.log"
    mv "$tmp/testbox.log" "$np/$1/testbox.log"
    rmdir "$tmp"
    cat "$np/$1/summary.txt"
    [[ -z ${2:-} ]] || scripts/goport/np-suite.sh diff "$2" "$1" | tail -20
    exit "$rc"
    ;;
  get)
    # rsync, not `blacksmith testbox download`: that timed out after 5 minutes on a 124 MB results dir.
    (($# == 1 || $# == 2)) || { echo "usage: testbox.sh get <remote> [local]" >&2; exit 2; }
    ssh_route
    src="$1"
    [[ "$src" == /* ]] || src="$remote_root/$src"
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
  stop | release)
    id="$(saved_id)"
    if [[ $cmd == stop ]]; then
      blacksmith testbox stop --id "$id"
    else
      echo "testbox $id: released; it ends at its idle timeout and requests a commit of its sticky disks"
      echo "(TESTBOX_ID=$id scripts/goport/testbox.sh status shows when it completed)"
    fi
    # Keep the saved ID when TESTBOX_ID named another testbox.
    [[ "$(cat "$id_file" 2>/dev/null || true)" != "$id" ]] || rm -f "$id_file"
    ;;
  list) blacksmith testbox list "$@" ;;
  *) echo "unknown command: $cmd (testbox.sh help)" >&2; exit 2 ;;
esac
