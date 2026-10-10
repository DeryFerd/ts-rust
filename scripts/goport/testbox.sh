#!/usr/bin/env bash
# Blacksmith testboxes: a warm 32 vCPU Linux x64 runner (.github/workflows/testbox.yml) that runs a command
# against this worktree's files. `run` syncs this worktree to the testbox (the CLI's rsync) and runs the
# command in the synced repo root. target/ and the cargo registry sit on sticky disks.
# usage: testbox.sh help                      this text
#        testbox.sh warmup                    start a testbox; saves its ID to target/testbox-id
#        testbox.sh run <command...>          sync this worktree, then run the command with the testbox env
#                                             (e.g. run scripts/run-cargo-capped.sh build --release -p ts_goport --bins).
#                                             Arguments keep their boundaries; use run bash -c '...' for pipes and &&
#        testbox.sh get <remote> [local]      copy a file or dir back (remote path relative to the repo root)
#        testbox.sh status | list             the saved testbox's status, list active testboxes
#        testbox.sh stop                      end the saved testbox now. stop cancels the job, and the sticky disks
#                                             do not commit after a cancelled step: the writes to target/ are lost
#        testbox.sh release                   forget the saved testbox: it ends at its idle timeout (TESTBOX_IDLE
#                                             minutes after the last command), and that end commits the sticky disks.
#                                             Use it after a cold build or new oracles; the idle minutes cost the same
#        testbox.sh pin [KEY...]              set up the zbook path mirror and each pin's Go checkout (default: the batch
#                                             pin, which warmup sets up). KEY comes from this worktree's UPSTREAM.json
#        testbox.sh oracles [KEY...]          seed the recorded oracle of each pin (default: the batch pin): upload the
#                                             ones the testbox's sticky target/testbox-oracles lacks (sha256 checked
#                                             against UPSTREAM.json on both sides), install them at their paths
#        testbox.sh tests [--pin KEY] OUT BASE
#                                             the protected test suite at HEAD: build-goport-tests.sh and
#                                             goport-tests.sh on the testbox (seeds the oracle first), fetch results.json
#                                             and the logs to OUT (must not exist), print compare-tests.py BASE OUT.
#                                             HEAD must be pushed; crates/, Cargo.toml and Cargo.lock must be clean
#        testbox.sh np-suite [--pin KEY] LABEL [BASE]
#                                             a stable release tsgo and np-suite.sh run LABEL on the testbox, fetched to
#                                             the main checkout's np-suite dir (LABEL must not exist), then
#                                             np-suite.sh diff BASE LABEL
# KEY defaults to the batch pin (docs/typechecker-state/current.json batch.upstreamPin.to).
# TESTBOX_ID overrides the saved ID. TESTBOX_IDLE: idle minutes before the testbox stops (default 15).
# TESTBOX_REF: the ref the workflow runs from (default main: the workflow must be on the default branch).
# Auth: `blacksmith auth login` once per host (`blacksmith auth status` shows it).
# scripts/goport/testbox-remote.sh holds the steps that run on the testbox.
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

# remote <command...>: sync this worktree, run the command in the testbox's repo root with the testbox env.
remote() {
  local remote_cmd
  printf -v remote_cmd '%q ' "$@"
  blacksmith testbox run --id "$(saved_id)" ". ~/testbox.env && $remote_cmd"
}
batch_pin() { jq -r '.batch.upstreamPin.to // empty' docs/typechecker-state/current.json; }

# oracles KEY...: upload the oracles the testbox lacks through the sync (an untracked dir that is not
# ignored, removed after), then install them.
oracles() {
  local k path out missing
  for k in "$@"; do
    path=$(python3 scripts/upstream/pin.py path oracle "$k") || exit 2
    [[ $(sha256sum < "$path" | cut -d' ' -f1) == "$(python3 scripts/upstream/pin.py show "$k" | jq -r .oracle.sha256)" ]] ||
      { echo "$path does not match the sha256 in UPSTREAM.json" >&2; exit 1; }
  done
  out=$(remote scripts/goport/testbox-remote.sh oracles-missing "$@") || { echo "$out"; exit 1; }
  read -ra missing <<< "$(sed -n 's/^missing: *//p' <<< "$out" | tail -1)"
  if ((${#missing[@]} == 0)); then
    echo "oracles on the testbox: $*"
    return
  fi
  echo "uploading oracles: ${missing[*]}"
  trap 'rm -rf "$repo_root/testbox-upload"' EXIT
  mkdir -p testbox-upload
  for k in "${missing[@]}"; do cp --reflink=auto "$(python3 scripts/upstream/pin.py path oracle "$k")" "testbox-upload/$k"; done
  remote scripts/goport/testbox-remote.sh oracles-install testbox-upload
  rm -rf "$repo_root/testbox-upload"
  trap - EXIT
}

# job RUN STEP ARGS...: start testbox-remote.sh STEP ARGS... detached on the testbox, print its log as it grows
# and return its exit code. It polls with downloads, which do not sync this worktree.
job() {
  local run=$1 id t n=0 fails=0 rc
  id=$(saved_id)
  remote scripts/goport/testbox-remote.sh start "$@"
  t=$(mktemp -d)
  while :; do
    rc=
    blacksmith testbox download --id "$id" "$run.rc" "$t/rc" > /dev/null 2>&1 && rc=$(cat "$t/rc")
    if blacksmith testbox download --id "$id" "$run.log" "$t/log" > /dev/null 2>&1; then
      fails=0
      tail -n "+$((n + 1))" "$t/log"
      n=$(wc -l < "$t/log")
    elif ((++fails >= 10)); then
      echo "testbox $id: no $run.log after 10 tries" >&2
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
# (the test binaries would fill the sticky target/).
fetch() {
  local id
  id=$(saved_id)
  mkdir -p "$2"
  blacksmith testbox download --id "$id" "$1/out.tar.gz" "$2/out.tar.gz" > /dev/null
  blacksmith testbox download --id "$id" "$1.log" "$2/testbox.log" > /dev/null
  tar -xzf "$2/out.tar.gz" -C "$2"
  rm "$2/out.tar.gz"
  remote rm -rf "$1" "$1.log" "$1.rc" > /dev/null
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
  pin) remote scripts/goport/testbox-remote.sh setup "$@" ;;
  oracles)
    (($#)) || set -- "$(batch_pin)"
    oracles "$@"
    ;;
  tests)
    (($# == 2)) || { echo "usage: testbox.sh tests [--pin KEY] OUT BASE" >&2; exit 2; }
    out=$(realpath -m -- "$1") base=$(realpath -- "$2")
    [[ ! -e $out ]] || { echo "$out exists (results are never replaced)" >&2; exit 2; }
    [[ -z $(git status --porcelain --untracked-files=all -- crates Cargo.toml Cargo.lock) ]] ||
      { echo "crates/, Cargo.toml or Cargo.lock has changes: commit them (build-goport-tests.sh builds HEAD)" >&2; exit 2; }
    head=$(git rev-parse HEAD)
    git branch -r --contains "$head" | grep -q . ||
      echo "warning: no remote branch here has HEAD ${head:0:12}; the testbox fetches it from origin" >&2
    oracles "$pin_key"
    run=target/testbox-runs/tests-$(date -u +%Y%m%dT%H%M%S)-${head:0:9}
    rc=0
    job "$run" tests "$pin_key" "$head" "$run" || rc=$?
    fetch "$run" "$out"
    [[ -f $out/tests-run/results.json ]] || { echo "no results.json (rc $rc): see $out/build.log and $out/tests.log" >&2; exit 1; }
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
    mv "$tmp/$1" "$np/$1"
    mv "$tmp/build.log" "$np/$1/testbox-build.log"
    mv "$tmp/testbox.log" "$np/$1/testbox.log"
    rmdir "$tmp"
    cat "$np/$1/summary.txt"
    [[ -z ${2:-} ]] || scripts/goport/np-suite.sh diff "$2" "$1" | tail -20
    exit "$rc"
    ;;
  get) blacksmith testbox download --id "$(saved_id)" "$@" ;;
  status) blacksmith testbox status --id "$(saved_id)" "$@" ;;
  stop | release)
    id="$(saved_id)"
    if [[ $cmd == stop ]]; then
      blacksmith testbox stop --id "$id"
    else
      echo "testbox $id: released; it ends and commits its sticky disks after its idle timeout"
    fi
    # Keep the saved ID when TESTBOX_ID named another testbox.
    [[ "$(cat "$id_file" 2>/dev/null || true)" != "$id" ]] || rm -f "$id_file"
    ;;
  list) blacksmith testbox list "$@" ;;
  *) echo "unknown command: $cmd (testbox.sh help)" >&2; exit 2 ;;
esac
