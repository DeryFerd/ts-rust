#!/usr/bin/env bash
# The testbox side of testbox.sh. Each command runs on a Blacksmith testbox in the synced repo root, through
# `blacksmith testbox run`. The workflow has set up zbook's paths (testbox-data.sh mount): the workspace is
# bound on /home/theo/Code/sandbox/ts-rust, the batch pin's Go checkout (with node_modules) on its zbook path,
# the pin oracle and the other files of testbox-data.txt on theirs, and the testbox env sets HOME=/home/theo.
# usage: testbox-remote.sh pin [KEY...]            the Go checkout of each pin at its zbook path, at the pin commit,
#                                                  with npm ci node_modules (default: the batch pin, which the
#                                                  workflow checks out)
#        testbox-remote.sh start RUN STEP ARGS...  run `testbox-remote.sh STEP ARGS...` detached from the SSH session:
#                                                  output in RUN.log, then its exit code in RUN.rc. The job counts as
#                                                  testbox activity (the idle timer does not end the testbox under it)
#        testbox-remote.sh tests KEY COMMIT RUN    build-goport-tests.sh at COMMIT, goport-tests.sh at pin KEY,
#                                                  pack the results and logs in RUN/out.tar.gz (after a failed build,
#                                                  its cargo logs in testbin.new/logs)
#        testbox-remote.sh np-suite KEY LABEL RUN  a stable release tsgo, np-suite.sh run LABEL at pin KEY, pack
#                                                  the label dir in RUN/out.tar.gz, then remove the label dir
#                                                  (after a failed build, only its build.log)
#        testbox-remote.sh exec CMD...             run CMD (the step of testbox.sh job)
#        testbox-remote.sh source DIR COMMIT [BUNDLE]
#                                                  DIR (a zbook path under target/) as a git worktree of this repo
#                                                  at COMMIT, fetched from BUNDLE (its prerequisites from origin)
#                                                  or from origin. A DIR that is not that worktree is replaced
# pin.py exec binds a pin's oracle and Go checkout over the default ones; bwrap makes those bind targets.
# Only microsoft/TypeScript pins (layout typescript) are set up: the older layout needs the TypeScript submodule.
set -euo pipefail
case "${1:-help}" in help | -h | --help) sed -n '2,/^set -euo/p' "$0" | sed '$d'; exit 0 ;; esac

# zbook's main checkout: the root of the absolute paths in UPSTREAM.json (pinRoot) and np-suite.sh.
ZBOOK_REPO=/home/theo/Code/sandbox/ts-rust
die() { echo "testbox-remote.sh: $*" >&2; exit 1; }
cd "$(git -C "$(dirname -- "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
pin() { python3 scripts/upstream/pin.py "$@"; }
batch_pin() { jq -r '.batch.upstreamPin.to // empty' docs/typechecker-state/current.json; }

# on_testbox: the workspace must be bound on $ZBOOK_REPO (testbox-data.sh mount). On zbook $ZBOOK_REPO is the
# main checkout itself, and `tests` must not move its HEAD (at_commit).
on_testbox() {
  [[ $PWD != "$ZBOOK_REPO" && $ZBOOK_REPO -ef $PWD ]] ||
    die "not on a testbox: $ZBOOK_REPO is not a bind of $PWD (testbox-data.sh mount)"
}

# checkout KEY: the whole pin checkout at its zbook path, at the pin commit, with the root node_modules
# (astnav tests and np-suite run node on them).
checkout() {
  local rec repo commit go dir
  rec=$(pin show "$1") || die "unknown pin $1"
  [[ $(jq -r .layout <<< "$rec") == typescript ]] || die "pin $1: layout $(jq -r .layout <<< "$rec"), not typescript"
  repo=$(jq -r .repo <<< "$rec") commit=$(jq -r .commit <<< "$rec") go=$(jq -r .goCheckout <<< "$rec")
  dir=${go%/"$(jq -r .subdir <<< "$rec")"}
  [[ $dir == /home/theo/.explore/repos/?* ]] || die "pin $1: checkout $dir is not under /home/theo/.explore/repos"
  if [[ $(git -C "$dir" rev-parse HEAD 2> /dev/null) == "$commit" && -f $dir/node_modules/typescript/package.json ]]; then
    echo "pin $1: $dir ready"
    return
  fi
  # The workflow binds its checkout of the batch pin here: never empty it.
  ! mountpoint -q "$dir" || die "pin $1: the workflow's checkout at $dir is not at ${commit:0:12} with node_modules"
  rm -rf "$dir"
  git init -q "$dir"
  git -C "$dir" fetch -q --depth=1 "https://github.com/$repo" "$commit"
  git -C "$dir" -c advice.detachedHead=false checkout -q FETCH_HEAD
  (cd "$dir" && npm ci --ignore-scripts --no-audit --no-fund --loglevel=error)
  [[ -d $go/testdata/baselines/reference ]] || die "pin $1: no $go/testdata/baselines/reference"
  echo "pin $1: $dir at ${commit:0:12}, $(ls "$dir/node_modules" | wc -l) node_modules"
}

# at_commit COMMIT: HEAD and the index at COMMIT, the synced files kept (the sync sends files, not git state).
at_commit() {
  [[ $(git rev-parse HEAD) != "$1" ]] || return 0
  git cat-file -e "$1^{commit}" 2> /dev/null || git fetch -q --depth=1 origin "$1" ||
    die "commit $1 is not on origin: push it first"
  git reset -q "$1"
}

cmd=$1
shift
case $cmd in
  start)
    (($# >= 2)) || die "usage: start RUN STEP ARGS..."
    [[ ! -e $1.log ]] || die "$1.log exists"
    mkdir -p "$(dirname "$1")"
    # A dropped SSH session must not stop a long job (one dropped after 170 s on 2026-10-10).
    setsid nohup "$0" job "$@" > /dev/null 2>&1 < /dev/null &
    echo "started $1"
    ;;
  job)
    run=$1
    shift
    # run-testbox resets its idle timer when this file is newer than the last activity. It is in the login
    # home (/home/runner), not in ~: the testbox env sets HOME=/home/theo. The keepalive ends with this
    # shell, so a killed job lets the testbox end at its idle timeout and the local poll stop.
    marker=$(getent passwd "$(id -u)" | cut -d: -f6)/.testbox-last-activity
    (while sleep 30 && kill -0 "$$" 2> /dev/null; do touch "$marker"; done) &
    keep=$!
    # RUN.rc is written on every exit. It stays 1 when the job shell itself is killed.
    rc=1
    trap 'kill "$keep" 2> /dev/null || true; echo "$rc" > "$run.rc"' EXIT
    if "$0" "$@" > "$run.log" 2>&1 < /dev/null; then rc=0; else rc=$?; fi
    ;;
  pin)
    on_testbox
    (($#)) || { k=$(batch_pin); [[ -z $k ]] || set -- "$k"; }
    (($#)) || echo "no batch pin in docs/typechecker-state/current.json: no pin checkout (testbox.sh pin KEY sets one up)"
    for k in "$@"; do checkout "$k"; done
    ;;
  tests)
    (($# == 3)) || die "usage: tests KEY COMMIT RUN"
    key=$1 commit=$2 run=$3
    [[ ! -e $run ]] || die "$run exists"
    # First: it refuses to run on zbook before at_commit moves HEAD.
    on_testbox
    at_commit "$commit"
    checkout "$key"
    mkdir -p "$run"
    rc=0
    echo "build-goport-tests.sh at ${commit:0:12} ($(date -u +%T))"
    scripts/goport/build-goport-tests.sh "$PWD" "$run/testbin" > "$run/build.log" 2>&1 || rc=$?
    # Not the bare DONE line: a driver log that ends in DONE or FAIL must not match it early.
    tail -2 "$run/build.log" | grep -vx DONE || true
    if ((rc == 0)); then
      echo "goport-tests.sh at pin $key ($(date -u +%T))"
      GOPORT_PIN=$key scripts/goport/goport-tests.sh "$run/testbin" "$run/tests-run" > "$run/tests.log" 2>&1 || rc=$?
      grep -E '^[a-z_0-9-]+: [0-9]+ names|^incomplete:' "$run/tests.log" || true
      tail -1 "$run/tests.log"
    fi
    # Not the test binaries, the release bins, the crates archive (tests-run/src) or the runner temp. A failed
    # build leaves its cargo logs (the compiler errors) in testbin.new/logs.
    (cd "$run" && for f in build.log tests.log testbin/* testbin.new/logs tests-run/*; do
      case $f in testbin/relbin | tests-run/src | tests-run/tmp) continue ;; esac
      if [[ -d $f || (-f $f && ! -x $f) ]]; then echo "$f"; fi
    done) > "$run/pack.list"
    tar -C "$run" -czf "$run/out.tar.gz" -T "$run/pack.list"
    echo "packed $run/out.tar.gz ($(du -h "$run/out.tar.gz" | cut -f1)); rc $rc ($(date -u +%T))"
    exit "$rc"
    ;;
  np-suite)
    (($# == 3)) || die "usage: np-suite KEY LABEL RUN"
    key=$1 label=$2 run=$3
    [[ ! -e $run ]] || die "$run exists"
    on_testbox
    checkout "$key"
    mkdir -p "$run"
    # Stable and not incremental, as candidate.sh builds release bins.
    TS_CARGO_NIGHTLY=0 TS_CARGO_INCREMENTAL=0 scripts/run-cargo-capped.sh build --release --locked -p ts_goport --bin tsgo \
      > "$run/build.log" 2>&1 || {
      tail -20 "$run/build.log"
      tar -czf "$run/out.tar.gz" -C "$run" build.log
      die "tsgo build failed"
    }
    np=target/continuation-r97-goport/compat-backlog/np-suite
    rc=0
    NP_GO_DIR=$(pin path goCheckout "$key") scripts/goport/np-suite.sh run "$label" "$PWD/target/release/tsgo" || rc=$?
    tar -czf "$run/out.tar.gz" -C "$run" build.log -C "$PWD/$np" "$label"
    # The local copy is the record: the sticky target/ keeps no label dirs.
    rm -rf "${np:?}/${label:?}"
    exit "$rc"
    ;;
  exec)
    on_testbox
    (($#)) || die "usage: exec CMD..."
    exec "$@"
    ;;
  source)
    (($# == 2 || $# == 3)) || die "usage: source DIR COMMIT [BUNDLE]"
    dir=$1 commit=$2 bundle=${3:-}
    # First: DIR is a zbook path, and this step replaces it.
    on_testbox
    [[ $dir == "$ZBOOK_REPO"/target/?* && $dir != *..* ]] || die "source: $dir is not under $ZBOOK_REPO/target"
    if [[ -n $bundle ]]; then
      # The prerequisites: the "-<sha>" lines of the bundle header, which ends at the first empty line.
      for p in $(awk '/^$/ {exit} /^-/ {print substr($1, 2)}' "$bundle"); do
        git cat-file -e "$p^{commit}" 2> /dev/null || git fetch -q --depth=1 origin "$p" || die "prerequisite $p is not on origin"
      done
      git fetch -q "$bundle" HEAD || die "cannot fetch $bundle"
    fi
    git cat-file -e "$commit^{commit}" 2> /dev/null || git fetch -q --depth=1 origin "$commit" ||
      die "commit $commit is not on origin and not in a bundle"
    if [[ $(git -C "$dir" rev-parse HEAD 2> /dev/null) == "$commit" && $(git -C "$dir" rev-parse --git-common-dir 2> /dev/null) -ef .git ]]; then
      git -C "$dir" reset -q --hard
      git -C "$dir" clean -q -fdx -e target/
    else
      # A dir from an older testbox (target/ is a sticky disk), or another commit: a new worktree.
      rm -rf "$dir"
      git worktree prune
      git worktree add -q --detach "$dir" "$commit"
    fi
    echo "$dir at ${commit:0:12}"
    ;;
  *) die "unknown command $cmd (testbox-remote.sh help)" ;;
esac
