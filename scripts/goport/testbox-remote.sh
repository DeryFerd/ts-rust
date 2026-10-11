#!/usr/bin/env bash
# The testbox side of testbox.sh. Each command runs on a Blacksmith testbox in the synced repo root:
# testbox.yml runs `setup` at warmup, testbox.sh runs the others through `blacksmith testbox run`.
# usage: testbox-remote.sh setup [KEY...]          the zbook path mirror and the Go checkout of each pin
#                                                  (default: the batch pin), then install the seeded oracles
#        testbox-remote.sh oracles-missing KEY...  print "missing: <keys>" (the seeded oracles that are absent or
#                                                  have another sha256 than UPSTREAM.json records)
#        testbox-remote.sh oracles-install DIR     move each uploaded DIR/<key> (sha256 checked) to the sticky
#                                                  target/testbox-oracles/<key>, then install the seeded oracles
#        testbox-remote.sh start RUN STEP ARGS...  run `testbox-remote.sh STEP ARGS...` detached from the SSH session:
#                                                  output in RUN.log, then its exit code in RUN.rc. The job counts as
#                                                  testbox activity (the idle timer does not end the testbox under it)
#        testbox-remote.sh tests KEY COMMIT RUN    build-goport-tests.sh at COMMIT, goport-tests.sh at pin KEY,
#                                                  pack the results and logs in RUN/out.tar.gz (after a failed build,
#                                                  its cargo logs in testbin.new/logs)
#        testbox-remote.sh np-suite KEY LABEL RUN  a stable release tsgo, np-suite.sh run LABEL at pin KEY, pack
#                                                  the label dir in RUN/out.tar.gz, then remove the label dir
#                                                  (after a failed build, only its build.log)
# The zbook path mirror (UPSTREAM.json, pin.py and the protected scripts use zbook's absolute paths):
#   /home/theo/Code/sandbox/ts-rust                the workspace (a symlink)
#   <pin goCheckout>/..                            the whole pin checkout (depth 1) with npm ci node_modules
#   the default goCheckout                         an empty real dir (pin.py exec binds the pin checkout over it)
#   each pin oracle path                           a real copy of target/testbox-oracles/<key> (sha256 checked)
#   the default oracle                             the current pin's seeded oracle, else a stub that exits 2
#   ~/.explore                                     /home/theo/.explore (a symlink), for ~/.explore paths
# Only microsoft/TypeScript pins (layout typescript) are set up: the older layout needs the TypeScript submodule.
set -euo pipefail
case "${1:-help}" in help | -h | --help) sed -n '2,/^set -euo/p' "$0" | sed '$d'; exit 0 ;; esac

# zbook's main checkout: the root of the absolute paths in UPSTREAM.json (pinRoot) and np-suite.sh.
ZBOOK_REPO=/home/theo/Code/sandbox/ts-rust
die() { echo "testbox-remote.sh: $*" >&2; exit 1; }
cd "$(git -C "$(dirname -- "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
pin() { python3 scripts/upstream/pin.py "$@"; }
batch_pin() { jq -r '.batch.upstreamPin.to // empty' docs/typechecker-state/current.json; }

mirror() {
  local d
  [[ -d /home/theo ]] || sudo install -d -o "$(id -u)" -g "$(id -g)" /home/theo
  mkdir -p "$(dirname "$ZBOOK_REPO")"
  [[ -L $ZBOOK_REPO || ! -e $ZBOOK_REPO ]] || die "$ZBOOK_REPO exists and is not a symlink"
  ln -sfn "$PWD" "$ZBOOK_REPO"
  mkdir -p "$(jq -r .defaults.goCheckout UPSTREAM.json)" "$(dirname "$(jq -r .defaults.oracle UPSTREAM.json)")"
  [[ -e $HOME/.explore ]] || ln -s /home/theo/.explore "$HOME/.explore"
  for d in "$ZBOOK_REPO/target" /home/theo/.explore/repos "$(dirname "$(jq -r .defaults.oracle UPSTREAM.json)")"; do
    touch "$d/.testbox-write-check" && rm "$d/.testbox-write-check" || die "$(id -un) cannot write to $d"
  done
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
  rm -rf "$dir"
  git init -q "$dir"
  git -C "$dir" fetch -q --depth=1 "https://github.com/$repo" "$commit"
  git -C "$dir" -c advice.detachedHead=false checkout -q FETCH_HEAD
  (cd "$dir" && npm ci --ignore-scripts --no-audit --no-fund --loglevel=error)
  [[ -d $go/testdata/baselines/reference ]] || die "pin $1: no $go/testdata/baselines/reference"
  echo "pin $1: $dir at ${commit:0:12}, $(ls "$dir/node_modules" | wc -l) node_modules"
}

# The recorded sha256 of a pin's oracle; empty when the synced UPSTREAM.json lacks the pin.
want_sha() { pin show "$1" 2> /dev/null | jq -r .oracle.sha256 || true; }

# install_oracles: a real copy of each seeded oracle at its path; the default oracle path gets the current
# pin's oracle, else a stub (pin.py exec binds over a real file; a run without GOPORT_PIN fails loudly).
install_oracles() {
  local f key path default
  default=$(jq -r .defaults.oracle UPSTREAM.json)
  for f in target/testbox-oracles/*; do
    [[ -f $f ]] || continue
    key=${f##*/}
    [[ -n $(want_sha "$key") ]] || continue
    [[ $(sha256sum < "$f" | cut -d' ' -f1) == "$(want_sha "$key")" ]] || { echo "oracle $key: sha256 differs, skipped" >&2; continue; }
    path=$(pin path oracle "$key")
    cmp -s "$f" "$path" 2> /dev/null || install -D -m 755 "$f" "$path"
    echo "oracle $key: $path"
  done
  [[ -f $default ]] || printf '%s\n' '#!/bin/sh' \
    "echo \"tsgo-oracle: no oracle of the current pin on this testbox (set GOPORT_PIN, or testbox.sh oracles $(jq -r .current UPSTREAM.json))\" >&2" \
    'exit 2' > "$default"
  chmod 755 "$default"
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
    # run-testbox resets its idle timer when this file is newer than the last activity. The keepalive ends
    # with this shell, so a killed job lets the testbox end at its idle timeout and the local poll stop.
    (while sleep 30 && kill -0 "$$" 2> /dev/null; do touch ~/.testbox-last-activity; done) &
    keep=$!
    # RUN.rc is written on every exit. It stays 1 when the job shell itself is killed.
    rc=1
    trap 'kill "$keep" 2> /dev/null || true; echo "$rc" > "$run.rc"' EXIT
    if "$0" "$@" > "$run.log" 2>&1 < /dev/null; then rc=0; else rc=$?; fi
    ;;
  setup)
    mirror
    (($#)) || { k=$(batch_pin); [[ -z $k ]] || set -- "$k"; }
    (($#)) || echo "no batch pin in docs/typechecker-state/current.json: no pin checkout (testbox.sh pin KEY sets one up)"
    for k in "$@"; do checkout "$k"; done
    install_oracles
    ;;
  oracles-missing)
    missing=()
    for k in "$@"; do
      [[ -f target/testbox-oracles/$k && $(sha256sum < "target/testbox-oracles/$k" | cut -d' ' -f1) == "$(want_sha "$k")" ]] ||
        missing+=("$k")
    done
    echo "missing: ${missing[*]}"
    ;;
  oracles-install)
    (($# == 1)) && [[ -d $1 ]] || die "usage: oracles-install DIR"
    mkdir -p target/testbox-oracles
    for f in "$1"/*; do
      k=${f##*/}
      [[ $(sha256sum < "$f" | cut -d' ' -f1) == "$(want_sha "$k")" ]] || die "upload $k: sha256 differs from UPSTREAM.json"
      mv -f "$f" "target/testbox-oracles/$k"
    done
    rm -rf "$1"
    mirror
    install_oracles
    ;;
  tests)
    (($# == 3)) || die "usage: tests KEY COMMIT RUN"
    key=$1 commit=$2 run=$3
    [[ ! -e $run ]] || die "$run exists"
    # mirror first: it refuses to run on zbook (a real dir at $ZBOOK_REPO) before at_commit moves HEAD.
    mirror
    at_commit "$commit"
    checkout "$key"
    install_oracles
    mkdir -p "$run"
    rc=0
    echo "build-goport-tests.sh at ${commit:0:12} ($(date -u +%T))"
    scripts/goport/build-goport-tests.sh "$PWD" "$run/testbin" > "$run/build.log" 2>&1 || rc=$?
    tail -2 "$run/build.log"
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
    mirror
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
  *) die "unknown command $cmd (testbox-remote.sh help)" ;;
esac
