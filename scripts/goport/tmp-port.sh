#!/usr/bin/env bash
# Keeps the legacy /tmp tools alive. /tmp on zbook is tmpfs: a reboot empties it, and
# systemd-tmpfiles-clean deletes files there after 10 days. Old revision pipelines still pin
# /tmp/port/fp.py (and treehash.py), and every drive needs the cargo pool runner in /tmp.
# R110 failed after a 2h13m wait because tmpfiles deleted that runner.
#
# usage: tmp-port.sh save      copy /tmp/port into target/tmp-port-persist (run after a /tmp/port change)
#        tmp-port.sh restore   put back missing files in /tmp/port and the pool runner (never replaces a file)
#        tmp-port.sh check     exit 1 when a pinned file is missing or differs
# ~/.config/user-tmpfiles.d/ts-rust.conf runs the same restore at login.
# Put new tools in scripts/, never in /tmp.
set -euo pipefail
REPO=/home/theo/Code/sandbox/ts-rust
KEEP=$REPO/target/tmp-port-persist
POOL=/tmp/ts-rust-wave202-cargo-pool-three-lanes-opt1-four-jobs.sh
POOL_SRC=$REPO/target/runner-recovery/cargo-pool-three-lanes-opt1-four-jobs.sh
POOL_PIN=9fd7fda9feaebaf9038816e02f2065ddc45586b43ecf3a3eb9f112008c9ab906

case ${1:-} in
  save) mkdir -p "$KEEP"; rsync -a /tmp/port/ "$KEEP/"; echo "saved /tmp/port to $KEEP" ;;
  restore)
    [[ -d $KEEP ]] || { echo "no $KEEP; run 'tmp-port.sh save' first" >&2; exit 2; }
    rsync -a --ignore-existing "$KEEP/" /tmp/port/
    [[ -e $POOL ]] || cp -p "$POOL_SRC" "$POOL"
    find /tmp/port "$POOL" -exec touch -a -h {} +  # resets the 10-day aging clock
    echo "restored /tmp/port and the pool runner" ;;
  check)
    rc=0
    [[ "$(sha256sum "$POOL" 2>/dev/null | cut -c1-64)" == "$POOL_PIN" ]] || { echo "pool runner missing or changed: $POOL"; rc=1; }
    for f in fp.py treehash.py fpcommit.py; do
      cmp -s "/tmp/port/$f" "$REPO/scripts/goport/$f" || { echo "/tmp/port/$f missing or differs from scripts/goport/$f"; rc=1; }
    done
    exit $rc ;;
  *) sed -n '7,11p' "$0"; exit 2 ;;
esac
