#!/usr/bin/env bash
# Keeps the legacy /tmp/port tools alive. /tmp on zbook is tmpfs: a reboot empties it, and
# systemd-tmpfiles-clean deletes files there after 10 days. Old revision bindings pin /tmp/port/fp.py,
# compat/p5-corpus and typesyms/scale call /tmp/port/treehash.py, the oracle sweeps write their build
# info under /tmp/port, and scripts/upstream/rerecord.sh (sweep step) runs `restore` first.
#
# usage: tmp-port.sh save      copy /tmp/port into target/tmp-port-persist (run after a /tmp/port change)
#        tmp-port.sh restore   put back missing files in /tmp/port (never replaces a file)
#        tmp-port.sh check     exit 1 when a pinned file is missing or differs
# ~/.config/user-tmpfiles.d/ts-rust.conf runs the same restore at login.
# Put new tools in scripts/, never in /tmp.
set -euo pipefail
REPO=/home/theo/Code/sandbox/ts-rust
KEEP=$REPO/target/tmp-port-persist

case ${1:-} in
  save) mkdir -p "$KEEP"; rsync -a /tmp/port/ "$KEEP/"; echo "saved /tmp/port to $KEEP" ;;
  restore)
    [[ -d $KEEP ]] || { echo "no $KEEP; run 'tmp-port.sh save' first" >&2; exit 2; }
    rsync -a --ignore-existing "$KEEP/" /tmp/port/
    find /tmp/port -exec touch -a -h {} +  # resets the 10-day aging clock
    echo "restored /tmp/port" ;;
  check)
    rc=0
    for f in fp.py treehash.py; do
      cmp -s "/tmp/port/$f" "$REPO/scripts/goport/$f" || { echo "/tmp/port/$f missing or differs from scripts/goport/$f"; rc=1; }
    done
    exit $rc ;;
  *) sed -n '7,9p' "$0"; exit 2 ;;
esac
