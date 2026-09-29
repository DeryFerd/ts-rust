#!/bin/bash
# Waits until no agent cargo build has run for 120 s, then starts the given driver.
cd /home/theo/Code/sandbox/ts-rust
quiet=0
while [ $quiet -lt 120 ]; do
  if pgrep -f "[r]un-cargo-capped.sh" >/dev/null; then quiet=0; else quiet=$((quiet+10)); fi
  sleep 10
done
echo "quiet at $(date -u +%T), starting $1"
exec bash "$1"
