#!/usr/bin/env bash
# Sessions of the ts_goport build-time benchmark (buildbench.sh). One session fits in one
# host-lock hold of about 60 minutes. Run it on the timing host, under its lock:
#   flock /tmp/goport-remote-dbook.lock scripts/goport/remote.sh run dbook-lan \
#     'export RUSTUP_HOME=/home/dbook/.rustup CARGO_HOME=/home/dbook/.cargo; <wt>/scripts/goport/buildbench-plan.sh <session> <out-dir>'
# Sessions: setup, s1 .. s7, identity, perf (the 2026-09-28 measurement, bench.md in
# target/continuation-r97-goport/buildspeed/), defaults (the run-cargo-capped.sh edit-loop
# defaults; run it before and after a build change), devloop (the same defaults in the dev
# profile: check, --bin tsgo, --bins and test --no-run) and toolchains (the evidence toolchain:
# 1.93.0, 1.95.0 and 1.99.0, with bin-identity.sh). The last line is DONE or FAIL rc=N.
set -uo pipefail
S=${1:?session} OUT=${2:?out-dir}
mkdir -p "$OUT"; echo "host $(hostname) session $S start $(date -Is) load $(cut -d" " -f1-3 /proc/loadavg)"
H=$(cd "$(dirname "$0")" && pwd)
B=$H/buildbench.sh
ST=1.93.0 NT=nightly-2026-06-17
CK=crates/ts_goport/src/checker/checker_p15.rs
LS=crates/ts_goport/src/ls/hover.rs
LG=crates/ts_goport/src/lsp/lsproto/lsp_generated/structures_p1.rs
rc=0
b() { "$B" "$OUT" "$@" || rc=$?; }
# The four release cells, run twice: clean, then one touch in the checker, ls and lsp_generated.
cells() {
  local p=$1 tc=$2 fl=$3 r
  for r in ${4:-1 2}; do
    b "$p-clean-r$r" "$tc" release clean "$fl"
    b "$p-touch-checker-r$r" "$tc" release "touch:$CK" "$fl"
    b "$p-touch-ls-r$r" "$tc" release "touch:$LS" "$fl"
    b "$p-touch-lspgen-r$r" "$tc" release "touch:$LG" "$fl"
  done
}
case $S in
  setup)
    rustup toolchain install "$ST" "$NT" --profile minimal || rc=$?
    (cd "$H/../.." && cargo "+$ST" fetch && cargo "+$NT" fetch) || rc=$? ;;
  s1) cells stable "$ST" "" ;;
  s2) cells nz8 "$NT" "-Zthreads=8" ;;
  s3) cells nz16 "$NT" "-Zthreads=16" 1
      b nz1-clean-r1 "$NT" release clean ""
      b nz1-touch-checker-r1 "$NT" release "touch:$CK" ""
      # Codegen is most of a -Zthreads=8 touch rebuild: more, smaller codegen units.
      CARGO_PROFILE_RELEASE_CODEGEN_UNITS=64 BENCH_TAG=cgu64 b nz8-cgu64-clean-r1 "$NT" release clean "-Zthreads=8"
      CARGO_PROFILE_RELEASE_CODEGEN_UNITS=64 BENCH_TAG=cgu64 b nz8-cgu64-touch-checker-r1 "$NT" release "touch:$CK" "-Zthreads=8" ;;
  s4) BENCH_INCREMENTAL=1 b stable-incr-clean-r1 "$ST" release clean ""
      BENCH_INCREMENTAL=1 b stable-incr-touch-checker-r1 "$ST" release "touch:$CK" ""
      BENCH_INCREMENTAL=1 b stable-incr-edit-checker-r1 "$ST" release "edit:$CK" ""
      BENCH_INCREMENTAL=1 b stable-incr-revert-checker-r1 "$ST" release build ""
      # Newer stable (1.98.1): the nightly control (nz1) was much faster than 1.93.0.
      rustup toolchain install 1.98.1 --profile minimal > /dev/null 2>&1 || rc=$?
      b s198-clean-r1 1.98.1 release clean ""
      b s198-touch-checker-r1 1.98.1 release "touch:$CK" "" ;;
  s5) b goport-stable-clean-r1 "$ST" goport clean ""
      b goport-stable-touch-checker-r1 "$ST" goport "touch:$CK" "" ;;
  s6) b goport-nz8-clean-r1 "$NT" goport clean "-Zthreads=8"
      b goport-nz8-touch-checker-r1 "$NT" goport "touch:$CK" "-Zthreads=8" ;;
  # Copies the stable and nightly -Zthreads=8 release bins (from s1 and s2) to $OUT/bins and
  # compares their outputs (bin-identity.sh).
  identity)
    T=$H/../../target/bench
    for pair in "stable:$T/$ST-release/release" "nz8:$T/$NT-release-_Zthreads=8/release"; do
      n=${pair%%:*} d=${pair#*:}; mkdir -p "$OUT/bins/$n"
      for f in tsgo goport goport_emit goport_typesyms goport_build goport_watch goport_live_programs goport_multiprog astdump; do
        cp "$d/$f" "$OUT/bins/$n/" || rc=$?
      done
      echo "${BENCH_COMMIT:-unknown}" > "$OUT/bins/$n/COMMIT"
      (cd "$OUT/bins/$n" && sha256sum tsgo goport goport_emit > sha256.txt)
    done
    "$H/bin-identity.sh" "$OUT/identity" "$OUT/bins/stable" "$OUT/bins/nz8" || rc=$? ;;
  # Run time of the stable and nightly -Zthreads=8 goport bins (identity session copies), perf.sh.
  perf)
    I=$(dirname "$OUT")/$(basename "$OUT" | sed 's/-perf$/-identity/')/bins
    PERF_WAIT=1 /home/theo/Code/sandbox/ts-rust/scripts/goport/perf.sh buildspeed-toolchain-1 \
      "$I/stable/goport" "$I/nz8/goport" | tee "$OUT/perf.txt" || rc=$?
    cp -r /home/theo/Code/sandbox/ts-rust/target/continuation-r97-goport/perf/buildspeed-toolchain-1 "$OUT/" || rc=$? ;;
  # Incremental with nightly -Zthreads=8, a second stable incremental edit, then identity and run
  # time of the 1.98.1 and incremental bins against 1.93.0.
  s7) BENCH_INCREMENTAL=1 b nz8-incr-clean-r1 "$NT" release clean "-Zthreads=8"
      BENCH_INCREMENTAL=1 b nz8-incr-touch-checker-r1 "$NT" release "touch:$CK" "-Zthreads=8"
      BENCH_INCREMENTAL=1 b nz8-incr-edit-checker-r1 "$NT" release "edit:$CK" "-Zthreads=8"
      BENCH_INCREMENTAL=1 b nz8-incr-revert-checker-r1 "$NT" release build "-Zthreads=8"
      BENCH_INCREMENTAL=1 b stable-incr-edit-checker-r2 "$ST" release "edit:$CK" ""
      BENCH_INCREMENTAL=1 b stable-incr-revert-checker-r2 "$ST" release build ""
      T=$H/../../target/bench
      for pair in "stable:$T/$ST-release/release" "s198:$T/1.98.1-release/release" \
          "stable-incr:$T/$ST-release-incr/release" "nz8-incr:$T/$NT-release-_Zthreads=8-incr/release"; do
        n=${pair%%:*} d=${pair#*:}; mkdir -p "$OUT/bins/$n"
        for f in tsgo goport goport_emit goport_typesyms goport_build; do cp "$d/$f" "$OUT/bins/$n/" || rc=$?; done
        echo "${BENCH_COMMIT:-unknown}" > "$OUT/bins/$n/COMMIT"
      done
      for n in s198 stable-incr nz8-incr; do
        "$H/bin-identity.sh" "$OUT/identity-$n" "$OUT/bins/stable" "$OUT/bins/$n" | sed "s/^/$n vs stable: /" || rc=$?
      done
      # The emitted trees are large and only needed on a DIFF.
      for n in s198 stable-incr nz8-incr; do
        grep -q DIFF "$OUT/identity-$n/summary.txt" || rm -rf "$OUT/identity-$n/a" "$OUT/identity-$n/b"
      done
      PERF_WAIT=1 /home/theo/Code/sandbox/ts-rust/scripts/goport/perf.sh buildspeed-toolchain-2 "$OUT/bins/stable/goport" \
        "$OUT/bins/s198/goport" "$OUT/bins/stable-incr/goport" "$OUT/bins/nz8-incr/goport" | tee "$OUT/perf.txt" || rc=$? ;;
  # The run-cargo-capped.sh edit-loop defaults: nightly -Zthreads=8, incremental ts_goport only.
  defaults)
    for r in 1 2; do
      BENCH_INCREMENTAL=ts_goport b "defaults-clean-r$r" "$NT" release clean "-Zthreads=8"
      BENCH_INCREMENTAL=ts_goport b "defaults-touch-checker-r$r" "$NT" release "touch:$CK" "-Zthreads=8"
      BENCH_INCREMENTAL=ts_goport b "defaults-edit-checker-r$r" "$NT" release "edit:$CK" "-Zthreads=8"
      BENCH_INCREMENTAL=ts_goport b "defaults-revert-checker-r$r" "$NT" release build "-Zthreads=8"
    done ;;
  # The same defaults in the dev profile, for each edit-loop command: check, one bin, the 9 bins and
  # the test executables. A one-line edit in the checker and one in ls (each with its revert).
  devloop)
    for r in 1 2; do
      for c in "check" "build --bin tsgo" "build --bins" "test --no-run"; do
        n=$(printf '%s' "$c" | tr -cs 'a-z' -); n=${n%-}
        for a in clean "touch:$CK" "edit:$CK" build "edit:$LS" build; do
          case $a in
            clean) l=clean ;; touch:*) l=touch-checker ;; edit:"$CK") l=edit-checker ;; edit:*) l=edit-ls ;;
            build) [[ $l == edit-checker ]] && l=revert-checker || l=revert-ls ;;
          esac
          BENCH_CMD=$c BENCH_INCREMENTAL=ts_goport b "dev-$n-$l-r$r" "$NT" dev "$a" "-Zthreads=8"
        done
      done
    done ;;
  # The evidence toolchain: release builds with the candidate.sh evidence settings (no nightly, no
  # incremental) on 1.93.0, 1.95.0 (build-release.sh) and a newer stable, then bin-identity.sh of each
  # against 1.93.0. The revert cell rebuilds the unedited source, so the copied bins are of it.
  toolchains)
    T=$H/../../target/bench
    for tc in "$ST" 1.95.0 1.99.0; do
      rustup toolchain install "$tc" --profile minimal > /dev/null 2>&1 || rc=$?
      b "tc-$tc-clean-r1" "$tc" release clean ""
      b "tc-$tc-touch-checker-r1" "$tc" release "touch:$CK" ""
      b "tc-$tc-edit-checker-r1" "$tc" release "edit:$CK" ""
      b "tc-$tc-revert-checker-r1" "$tc" release build ""
      mkdir -p "$OUT/bins/$tc"
      for f in tsgo goport; do cp "$T/$tc-release/release/$f" "$OUT/bins/$tc/" || rc=$?; done
    done
    for tc in 1.95.0 1.99.0; do
      "$H/bin-identity.sh" "$OUT/identity-$tc" "$OUT/bins/$ST" "$OUT/bins/$tc" | sed "s/^/$tc vs $ST: /" || rc=$?
      grep -q DIFF "$OUT/identity-$tc/summary.txt" || rm -rf "$OUT/identity-$tc/a" "$OUT/identity-$tc/b"
    done ;;
  *) echo "unknown session $S" >&2; rc=2 ;;
esac
((rc == 0)) && echo DONE || echo "FAIL rc=$rc"
exit $rc
