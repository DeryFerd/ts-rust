#!/usr/bin/env bash
# Build-time benchmark of ts_goport: one timed `cargo build -p ts_goport --bins` (or BENCH_CMD) per call.
# Run it on a quiet host (mini-743d) under that host's lock. Compare numbers only
# within one host.
#
# usage: buildbench.sh <out-dir> <label> <toolchain> <profile> <action> [rustflags]
#   toolchain  rustup toolchain name (1.93.0, nightly-2026-06-17, ...)
#   profile    release, goport or dev
#   action     clean          remove this config's target dir, then build
#              build          build as is (a primer or a no-op check)
#              touch:<file>   touch a file (repo-relative), then build
#              edit:<file>    insert one statement at the top of one function, build, then revert the
#                             file: has_empty_object_intersection (checker/checker_p15.rs) or
#                             should_get_type (ls/hover.rs)
#   rustflags  extra RUSTFLAGS, for example "-Zthreads=8"
# Env: BENCH_INCREMENTAL=1 builds every workspace crate incrementally, BENCH_INCREMENTAL=ts_goport
# only ts_goport (the run-cargo-capped.sh edit-loop default); each has its own target dir. BENCH_JOBS
# (default 16, zbook's TS_CARGO_JOBS). BENCH_MEM_KIB (default 22 GiB) is the cgroup cap.
# BENCH_TAG=<name> gives a config with other env (CARGO_PROFILE_*) its own target dir.
# BENCH_CMD is the cargo command and its targets (default "build --bins"; for example "check",
# "build --bin tsgo" or "test --no-run"); each command has its own target dir.
# Each config (toolchain, profile, flags, incremental, command) has its own target dir under
# target/bench/, so a clean build is a real cold build. sccache is off.
# Output: <out-dir>/results.tsv (one row per build, with the peak memory of the whole build's
# cgroup), <out-dir>/logs/<label>.{log,time,html,peak}.
set -uo pipefail
[[ $# -ge 5 ]] || { sed -n '2,25p' "$0"; exit 2; }
OUT=$1 LABEL=$2 TC=$3 PROFILE=$4 ACTION=$5 FLAGS=${6:-}
WT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$WT" || exit 2
mkdir -p "$OUT/logs"
# A results.tsv with another header (an older buildbench.sh, before the cmd and peak_kib columns)
# would get rows that do not match it.
HEADER=$'label\thost\ttoolchain\tprofile\trustflags\tincr\taction\trc\twall_s\tuser_s\tsys_s\tmaxrss_kib\tcpu\tts_goport_lib_s\tload_before\trustc\tcmd\tpeak_kib'
if [[ -s $OUT/results.tsv && $(head -1 "$OUT/results.tsv") != "$HEADER" ]]; then
  echo "$OUT/results.tsv has another header (an older buildbench.sh): use a new out-dir" >&2
  exit 2
fi
INCR=${BENCH_INCREMENTAL:-0}
CMD=${BENCH_CMD:-build --bins}
read -ra cmd <<< "$CMD"
slug=$(printf '%s' "$FLAGS" | tr -c 'A-Za-z0-9=' _)
cslug=$(printf '%s' "${BENCH_CMD:-}" | tr -c 'A-Za-z0-9' _)
case $INCR in 0) isuf= ;; 1) isuf=-incr ;; *) isuf=-incr-$INCR ;; esac
TDIR=$WT/target/bench/$TC-$PROFILE${slug:+-$slug}$isuf${BENCH_TAG:+-$BENCH_TAG}${cslug:+-$cslug}
declare -A EDIT_ANCHORS=(
  [crates/ts_goport/src/checker/checker_p15.rs]='    pub fn has_empty_object_intersection(&mut self, t: TypeId) -> bool {'
  [crates/ts_goport/src/ls/hover.rs]='pub fn should_get_type(node: Node) -> bool {'
)

case $ACTION in
  clean) rm -rf "$TDIR" ;;
  build) ;;
  touch:*) f=${ACTION#touch:}; [[ -f $f ]] || { echo "no file $f" >&2; exit 2; }; touch "$f" ;;
  edit:*)
    f=${ACTION#edit:}; [[ -n ${EDIT_ANCHORS[$f]:-} ]] || { echo "edit supports only ${!EDIT_ANCHORS[*]}" >&2; exit 2; }
    cp "$f" "$OUT/logs/$LABEL.orig.rs"
    python3 - "$f" "${EDIT_ANCHORS[$f]}" <<'EOF' || exit 2
import sys
p, anchor = sys.argv[1], sys.argv[2]
s = open(p).read()
assert s.count(anchor + "\n") == 1, "anchor not unique"
indent = " " * (len(anchor) - len(anchor.lstrip()) + 4)
open(p, "w").write(s.replace(anchor + "\n", anchor + "\n" + indent + "std::hint::black_box(());\n"))
EOF
    ;;
  *) echo "unknown action $ACTION" >&2; exit 2 ;;
esac

load_before=$(cut -d' ' -f1-3 /proc/loadavg)
ver=$(rustc "+$TC" --version 2>&1)
case $PROFILE in release) prof_arg=(--release) ;; dev) prof_arg=() ;; *) prof_arg=(--profile "$PROFILE") ;; esac
rm -rf "$TDIR/cargo-timings"
mem_kib=${BENCH_MEM_KIB:-23068672}
# RUSTUP_TOOLCHAIN and RUSTFLAGS turn off run-cargo-capped.sh's own nightly choice. The build runs in
# this script's own scope (TS_CARGO_CGROUP_ACTIVE=1 skips the scope of run-cargo-capped.sh), so the
# scope's memory.peak is the peak of the whole build.
env RUSTC_WRAPPER= SCCACHE_DISABLE=1 TS_CARGO_SCCACHE=0 RUSTUP_TOOLCHAIN="$TC" RUSTFLAGS="$FLAGS" \
  TS_CARGO_JOBS="${BENCH_JOBS:-16}" TS_CARGO_MEMORY_LIMIT_KIB="$mem_kib" TS_CARGO_CGROUP_ACTIVE=1 \
  TS_CARGO_INCREMENTAL="$INCR" TS_CARGO_SEPARATE_TARGET=1 CARGO_TARGET_DIR="$TDIR" BENCH_PEAK="$OUT/logs/$LABEL.peak" \
  /usr/bin/time -f '%e %U %S %M %P' -o "$OUT/logs/$LABEL.time" \
  systemd-run --user --scope --quiet --collect -p "MemoryMax=${mem_kib}K" -p MemorySwapMax=0 \
  bash -c 'scripts/run-cargo-capped.sh "$@"; rc=$?
    cat "/sys/fs/cgroup$(sed -n "s/^0:://p" /proc/self/cgroup)/memory.peak" > "$BENCH_PEAK"; exit $rc' bench \
  "${cmd[0]}" "${prof_arg[@]}" -p ts_goport "${cmd[@]:1}" --timings \
  > "$OUT/logs/$LABEL.log" 2>&1
rc=$?
peak_kib=$(( $(cat "$OUT/logs/$LABEL.peak" 2>/dev/null || echo 0) / 1024 ))
if [[ $ACTION == edit:* ]]; then cp "$OUT/logs/$LABEL.orig.rs" "${ACTION#edit:}"; fi
cp "$TDIR"/cargo-timings/cargo-timing.html "$OUT/logs/$LABEL.html" 2>/dev/null
read -r wall user sys rss cpu < <(tail -1 "$OUT/logs/$LABEL.time")
# ts_goport lib compile time from the cargo timing data (0 when the unit did not build).
lib=$(python3 - "$OUT/logs/$LABEL.html" <<'EOF'
import json, re, sys
try:
    html = open(sys.argv[1]).read()
    units = json.loads(re.search(r"const UNIT_DATA = (\[.*?\]);\n", html, re.S).group(1))
    print(round(sum(u["duration"] for u in units if u["name"] == "ts_goport" and u["target"].strip() in ("", "lib")), 1))
except Exception:
    print("-")
EOF
)
[[ -s $OUT/results.tsv ]] || printf '%s\n' "$HEADER" > "$OUT/results.tsv"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$LABEL" "$(hostname)" "$TC" "$PROFILE" "${FLAGS:--}" "$INCR" \
  "$ACTION" "$rc" "$wall" "$user" "$sys" "$rss" "$cpu" "$lib" "$load_before" "$ver" "$CMD" "$peak_kib" >> "$OUT/results.tsv"
echo "$LABEL rc=$rc wall=${wall}s user=${user}s sys=${sys}s maxrss=${rss}KiB peak=${peak_kib}KiB cpu=$cpu lib=${lib}s"
exit $rc
