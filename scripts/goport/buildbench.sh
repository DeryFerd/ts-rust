#!/usr/bin/env bash
# Build-time benchmark of ts_goport: one timed `cargo build -p ts_goport --bins` per call.
# Run it on a quiet host (mini-abf9 or mini-743d) under that host's lock. Compare numbers only
# within one host.
#
# usage: buildbench.sh <out-dir> <label> <toolchain> <profile> <action> [rustflags]
#   toolchain  rustup toolchain name (1.93.0, nightly-2026-06-17, ...)
#   profile    release or goport
#   action     clean          remove this config's target dir, then build
#              build          build as is (a primer or a no-op check)
#              touch:<file>   touch a file (repo-relative), then build
#              edit:<file>    insert one statement in has_empty_object_intersection
#                             (checker/checker_p15.rs only), build, then revert the file
#   rustflags  extra RUSTFLAGS, for example "-Zthreads=8"
# Env: BENCH_INCREMENTAL=1 builds every workspace crate incrementally, BENCH_INCREMENTAL=ts_goport
# only ts_goport (the run-cargo-capped.sh edit-loop default); each has its own target dir. BENCH_JOBS
# (default 16, zbook's TS_CARGO_JOBS). BENCH_MEM_KIB (default 22 GiB) is the cgroup cap.
# BENCH_TAG=<name> gives a config with other env (CARGO_PROFILE_*) its own target dir.
# Each config (toolchain, profile, flags, incremental) has its own target dir under
# target/bench/, so a clean build is a real cold build. sccache is off.
# Output: <out-dir>/results.tsv (one row per build), <out-dir>/logs/<label>.{log,time,html}.
set -uo pipefail
[[ $# -ge 5 ]] || { sed -n '2,19p' "$0"; exit 2; }
OUT=$1 LABEL=$2 TC=$3 PROFILE=$4 ACTION=$5 FLAGS=${6:-}
WT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$WT" || exit 2
mkdir -p "$OUT/logs"
INCR=${BENCH_INCREMENTAL:-0}
slug=$(printf '%s' "$FLAGS" | tr -c 'A-Za-z0-9=' _)
case $INCR in 0) isuf= ;; 1) isuf=-incr ;; *) isuf=-incr-$INCR ;; esac
TDIR=$WT/target/bench/$TC-$PROFILE${slug:+-$slug}$isuf${BENCH_TAG:+-$BENCH_TAG}
EDIT_FILE=crates/ts_goport/src/checker/checker_p15.rs
EDIT_ANCHOR='    pub fn has_empty_object_intersection(&mut self, t: TypeId) -> bool {'

case $ACTION in
  clean) rm -rf "$TDIR" ;;
  build) ;;
  touch:*) f=${ACTION#touch:}; [[ -f $f ]] || { echo "no file $f" >&2; exit 2; }; touch "$f" ;;
  edit:*)
    f=${ACTION#edit:}; [[ $f == "$EDIT_FILE" ]] || { echo "edit only supports $EDIT_FILE" >&2; exit 2; }
    cp "$f" "$OUT/logs/$LABEL.orig.rs"
    python3 - "$f" "$EDIT_ANCHOR" <<'EOF' || exit 2
import sys
p, anchor = sys.argv[1], sys.argv[2]
s = open(p).read()
assert s.count(anchor + "\n") == 1, "anchor not unique"
open(p, "w").write(s.replace(anchor + "\n", anchor + "\n        std::hint::black_box(());\n"))
EOF
    ;;
  *) echo "unknown action $ACTION" >&2; exit 2 ;;
esac

load_before=$(cut -d' ' -f1-3 /proc/loadavg)
ver=$(rustc "+$TC" --version 2>&1)
prof_arg=(--release); [[ $PROFILE == release ]] || prof_arg=(--profile "$PROFILE")
rm -rf "$TDIR/cargo-timings"
# RUSTUP_TOOLCHAIN and RUSTFLAGS turn off run-cargo-capped.sh's own nightly choice.
env RUSTC_WRAPPER= SCCACHE_DISABLE=1 TS_CARGO_SCCACHE=0 RUSTUP_TOOLCHAIN="$TC" RUSTFLAGS="$FLAGS" \
  TS_CARGO_JOBS="${BENCH_JOBS:-16}" TS_CARGO_MEMORY_LIMIT_KIB="${BENCH_MEM_KIB:-23068672}" \
  TS_CARGO_INCREMENTAL="$INCR" TS_CARGO_SEPARATE_TARGET=1 CARGO_TARGET_DIR="$TDIR" \
  /usr/bin/time -f '%e %U %S %M %P' -o "$OUT/logs/$LABEL.time" \
  scripts/run-cargo-capped.sh build "${prof_arg[@]}" -p ts_goport --bins --timings \
  > "$OUT/logs/$LABEL.log" 2>&1
rc=$?
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
[[ -s $OUT/results.tsv ]] || printf 'label\thost\ttoolchain\tprofile\trustflags\tincr\taction\trc\twall_s\tuser_s\tsys_s\tmaxrss_kib\tcpu\tts_goport_lib_s\tload_before\trustc\n' > "$OUT/results.tsv"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$LABEL" "$(hostname)" "$TC" "$PROFILE" "${FLAGS:--}" "$INCR" \
  "$ACTION" "$rc" "$wall" "$user" "$sys" "$rss" "$cpu" "$lib" "$load_before" "$ver" >> "$OUT/results.tsv"
echo "$LABEL rc=$rc wall=${wall}s user=${user}s sys=${sys}s maxrss=${rss}KiB cpu=$cpu lib=${lib}s"
exit $rc
