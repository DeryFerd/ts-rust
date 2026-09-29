#!/usr/bin/env bash
# Runs arm64 Linux goport builds under qemu-aarch64 (user mode) on an x86_64 host and compares them with
# an x86_64 base.
#
# usage:
#   scripts/goport/xtest-arm64.sh identity <arm64-bin-dir> <x86_64-bin-dir> <out-dir> [<project>...]
#   scripts/goport/xtest-arm64.sh build-tests <out-testbin-dir> [<target>]
#   scripts/goport/xtest-arm64.sh tests <arm64-testbin-dir> <x86_64-testbin-dir> <out-dir> [<suite>:<filter>...]
#
# identity: runs `tsgo -p <config> --pretty false --outDir ... --tsBuildInfoFile ...` (the flags of
#   bin-identity.sh) with each side on each project and compares stdout, the exit code and the emitted tree
#   byte for byte. Projects: query hono zod effect (default: query hono). The arm64 side runs under qemu.
#   Writes <out-dir>/summary.txt, one line per project: EQUAL or DIFF(<what>), and the arm64 and x86_64 times.
# build-tests: builds the test binaries fswatch_linux and go_baselines and the goport_util lib tests for
#   <target> (default aarch64-unknown-linux-gnu) with cargo-zigbuild through run-cargo-capped.sh, in this
#   checkout, and copies them to <out-testbin-dir> (must not exist) with SUITES ("<suite>\t<crate dir>")
#   and COMMIT. The test binaries read their fixtures from this checkout (paths compiled in).
# tests: runs each <suite>:<filter> (a libtest name filter; default: the fswatch, vfs and execute modules,
#   see DEFAULT_TESTS) with both test bin dirs and compares each test name: a name that passes on x86_64
#   and not on arm64 is LOST. Each arm64 run is bounded (XTEST_TIMEOUT seconds, default 1800).
#   Writes <out-dir>/<suite>.<n>.{arm64,x86_64}.log and <out-dir>/tests.tsv (name, x86_64, arm64).
#
# qemu-user cannot exec another arm64 binary (no binfmt_misc entry on zbook), so the arm64 side runs with
# GOPORT_LAUNCH=0 (no worker process) and with _RJEM_MALLOC_CONF and GLIBC_TUNABLES set (tsgo and goport
# exec themselves once to set them). Neither changes the output. A test that starts an arm64 child process
# fails under qemu; the tests step lists those as LOST, so read the log before you call one a port bug.
# Big runs belong under systemd-run --user --collect -p MemoryMax=24G -p MemorySwapMax=0.
# Last stdout line: DONE, or FAIL rc=<N>.
set -uo pipefail

{
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
CO=$(cd -- "$here/../.." && pwd)
P=$(dirname "$(git -C "$here" rev-parse --path-format=absolute --git-common-dir)")/target/project-inputs
QEMU=${QEMU:-qemu-aarch64}
SYSROOT=${XTEST_SYSROOT:-/usr/aarch64-linux-gnu}
JEMALLOC_CONF="narenas:4,thp:always,metadata_thp:always"
DEFAULT_TESTS=(
  "fswatch_linux:"
  "go_baselines:units_platform::fswatch"
  "go_baselines:units_platform::watchmanager"
  "go_baselines:units_platform::lspwatcher"
  "go_baselines:units_platform::osvfs"
  "go_baselines:units_platform::cachedvfs"
  "go_baselines:units_platform::vfsmock"
  "go_baselines:units_platform::vfsmatch"
  "go_baselines:tsctests::"
  "goport_util_lib:"
)

fail() { echo "xtest-arm64.sh: $2" >&2; echo "FAIL rc=$1"; exit "$1"; }
usage() { sed -n '2,/^set -uo/p' "$0" | sed '$d'; echo "FAIL rc=2"; exit 2; }

# qemu command for an arm64 binary. A static (musl) binary needs no sysroot.
arm() {
  env GOPORT_LAUNCH=0 _RJEM_MALLOC_CONF="$JEMALLOC_CONF" GLIBC_TUNABLES=glibc.malloc.arena_max=8 \
    "$QEMU" -L "$SYSROOT" "$@"
}

cmd_identity() {
  (($# >= 3)) || usage
  local A B OUT
  A=$(realpath -- "$1") B=$(realpath -- "$2") OUT=$(realpath -m -- "$3")
  shift 3
  local names=("$@")
  ((${#names[@]})) || names=(query hono)
  [[ -x $A/tsgo && -x $B/tsgo ]] || fail 2 "missing tsgo in $A or $B"
  command -v "$QEMU" >/dev/null || fail 2 "$QEMU is not installed"
  rm -rf "$OUT"
  mkdir -p "$OUT"
  # name|cwd|emit config|emit flags (as in bin-identity.sh)
  local -A projects=(
    [query]="$P/query/source/packages/query-core|tsconfig.prod.json|--emitDeclarationOnly false --sourceMap --declarationMap"
    [hono]="$P/hono/source|tsconfig.build.json|--emitDeclarationOnly false --sourceMap --declarationMap"
    [zod]="$P/zod/source/packages/zod|tsconfig.build.json|"
    [effect]="$P/effect/source/packages/effect|tsconfig.json|--noEmit false"
  )
  local failed=0 name cwd emit flags side o start res files
  for name in "${names[@]}"; do
    [[ -n ${projects[$name]:-} ]] || fail 2 "unknown project $name"
    IFS='|' read -r cwd emit flags <<<"${projects[$name]}"
    local -A secs=()
    for side in arm64 x86_64; do
      o=$OUT/$side/$name
      mkdir -p "$o"
      start=$(date +%s.%N)
      if [[ $side == arm64 ]]; then
        # shellcheck disable=SC2086
        (cd "$cwd" && arm "$A/tsgo" -p "$emit" $flags --pretty false --outDir "$o/emit" \
          --tsBuildInfoFile "$o/tsbuildinfo" >"$o/tsgo.out" 2>"$o/tsgo.err"; echo $? >"$o/tsgo.rc")
      else
        # shellcheck disable=SC2086
        (cd "$cwd" && "$B/tsgo" -p "$emit" $flags --pretty false --outDir "$o/emit" \
          --tsBuildInfoFile "$o/tsbuildinfo" >"$o/tsgo.out" 2>"$o/tsgo.err"; echo $? >"$o/tsgo.rc")
      fi
      secs[$side]=$(awk -v a="$start" -v b="$(date +%s.%N)" 'BEGIN { print b - a }')
    done
    local a=$OUT/arm64/$name b=$OUT/x86_64/$name
    res=()
    for f in tsgo.out tsgo.rc; do cmp -s "$a/$f" "$b/$f" || res+=("$f"); done
    diff -r "$a/emit" "$b/emit" >"$OUT/$name.emit.diff" 2>&1 || res+=(emit)
    files=$(find "$a/emit" -type f 2>/dev/null | wc -l)
    local st=EQUAL
    if ((${#res[@]})); then st="DIFF(${res[*]})"; failed=1; fi
    printf '%s %s emit_files=%s rc=%s/%s diag_lines=%s arm64_s=%.1f x86_64_s=%.1f\n' "$name" "$st" "$files" \
      "$(cat "$a/tsgo.rc")" "$(cat "$b/tsgo.rc")" "$(wc -l <"$a/tsgo.out")" "${secs[arm64]}" "${secs[x86_64]}" |
      tee -a "$OUT/summary.txt"
  done
  if ((failed)); then echo "FAIL rc=1"; exit 1; fi
  echo DONE
}

cmd_build_tests() {
  (($# >= 1)) || usage
  local TB target=${2:-aarch64-unknown-linux-gnu}
  TB=$(realpath -m -- "$1")
  [[ ! -e $TB ]] || fail 2 "$TB exists"
  mkdir -p "$TB/logs"
  local json=$TB/logs/build.json
  (cd "$CO" && scripts/run-cargo-capped.sh zigbuild --release --locked --target "$target" \
    -p ts_goport --test fswatch_linux --test go_baselines -p goport_util --lib --tests \
    --message-format=json-render-diagnostics >"$json" 2>"$TB/logs/build.err") ||
    { tail -20 "$TB/logs/build.err" >&2; fail 1 "build failed (log $TB/logs/build.err)"; }
  # One executable per test target: <name> for [[test]] targets, <crate>_lib for lib tests.
  python3 - "$json" "$TB" "$CO" <<'EOF' || fail 1 "could not collect the test binaries"
import json, os, shutil, sys
log, tb, co = sys.argv[1:]
suites = []
for line in open(log):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") != "compiler-artifact" or not m.get("executable") or not m["profile"]["test"]:
        continue
    t = m["target"]
    name = t["name"] + "_lib" if "lib" in t["kind"] else t["name"]
    shutil.copy2(m["executable"], os.path.join(tb, name))
    crate_dir = os.path.relpath(os.path.dirname(m["manifest_path"]), co)
    suites.append(f"{name}\t{crate_dir}")
open(os.path.join(tb, "SUITES"), "w").write("\n".join(sorted(set(suites))) + "\n")
EOF
  git -C "$CO" rev-parse HEAD >"$TB/COMMIT"
  echo "$target" >"$TB/TARGET"
  cat "$TB/SUITES"
  echo DONE
}

cmd_tests() {
  (($# >= 3)) || usage
  local A B OUT
  A=$(realpath -- "$1") B=$(realpath -- "$2") OUT=$(realpath -m -- "$3")
  shift 3
  local specs=("$@")
  ((${#specs[@]})) || specs=("${DEFAULT_TESTS[@]}")
  mkdir -p "$OUT"
  local timeout_s=${XTEST_TIMEOUT:-1800} threads=${XTEST_THREADS:-8}
  local n=0 spec suite filter dir side log rc
  for spec in "${specs[@]}"; do
    suite=${spec%%:*} filter=${spec#*:}
    n=$((n + 1))
    [[ -x $A/$suite && -x $B/$suite ]] || { echo "$suite: missing in $A or $B" | tee -a "$OUT/summary.txt"; continue; }
    # libtest runs each binary in its crate dir, as cargo test does.
    dir=$(awk -F'\t' -v s="$suite" '$1 == s { print $2 }' "$A/SUITES")
    for side in arm64 x86_64; do
      log=$OUT/$suite.$n.$side.log
      if [[ $side == arm64 ]]; then
        (cd "$CO/$dir" && RUST_TEST_THREADS=$threads timeout "$timeout_s" \
          env GOPORT_LAUNCH=0 _RJEM_MALLOC_CONF="$JEMALLOC_CONF" GLIBC_TUNABLES=glibc.malloc.arena_max=8 \
          "$QEMU" -L "$SYSROOT" "$A/$suite" ${filter:+"$filter"} >"$log" 2>&1)
      else
        (cd "$CO/$dir" && RUST_TEST_THREADS=$threads timeout "$timeout_s" "$B/$suite" ${filter:+"$filter"} >"$log" 2>&1)
      fi
      rc=$?
      echo "$suite '${filter}' $side rc=$rc $(grep -m1 '^test result:' "$log")" | tee -a "$OUT/summary.txt"
    done
  done
  # Per-name compare over every log pair.
  python3 - "$OUT" <<'EOF'
import glob, os, re, sys
out = sys.argv[1]
res = {}
for log in sorted(glob.glob(os.path.join(out, "*.log"))):
    base, side = log.rsplit(".", 2)[0], log.rsplit(".", 2)[1]
    suite = os.path.basename(base).rsplit(".", 1)[0]
    for line in open(log, errors="replace"):
        m = re.match(r"^test (\S+) \.\.\. (ok|FAILED|ignored)", line)
        if m:
            res.setdefault((suite, m.group(1)), {})[side] = m.group(2)
lost = retained = other = 0
with open(os.path.join(out, "tests.tsv"), "w") as f:
    for (suite, name), r in sorted(res.items()):
        x, a = r.get("x86_64", "absent"), r.get("arm64", "absent")
        f.write(f"{suite}\t{name}\t{x}\t{a}\n")
        if x == "ok" and a != "ok":
            lost += 1
            print(f"LOST {suite} {name} x86_64={x} arm64={a}")
        elif x == "ok":
            retained += 1
        else:
            other += 1
print(f"names {len(res)}, retained {retained}, lost {lost}, not passing on x86_64 {other}")
open(os.path.join(out, "summary.txt"), "a").write(f"names {len(res)} retained {retained} lost {lost} other {other}\n")
sys.exit(1 if lost else 0)
EOF
  if (($? != 0)); then echo "FAIL rc=1"; exit 1; fi
  echo DONE
}

case "${1:-}" in
  identity) shift; cmd_identity "$@" ;;
  build-tests) shift; cmd_build_tests "$@" ;;
  tests) shift; cmd_tests "$@" ;;
  *) usage ;;
esac
}
