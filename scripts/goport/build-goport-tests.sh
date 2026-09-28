#!/usr/bin/env bash
# Builds the protected goport test binaries at a checkout and copies them to a test bin dir.
#
# usage: scripts/goport/build-goport-tests.sh <checkout> <testbin-dir>
#
# Builds like the candidate release bins (candidate.sh side): the default toolchain (TS_CARGO_NIGHTLY=0),
# no incremental cache, --release --locked, in the shared candidate target runtime/cargo-target under
# its lock /tmp/ts-rust-candidate-target.lock. The test binaries:
#   ts_goport lib, go_baselines, multi_program, emit_pool, early_emit, fswatch_linux,
#   goport_util lib, goport_lsproto lib, and the lib tests of the kept crates in KEPT below
#   (a kept crate that the checkout no longer has is skipped).
# <testbin-dir> (must not exist) then holds:
#   <suite>                one file per test binary (ts_goport_lib, go_baselines, ts_scanner_lib, ...)
#   relbin/                the ts_goport release bins of the same build; multi_program and early_emit
#                          run them (their paths are compiled in)
#   COMMIT, TREE           the checkout HEAD at the start and its crates tree
#   BUILD_ROOT             the checkout path compiled into the test binaries (fixtures)
#   BUILD_TARGET           the target dir compiled into them (BUILD_TARGET/release/<bin>)
#   TOOLCHAIN              rustc --version of the build
#   bins.sha256            every test binary and relbin/<bin>
#   logs/                  the cargo output
# goport-tests.sh runs the dir. The checkout must be clean under crates/, Cargo.toml and Cargo.lock
# (crates/ts_goport/CANDIDATE.md excepted), and those must not change during the build (other commits
# in the checkout are fine). Last stdout line: DONE or FAIL rc=<N>.
set -uo pipefail

# One brace group: bash reads the whole script before it runs it, so an edit of this file does not
# change a running build.
{
KEPT=(ts_scanner ts_ast ts_diagnostics ts_path ts_core ts_jsnum)
GOPORT_TESTS=(go_baselines multi_program emit_pool early_emit fswatch_linux)

fail() { echo "build-goport-tests.sh: $2" >&2; echo "FAIL rc=$1"; exit "$1"; }
[[ $# == 2 ]] || { sed -n '2,/^set -uo/p' "$0" | sed '$d'; echo "FAIL rc=2"; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# The main checkout: the parent of the common git dir (this script can run from a worktree).
ROOT=$(dirname "$(git -C "$here" rev-parse --path-format=absolute --git-common-dir)")
TARGET=$ROOT/target/continuation-r97-goport/runtime/cargo-target
CO=$(realpath -- "$1") || fail 2 "no checkout $1"
TB=$(realpath -m -- "$2")
[[ ! -e $TB ]] || fail 2 "$TB exists (a test bin dir is never replaced)"
[[ -f $CO/crates/ts_goport/Cargo.toml ]] || fail 2 "$CO has no crates/ts_goport"

# build_inputs: the committed crates tree, Cargo.toml and Cargo.lock, and each dirty or untracked path
# under them.
build_inputs() {
  git -C "$CO" rev-parse HEAD:crates HEAD:Cargo.toml HEAD:Cargo.lock
  git -C "$CO" status --porcelain --untracked-files=all -- crates Cargo.toml Cargo.lock |
    grep -v '^?? crates/ts_goport/CANDIDATE.md$'
}
commit=$(git -C "$CO" rev-parse HEAD)
before=$(build_inputs)
[[ $(wc -l <<< "$before") == 3 ]] || fail 3 "dirty build inputs in $CO:
$(sed -n '4,$p' <<< "$before")"
tree=$(sed -n 1p <<< "$before")

pkgs=()
for c in goport_util goport_lsproto "${KEPT[@]}"; do
  if [[ -f $CO/crates/$c/Cargo.toml || -f $CO/crates/ts_goport/parts/$c/Cargo.toml ]]; then pkgs+=(-p "$c"); fi
done
tests=()
for t in "${GOPORT_TESTS[@]}"; do tests+=(--test "$t"); done

NEW=$TB.new
rm -rf "$NEW" && mkdir -p "$NEW/relbin" "$NEW/logs" || fail 4 "cannot make $NEW"
echo "$(date -u +%FT%TZ) build test bins of $CO ${commit:0:9} (crates tree ${tree:0:12}) in $TARGET"

# The target lock keeps a candidate side run from replacing the target's bins between the build and
# the copy. Cargo runs with fd 8 closed, so a started sccache server does not keep the lock.
exec 8> /tmp/ts-rust-candidate-target.lock
flock 8
cargo_test() {
  (cd "$CO" && TS_CARGO_NIGHTLY=0 TS_CARGO_INCREMENTAL=0 TS_CARGO_LOCK_ID=candidate-side \
    TS_CARGO_JOBS="${TS_CARGO_JOBS:-12}" TS_CARGO_SEPARATE_TARGET=1 CARGO_TARGET_DIR="$TARGET" \
    "$ROOT/scripts/run-cargo-capped.sh" test --release --locked --no-run \
    --message-format=json-render-diagnostics "$@") 8>&-
}
cargo_test -p ts_goport --lib "${tests[@]}" > "$NEW/logs/build-ts_goport.json" 2> "$NEW/logs/build-ts_goport.log" ||
  fail 5 "ts_goport test build failed; see $NEW/logs/build-ts_goport.log"
echo "$(date -u +%FT%TZ) ts_goport tests built"
cargo_test "${pkgs[@]}" --lib > "$NEW/logs/build-crates.json" 2> "$NEW/logs/build-crates.log" ||
  fail 5 "crate test build failed; see $NEW/logs/build-crates.log"
echo "$(date -u +%FT%TZ) crate tests built"

# Copy each test executable (profile.test) under its suite name, and each ts_goport bin to relbin/.
python3 - "$NEW" "$NEW/logs/build-ts_goport.json" "$NEW/logs/build-crates.json" << 'PY' || fail 6 "copy failed"
import json, os, shutil, sys
new, logs = sys.argv[1], sys.argv[2:]
seen = {}
for path in logs:
    for line in open(path):
        if not line.startswith('{'):
            continue
        m = json.loads(line)
        if m.get('reason') != 'compiler-artifact' or not m.get('executable'):
            continue
        kind = m['target']['kind']
        if m['profile']['test']:
            name = m['target']['name'] + '_lib' if kind == ['lib'] else m['target']['name']
            dest = os.path.join(new, name)
        elif kind == ['bin'] and m['manifest_path'].endswith('/crates/ts_goport/Cargo.toml'):
            dest = os.path.join(new, 'relbin', m['target']['name'])
        else:
            continue
        if seen.get(dest, m['executable']) != m['executable']:
            sys.exit(f'two executables for {dest}: {seen[dest]} and {m["executable"]}')
        seen[dest] = m['executable']
for dest, src in sorted(seen.items()):
    shutil.copy2(src, dest)
    print(f'{os.path.relpath(dest, new)} <- {src}')
PY
exec 8>&-

[[ $(build_inputs) == "$before" ]] || fail 7 "the build inputs of $CO changed during the build; $NEW is not kept"
want=(ts_goport_lib goport_util_lib goport_lsproto_lib "${GOPORT_TESTS[@]}")
for c in "${KEPT[@]}"; do [[ " ${pkgs[*]} " != *" $c "* ]] || want+=("${c}_lib"); done
for t in "${want[@]}"; do [[ -x $NEW/$t ]] || fail 8 "no test binary $t"; done
[[ -x $NEW/relbin/tsgo && -x $NEW/relbin/goport ]] || fail 8 "no relbin/tsgo or relbin/goport"

echo "$commit" > "$NEW/COMMIT"
echo "$tree" > "$NEW/TREE"
echo "$CO" > "$NEW/BUILD_ROOT"
echo "$TARGET" > "$NEW/BUILD_TARGET"
(cd "$CO" && rustc --version) > "$NEW/TOOLCHAIN"
(cd "$NEW" && find . -maxdepth 2 -type f -perm -u+x | sed 's|^\./||' | sort | xargs sha256sum > bins.sha256)
mv "$NEW" "$TB" || fail 9 "cannot move $NEW to $TB"
echo "$(date -u +%FT%TZ) $TB: $(grep -vc ' relbin/' "$TB/bins.sha256") test binaries, $(grep -c ' relbin/' "$TB/bins.sha256") release bins"
echo DONE
exit 0
}
