#!/usr/bin/env bash
# Builds the protected goport test binaries at a checkout and copies them to a test bin dir.
#
# usage: scripts/goport/build-goport-tests.sh <checkout> <testbin-dir>
#
# Builds like the candidate release bins (candidate.sh side): the default toolchain (TS_CARGO_NIGHTLY=0),
# no incremental cache, --release --locked, in the shared candidate target runtime/cargo-target under
# its lock /tmp/ts-rust-candidate-target.lock. The test binaries: the lib tests and every [[test]]
# target (go_baselines too, which has test = false) of each workspace member that is not in
# NOT_PROTECTED below. `cargo metadata` of the checkout gives the list, so a new crate (a parts/ crate,
# a kept crate) or a new tests/*.rs target joins the set with no edit here. Bin and example targets have
# no tests and are not built. At R131 that is ts_goport (lib, go_baselines, multi_program, emit_pool,
# early_emit, fswatch_linux), goport_util, goport_lsproto and the kept crates ts_scanner, ts_ast,
# ts_diagnostics, ts_path, ts_core and ts_jsnum.
# <testbin-dir> (must not exist) then holds:
#   <suite>                one file per test binary: <lib>_lib for lib tests, else the test target name
#   SUITES                 "<suite>\t<crate dir>" per test binary (the crate dir relative to the
#                          checkout; goport-tests.sh runs each binary there, as cargo test does)
#   relbin/                the ts_goport release bins of the same build; multi_program and early_emit
#                          run them (their paths are compiled in)
#   COMMIT, TREE           the checkout HEAD at the start and its crates tree
#   BUILD_ROOT             the checkout path compiled into the test binaries (fixtures)
#   BUILD_TARGET           the target dir compiled into them (BUILD_TARGET/release/<bin>)
#   TOOLCHAIN              rustc --version of the build
#   bins.sha256            every test binary, relbin/<bin> and SUITES
#   logs/                  the cargo output
# goport-tests.sh runs the dir. The checkout must be clean under crates/, Cargo.toml and Cargo.lock
# (crates/ts_goport/CANDIDATE.md excepted), and those must not change during the build (other commits
# in the checkout are fine). Last stdout line: DONE or FAIL rc=<N>.
set -uo pipefail

# One brace group: bash reads the whole script before it runs it, so an edit of this file does not
# change a running build.
{
# Workspace members whose tests are not protected: the legacy stack (stages 2 and 3 of the legacy
# removal delete it) and the tools (the codegen tools: see docs/goport-protected/README.md).
NOT_PROTECTED=(ts_binder ts_bundled ts_checker ts_cli ts_compiler ts_config ts_diagnostic_writer ts_evaluator
  ts_fswatch ts_glob ts_incremental ts_jsonrpc ts_lsp ts_module ts_options ts_outputpaths ts_parser
  ts_printer ts_project ts_semver ts_sourcemap ts_vfs ts_watch
  ts_ast_codegen ts_compare ts_diagnostics_codegen ts_fixture)

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

NEW=$TB.new
rm -rf "$NEW" && mkdir -p "$NEW/relbin" "$NEW/logs" || fail 4 "cannot make $NEW"

# The cargo arguments of the two builds (ts_goport, then the other protected members), one per line,
# and the planned suites, from `cargo metadata` of the checkout.
(cd "$CO" && cargo metadata --no-deps --format-version 1 --locked --offline) > "$NEW/logs/metadata.json" \
  2> "$NEW/logs/metadata.log" || fail 4 "cargo metadata failed; see $NEW/logs/metadata.log"
python3 - "$NEW" "${NOT_PROTECTED[@]}" << 'PY' || fail 4 "cannot plan the test build"
import json, os, sys
LIB_KINDS = {'lib', 'rlib', 'dylib', 'cdylib', 'staticlib', 'proc-macro'}
new, skip = sys.argv[1], set(sys.argv[2:])
meta = json.load(open(os.path.join(new, 'logs', 'metadata.json')))
members = set(meta['workspace_members'])
groups = {'ts_goport': [], 'crates': []}
suites = []
for p in sorted(meta['packages'], key=lambda p: p['name']):
    if p['id'] not in members or p['name'] in skip:
        continue
    pkg = []
    for t in p['targets']:
        if set(t['kind']) & LIB_KINDS and t['test']:
            pkg.append('--lib')
            suites.append(t['name'] + '_lib')
        elif t['kind'] == ['test']:
            pkg += ['--test', t['name']]
            suites.append(t['name'])
    if pkg:
        g = groups['ts_goport' if p['name'] == 'ts_goport' else 'crates']
        # cargo applies --lib and each --test to all packages of a build; `--lib` once is enough.
        g += ['-p', p['name']] + [a for a in pkg if a != '--lib' or '--lib' not in g]
for name, args in groups.items():
    open(os.path.join(new, 'logs', f'args-{name}'), 'w').write(''.join(a + '\n' for a in args))
open(os.path.join(new, 'logs', 'planned'), 'w').write(''.join(s + '\n' for s in sorted(suites)))
print(f'protected: {len(suites)} test binaries: {" ".join(sorted(suites))}')
PY
mapfile -t goport_args < "$NEW/logs/args-ts_goport"
mapfile -t crate_args < "$NEW/logs/args-crates"
((${#goport_args[@]})) || fail 4 "no ts_goport tests in the plan"
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
cargo_test "${goport_args[@]}" > "$NEW/logs/build-ts_goport.json" 2> "$NEW/logs/build-ts_goport.log" ||
  fail 5 "ts_goport test build failed; see $NEW/logs/build-ts_goport.log"
echo "$(date -u +%FT%TZ) ts_goport tests built"
: > "$NEW/logs/build-crates.json"
if ((${#crate_args[@]})); then
  cargo_test "${crate_args[@]}" > "$NEW/logs/build-crates.json" 2> "$NEW/logs/build-crates.log" ||
    fail 5 "crate test build failed; see $NEW/logs/build-crates.log"
  echo "$(date -u +%FT%TZ) crate tests built"
fi

# Copy each test executable (profile.test) under its suite name, and each ts_goport bin to relbin/.
# SUITES gets the crate dir of each test executable. Every planned suite must have one.
python3 - "$NEW" "$CO" "$NEW/logs/build-ts_goport.json" "$NEW/logs/build-crates.json" << 'PY' || fail 6 "copy failed"
import json, os, shutil, sys
LIB_KINDS = {'lib', 'rlib', 'dylib', 'cdylib', 'staticlib', 'proc-macro'}
new, co, logs = sys.argv[1], sys.argv[2], sys.argv[3:]
seen, crate_dir = {}, {}
for path in logs:
    for line in open(path):
        if not line.startswith('{'):
            continue
        m = json.loads(line)
        if m.get('reason') != 'compiler-artifact' or not m.get('executable'):
            continue
        kind = m['target']['kind']
        if m['profile']['test']:
            name = m['target']['name'] + ('_lib' if set(kind) & LIB_KINDS else '')
            dest = os.path.join(new, name)
            crate_dir[name] = os.path.relpath(os.path.dirname(m['manifest_path']), co)
        elif kind == ['bin'] and m['manifest_path'].endswith('/crates/ts_goport/Cargo.toml'):
            dest = os.path.join(new, 'relbin', m['target']['name'])
        else:
            continue
        if seen.get(dest, m['executable']) != m['executable']:
            sys.exit(f'two executables for {dest}: {seen[dest]} and {m["executable"]}')
        seen[dest] = m['executable']
planned = open(os.path.join(new, 'logs', 'planned')).read().split()
missing = [s for s in planned if s not in crate_dir]
if missing:
    sys.exit(f'no test binary for {" ".join(missing)}')
for dest, src in sorted(seen.items()):
    shutil.copy2(src, dest)
    print(f'{os.path.relpath(dest, new)} <- {src}')
with open(os.path.join(new, 'SUITES'), 'w') as f:
    f.writelines(f'{name}\t{d}\n' for name, d in sorted(crate_dir.items()))
PY
exec 8>&-

[[ $(build_inputs) == "$before" ]] || fail 7 "the build inputs of $CO changed during the build; $NEW is not kept"
[[ -x $NEW/relbin/tsgo && -x $NEW/relbin/goport ]] || fail 8 "no relbin/tsgo or relbin/goport"

echo "$commit" > "$NEW/COMMIT"
echo "$tree" > "$NEW/TREE"
echo "$CO" > "$NEW/BUILD_ROOT"
echo "$TARGET" > "$NEW/BUILD_TARGET"
(cd "$CO" && rustc --version) > "$NEW/TOOLCHAIN"
(cd "$NEW" && { find . -maxdepth 2 -type f -perm -u+x | sed 's|^\./||'; echo SUITES; } | sort | xargs sha256sum > bins.sha256)
mv "$NEW" "$TB" || fail 9 "cannot move $NEW to $TB"
echo "$(date -u +%FT%TZ) $TB: $(wc -l < "$TB/SUITES") test binaries, $(grep -c ' relbin/' "$TB/bins.sha256") release bins"
echo DONE
exit 0
}
