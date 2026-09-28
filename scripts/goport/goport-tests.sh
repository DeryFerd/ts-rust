#!/usr/bin/env bash
# Runs every protected goport test suite from prebuilt test binaries and writes per-name results.
#
# usage: scripts/goport/goport-tests.sh <testbin-dir> <out-dir> [--pin PIN]
#
# <testbin-dir> is a dir from build-goport-tests.sh: the test binaries, relbin/, COMMIT, BUILD_ROOT,
# BUILD_TARGET and bins.sha256 (checked first). PIN (default: GOPORT_PIN, else the saved state's
# batch.upstreamPin.to, else UPSTREAM.json current) selects the Go checkout (TS_GO_REPO) and runs every
# binary under `pin.py exec`. One test thread (RUST_TEST_THREADS=1) everywhere, as the project runs them.
#
# The test binaries have their build paths compiled in (fixtures under BUILD_ROOT/crates/ts_goport,
# release bins under BUILD_TARGET/release). So each binary runs in a bwrap that binds a git archive of
# COMMIT's crates/ over BUILD_ROOT/crates and relbin/ over BUILD_TARGET/release. The checkout and the
# shared target do not change the run, and the run does not change them.
#
# Suites (results.json "suites" keys), in run order:
#   lib_snapshot                  ts_goport_lib snapshot_matches_live (the 2 lib snapshot tests, first)
#   ts_goport_lib, goport_util_lib, goport_lsproto_lib
#   go_baselines                  the default set (TestLocal, units, tsctests, project_lsp, ...)
#   go_baselines_local            TestLocal subtests, "<kind> <key>" (COMPILER_RUNNER_RESULTS rows)
#   go_baselines_transpile        TestTranspile subtests, "<kind> <key>" (TRANSPILE_RUNNER_RESULTS rows;
#                                 only when go_baselines has compiler_runner::test_transpile, from bump B)
#   go_baselines_submodule_shards TestSubmodule in 4 shards (COMPILER_RUNNER_JOBS=8), "<test> <i>/4"
#   go_baselines_submodule        TestSubmodule subtests, "<kind> <key>"
#   go_baselines_reference        each Go reference baseline file (testdata/baselines/reference,
#                                 without .diff): ok = compared and its subtest passed, failed =
#                                 compared and its subtest failed, ignored = not compared or skipped
#   multi_program, emit_pool, early_emit, fswatch_linux
#   ts_scanner_lib, ts_ast_lib, ts_diagnostics_lib, ts_path_lib, ts_core_lib, ts_jsnum_lib
# A test binary that the dir lacks is skipped, and its suite is missing from results.json.
#
# Output in <out-dir> (it must not have results.json or logs/):
#   results.json  {"source": {"commit", "tree", "testbinSha256"}, "pin",
#                  "suites": {"<suite>": {"<test name>": "ok" | "failed" | "ignored" | "unrun"}},
#                  "incomplete": ["<suite>", ...]}
#                 tree is COMMIT's crates tree, testbinSha256 the sha256 of bins.sha256. "unrun" is a
#                 name that `--list` shows but that has no result (a crash or a timeout). A suite is
#                 incomplete when a binary of it ended without all its results.
#   logs/         <suite>.log (stdout and stderr, then exit=<rc>), <suite>.list (--list),
#                 <suite>.results (libtest --logfile)
#   *.tsv         the compiler runner results (COMPILER_RUNNER_RESULTS, TRANSPILE_RUNNER_RESULTS) of
#                 TestLocal, TestTranspile and each TestSubmodule shard
# Last stdout line: DONE (every suite ran and results.json is written; test failures are in
# results.json) or FAIL rc=<N>. Compare two results with compare-tests.py.
set -uo pipefail

# One brace group: bash reads the whole script before it runs it, so an edit of this file does not
# change a running check.
{
fail() { echo "goport-tests.sh: $2" >&2; echo "FAIL rc=$1"; exit "$1"; }
usage() { sed -n '2,/^set -uo/p' "$0" | sed '$d'; echo "FAIL rc=2"; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
ROOT=$(dirname "$(git -C "$here" rev-parse --path-format=absolute --git-common-dir)")

pin=${GOPORT_PIN:-}
args=()
while (($#)); do
  case $1 in
  --pin) (($# >= 2)) || usage; pin=$2; shift 2 ;;
  -h | --help) usage ;;
  *) args+=("$1"); shift ;;
  esac
done
((${#args[@]} == 2)) || usage
[[ -n $pin ]] || pin=$(jq -r '.batch.upstreamPin.to // empty' "$ROOT/docs/typechecker-state/current.json" 2> /dev/null)
[[ -n $pin ]] || pin=$(jq -r .current "$ROOT/UPSTREAM.json")
TB=$(realpath -- "${args[0]}") || fail 2 "no test bin dir ${args[0]}"
O=$(realpath -m -- "${args[1]}")
[[ ! -e $O/results.json && ! -e $O/logs ]] || fail 2 "$O has results.json or logs/ (results are never replaced)"

for f in COMMIT BUILD_ROOT BUILD_TARGET bins.sha256; do [[ -s $TB/$f ]] || fail 3 "$TB has no $f"; done
(cd "$TB" && sha256sum -c --quiet bins.sha256) || fail 3 "$TB/bins.sha256 does not match"
COMMIT=$(cat "$TB/COMMIT") BUILD_ROOT=$(cat "$TB/BUILD_ROOT") BUILD_TARGET=$(cat "$TB/BUILD_TARGET")
tree=$(git -C "$ROOT" rev-parse --verify --quiet "$COMMIT:crates") || fail 3 "no commit $COMMIT"
[[ -d $BUILD_ROOT/crates && -d $BUILD_TARGET/release && -d $TB/relbin ]] ||
  fail 3 "missing bind path: $BUILD_ROOT/crates, $BUILD_TARGET/release or $TB/relbin"
GO=$(python3 "$ROOT/scripts/upstream/pin.py" path goCheckout "$pin") || fail 3 "unknown pin $pin"
[[ -d $GO/testdata/baselines/reference ]] || fail 3 "no Go checkout at $GO"

mkdir -p "$O/logs" "$O/tmp" || fail 4 "cannot make $O"
rm -rf "$O/src" && mkdir -p "$O/src" || fail 4 "cannot make $O/src"
git -C "$ROOT" archive "$COMMIT" crates | tar -x -C "$O/src" || fail 4 "git archive of $COMMIT failed"

# A clean environment: no goport, compiler runner or test harness settings of the caller.
while IFS= read -r v; do unset "$v"; done < <(compgen -e | grep -E '^(GOPORT_|COMPILER_RUNNER_|TRANSPILE_RUNNER_|TS_TEST_|RUST_TEST_)')
export GOPORT_PIN=$pin TS_GO_REPO=$GO RUST_TEST_THREADS=1 CARGO_MANIFEST_DIR=$BUILD_ROOT/crates/ts_goport
cap=(systemd-run --user --scope --quiet --collect -p MemoryMax=24000000K -p MemorySwapMax=0 nice -n 10)
pinwrap=(python3 "$ROOT/scripts/upstream/pin.py" exec --)
state() { echo "$1 $(date -u +%FT%TZ) Go $(git -C "$GO" rev-parse --short=12 HEAD) Go-dirty $(git -C "$GO" status --porcelain | wc -l) load $(cut -d' ' -f1-3 /proc/loadavg)"; }

# suite <name> <binary> <crate dir> <timeout s> [test args...]: lists, then runs one test binary.
# The caller sets extra environment on the call.
suite() {
  local name=$1 bin=$TB/$2 dir=$BUILD_ROOT/crates/$3 secs=$4 rc
  shift 4
  if [[ ! -x $bin ]]; then echo "skip $name: no binary $bin"; return; fi
  local box=(bwrap --dev-bind / / --bind "$O/src/crates" "$BUILD_ROOT/crates"
    --ro-bind "$TB/relbin" "$BUILD_TARGET/release" --chdir "$dir" --)
  rm -f "$O/logs/$name.results"
  "${cap[@]}" "${pinwrap[@]}" "${box[@]}" "$bin" "$@" --list > "$O/logs/$name.list" 2>&1
  timeout "$secs" "${cap[@]}" "${pinwrap[@]}" "${box[@]}" "$bin" "$@" --logfile "$O/logs/$name.results" \
    > "$O/logs/$name.log" 2>&1
  rc=$?
  echo "exit=$rc" >> "$O/logs/$name.log"
  echo "$name exit=$rc $(grep -m1 '^test result:' "$O/logs/$name.log") $(date -u +%FT%TZ)"
}

echo "== goport tests: $TB (${COMMIT:0:9}, crates tree ${tree:0:12}), pin $pin, Go $GO, out $O"
state before
suite lib_snapshot ts_goport_lib ts_goport 1200 snapshot_matches_live
suite ts_goport_lib ts_goport_lib ts_goport 1800
suite goport_util_lib goport_util_lib ts_goport 1200
suite goport_lsproto_lib goport_lsproto_lib ts_goport 1200
mkdir -p "$O/tmp/local"
COMPILER_RUNNER_TMP=$O/tmp/local COMPILER_RUNNER_RESULTS=$O/go_baselines_local.tsv \
  TRANSPILE_RUNNER_RESULTS=$O/go_baselines_transpile.tsv suite go_baselines go_baselines ts_goport 3600
for i in 0 1 2 3; do
  mkdir -p "$O/tmp/sub$i"
  COMPILER_RUNNER_TMP=$O/tmp/sub$i COMPILER_RUNNER_SHARD=$i/4 COMPILER_RUNNER_JOBS=8 \
    COMPILER_RUNNER_RESULTS=$O/go_baselines_submodule-$i.tsv \
    suite "go_baselines_submodule-$i" go_baselines ts_goport 3600 --exact compiler_runner::test_submodule --include-ignored
done
for t in multi_program emit_pool early_emit fswatch_linux; do suite "$t" "$t" ts_goport 1200; done
for c in ts_scanner ts_ast ts_diagnostics ts_path ts_core ts_jsnum; do
  if [[ -d $O/src/crates/$c ]]; then suite "${c}_lib" "${c}_lib" "$c" 600; else echo "skip ${c}_lib: no crates/$c"; fi
done
state after

# results.json from the --list, --logfile and compiler runner files.
python3 - "$O" "$TB" "$COMMIT" "$tree" "$pin" "$GO/testdata/baselines/reference" << 'PY' || fail 5 "results.json not written"
import hashlib, json, os, sys
out, tb, commit, tree, pin, ref_root = sys.argv[1:]
logs = os.path.join(out, 'logs')
LIBTEST = {'ok': 'ok', 'failed': 'failed', 'ignored': 'ignored'}
RUNNER = {'pass': 'ok', 'fail': 'failed', 'skip': 'ignored'}
WORST = ['ok', 'ignored', 'failed']
suites, incomplete = {}, set()

def libtest(name):
    """{test name: status} of one run, and whether every listed name has a result."""
    listed = [l[:-len(': test')] for l in open(os.path.join(logs, name + '.list'), errors='replace').read().splitlines()
              if l.endswith(': test')]
    res_path = os.path.join(logs, name + '.results')
    got = {}
    if os.path.exists(res_path):
        # "ok <name>", "failed <name>", "ignored <name>" or "ignored: <reason> <name>". Test names
        # have no spaces, so the name is the last word.
        for l in open(res_path, errors='replace').read().splitlines():
            words = l.split()
            if len(words) >= 2 and words[0].rstrip(':') in LIBTEST:
                got[words[-1]] = LIBTEST[words[0].rstrip(':')]
    names = {n: got.get(n, 'unrun') for n in listed}
    names.update(got)
    return names, bool(listed) and all(n in got for n in listed)

def ran(name):
    return os.path.exists(os.path.join(logs, name + '.list'))

for name in ['lib_snapshot', 'ts_goport_lib', 'goport_util_lib', 'goport_lsproto_lib', 'go_baselines',
             'multi_program', 'emit_pool', 'early_emit', 'fswatch_linux'] + \
            [c + '_lib' for c in ('ts_scanner', 'ts_ast', 'ts_diagnostics', 'ts_path', 'ts_core', 'ts_jsnum')]:
    if ran(name):
        suites[name], complete = libtest(name)
        if not complete:
            incomplete.add(name)

def runner_rows(paths, subtests, compared):
    """Reads compiler runner results files into subtests {"<kind> <key>": status} and compared paths."""
    dups = 0
    for path in paths:
        if not os.path.exists(path):
            continue
        for line in open(path, encoding='utf-8', errors='surrogateescape'):
            f = line.rstrip('\n').split('\t')
            if f[0] == 'baseline' and len(f) >= 2:
                compared.add(f[1])
            elif f[0] in RUNNER and len(f) >= 3:
                n, st = f'{f[1]} {f[2]}', RUNNER[f[0]]
                if n in subtests:
                    dups += 1
                    st = max(st, subtests[n], key=WORST.index)
                subtests[n] = st
    return dups

compared = set()
status_of_parent = lambda suite, test: suites.get(suite, {}).get(test)
if ran('go_baselines'):
    local = {}
    dups = runner_rows([os.path.join(out, 'go_baselines_local.tsv')], local, compared)
    suites['go_baselines_local'] = local
    if status_of_parent('go_baselines', 'compiler_runner::test_local') not in ('ok', 'failed'):
        incomplete.add('go_baselines_local')
    if dups:
        print(f'go_baselines_local: {dups} repeated subtests (the worst status is kept)')
    parent = status_of_parent('go_baselines', 'compiler_runner::test_transpile')
    if parent is not None:
        transpile = {}
        dups = runner_rows([os.path.join(out, 'go_baselines_transpile.tsv')], transpile, set())
        suites['go_baselines_transpile'] = transpile
        if parent not in ('ok', 'failed'):
            incomplete.add('go_baselines_transpile')
        if dups:
            print(f'go_baselines_transpile: {dups} repeated subtests (the worst status is kept)')
shards = [i for i in range(4) if ran(f'go_baselines_submodule-{i}')]
if shards:
    sub, shard_suite = {}, {}
    dups = runner_rows([os.path.join(out, f'go_baselines_submodule-{i}.tsv') for i in shards], sub, compared)
    for i in shards:
        names, complete = libtest(f'go_baselines_submodule-{i}')
        for test, st in names.items():
            shard_suite[f'{test} {i}/4'] = st
        if not complete or names.get('compiler_runner::test_submodule') not in ('ok', 'failed'):
            incomplete.update(['go_baselines_submodule_shards', 'go_baselines_submodule'])
    if len(shards) < 4:
        incomplete.update(['go_baselines_submodule_shards', 'go_baselines_submodule'])
    suites['go_baselines_submodule_shards'] = shard_suite
    suites['go_baselines_submodule'] = sub
    if dups:
        print(f'go_baselines_submodule: {dups} repeated subtests (the worst status is kept)')

# Reference files, as upstream/bumpB/wave3/r1/tools/coverage.py: a reference file (without .diff) is
# matched when its subtest passed, differs when it failed, and not compared when no run compared it.
KIND_OF_EXT = {'.errors.txt': 'error', '.js': 'output', '.js.map': 'sourcemap', '.sourcemap.txt': 'sourcemaprecord',
               '.types': 'types', '.symbols': 'symbols', '.trace.json': 'moduleresolution',
               '.contentmapper': 'contentmapper'}
EXTS = sorted(KIND_OF_EXT, key=len, reverse=True)
if 'go_baselines_local' in suites or 'go_baselines_submodule' in suites:
    by_stem = {}
    for s in ('go_baselines_local', 'go_baselines_submodule'):
        for n, st in suites.get(s, {}).items():
            kind, key = n.split(' ', 1)
            if key.count('/') < 2:
                continue
            where, suite, cname = key.split('/', 2)
            for ext in ('.tsx', '.ts'):
                if cname.endswith(ext):
                    cname = cname[:-len(ext)]
                    break
            by_stem[(('submodule/' if where == 'submodule' else '') + f'{suite}/{cname}', kind)] = st
    ref, unknown = {}, 0
    for top in ('compiler', 'conformance', 'submodule/compiler', 'submodule/conformance'):
        d = os.path.join(ref_root, top)
        for f in sorted(os.listdir(d)) if os.path.isdir(d) else []:
            if f.endswith('.diff'):
                continue
            rel = f'{top}/{f}'
            ext = next((e for e in EXTS if f.endswith(e)), None)
            if ext is None:
                unknown += 1
                continue
            st = by_stem.get((rel[:-len(ext)], KIND_OF_EXT[ext])) if rel in compared else None
            ref[rel] = st if st in ('ok', 'failed') else 'ignored'
    suites['go_baselines_reference'] = ref
    if {'go_baselines_local', 'go_baselines_submodule'} & incomplete or \
            not {'go_baselines_local', 'go_baselines_submodule'} <= suites.keys():
        incomplete.add('go_baselines_reference')
    if unknown:
        print(f'go_baselines_reference: {unknown} reference files of no known kind are not listed')

sha = hashlib.sha256(open(os.path.join(tb, 'bins.sha256'), 'rb').read()).hexdigest()
doc = {'source': {'commit': commit, 'tree': tree, 'testbinSha256': sha}, 'pin': pin,
       'suites': {s: dict(sorted(n.items())) for s, n in sorted(suites.items())},
       'incomplete': sorted(incomplete)}
tmp = os.path.join(out, 'results.json.tmp')
with open(tmp, 'w', encoding='utf-8', errors='surrogateescape') as f:
    json.dump(doc, f, indent=1, ensure_ascii=False)
    f.write('\n')
os.replace(tmp, os.path.join(out, 'results.json'))
for s, n in doc['suites'].items():
    c = {k: sum(v == k for v in n.values()) for k in ('ok', 'failed', 'ignored', 'unrun')}
    print(f'{s}: {len(n)} names, ' + ', '.join(f'{k} {v}' for k, v in c.items() if v or k == 'ok'))
print(f'incomplete: {", ".join(doc["incomplete"]) or "none"}')
PY
rm -rf "$O/src" "$O/tmp"
echo "results $O/results.json sha256 $(sha256sum < "$O/results.json" | cut -c1-64)"
echo DONE
exit 0
}
