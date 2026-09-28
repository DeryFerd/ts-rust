#!/usr/bin/env bash
# Regression gate for goport. Perf and compat work must pass it before any merge.
#
# usage: gate.sh <label> [--bins DIR] [--quick|--full] [--commit SHA]
#   --bins DIR    dir with goport, goport_emit, goport_typesyms, goport_build and tsgo
#                 (default: runtime/cargo-target/release; build them with --release, not
#                 the fat-LTO goport profile: output is the same and the build is much faster)
#   --quick       project checks only (default is --full)
#   --full        also 1,500-case diagnostic and emit corpus samples and effect typesyms
#   --commit SHA  commit the binaries were built from (else read DIR/COMMIT, else "unknown")
#
# Stages (serial, one gate run at a time through /tmp/goport-gate.lock):
#   measure, measure-extra, sweep, sweep-extra2, sweep-hono-runtime   (existing scripts)
#   sweep-wide    (--full) 292 configs of 51 more real projects (sweep-wide.sh)
#   f1            sample-f1/run-f1.py (R104 conformance sample)
#   emit          emit/compare-emit.sh
#   typesyms      Go vs Rust dumps for query and hono (+ effect in --full)
#   build         build-mode/compare-build.sh seq <repo> cold edits flags foreign, repro and query-chain
#   determinism   goport 3x on zod, effect, elysia: runs must be equal and equal to the oracle
#   editor        ls_edit_bench.py on Query core and Hono (typing-paced, errfix-paced, imports, long)
#                 against Go in the same run. RSS, growth and answers limits are judged; latency is
#                 reported only, because load changes it. Holds /tmp/goport-lsguard.lock.
#   corpus-diag   (--full) corpus-p5 1,500-case shard through corpus-full/run_shard_parallel.py
#   corpus-emit   (--full) emit-corpus/run_emit_shard2.py shard 0 + shard 1 --limit 502
#
# Output: target/continuation-r97-goport/compat/gate/<label>/ (never reused). It holds
# runs/, logs/, items/ and manifest.json (binary hashes, commit, every result).
# Exit 0 only when every result is MATCH, or ALLOWED by gate-allow.txt (next to this script).
# An allow entry only applies when its condition verifies again in this run.
# Project inputs and the existing scripts and oracle caches are only read.
set -uo pipefail
# GOPORT_PIN=<key> runs this against that upstream pin (scripts/upstream/pin.py). Unset: no change.
[[ -z ${GOPORT_PIN:-} || -n ${GOPORT_PIN_ACTIVE:-} ]] || exec python3 /home/theo/Code/sandbox/ts-rust/scripts/upstream/pin.py exec -- bash "$0" "$@"

REPO=/home/theo/Code/sandbox/ts-rust
R=$REPO/target/continuation-r97-goport
TP=$R/tools-port
X=$REPO/target/project-inputs-extra
HERE=$(cd "$(dirname "$0")" && pwd)
SELF=$HERE/$(basename "$0")
ALLOW=$HERE/gate-allow.txt

usage() { sed -n '2,28p' "$SELF"; exit 2; }
LABEL=${1:-}; [[ -n $LABEL && $LABEL != -* ]] || usage; shift
[[ $LABEL =~ ^[A-Za-z0-9._-]+$ ]] || { echo "label must match [A-Za-z0-9._-]+" >&2; exit 2; }
BINS=$R/runtime/cargo-target/release; MODE=full; COMMIT=
while [[ $# -gt 0 ]]; do
  case $1 in
    --bins) BINS=$2; shift 2 ;;
    --quick) MODE=quick; shift ;;
    --full) MODE=full; shift ;;
    --commit) COMMIT=$2; shift 2 ;;
    *) usage ;;
  esac
done
BINS=$(realpath "$BINS")
for b in goport goport_emit goport_typesyms goport_build tsgo; do
  [[ -x $BINS/$b ]] || { echo "missing binary $BINS/$b" >&2; exit 2; }
done
[[ -f $ALLOW ]] || { echo "missing allow-list $ALLOW" >&2; exit 2; }
if [[ -z $COMMIT && -f $BINS/COMMIT ]]; then COMMIT=$(tr -d '[:space:]' < "$BINS/COMMIT"); fi
COMMIT_FULL=unknown
if [[ -n $COMMIT ]]; then
  COMMIT_FULL=$(git -C "$REPO" rev-parse --verify --quiet "$COMMIT^{commit}") || { echo "unknown commit $COMMIT" >&2; exit 2; }
else
  echo "warning: no --commit and no $BINS/COMMIT; manifest records commit unknown" >&2
fi

# Cached oracle outputs must exist, or the sweep scripts would write new ones.
for n in query-core-tests query-core-legacy hono-spec hono-full ts-pattern-tests svelte svelte-runtime effect \
         pathe ufo tiny-invariant rhf-app hono-rt-bun hono-rt-fastly hono-rt-lambda hono-rt-lambda-edge \
         hono-rt-node hono-rt-workerd hono-perf-scripts; do
  [[ -f $R/oracle-sweep/$n.txt ]] || { echo "missing cached oracle $R/oracle-sweep/$n.txt" >&2; exit 2; }
done

exec 9> /tmp/goport-gate.lock
flock -n 9 || { echo "another gate run holds /tmp/goport-gate.lock; waiting"; flock 9; }

OUT=$R/compat/gate/$LABEL
[[ -e $OUT ]] && { echo "$OUT exists; use a new label" >&2; exit 2; }
mkdir -p "$OUT"/{runs,logs,items}
STARTED=$(date -u +%FT%TZ)
export GOPORT_BIN=$BINS/goport

# Python helper: parses logs into items, runs the Python stages, applies the allow-list,
# writes manifest.json and prints the summary. Called as: py <command> args...
read -r -d '' PY <<'PYEOF'
import fnmatch, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path
import psutil

REPO = Path('/home/theo/Code/sandbox/ts-rust')
R = REPO / 'target/continuation-r97-goport'
X = REPO / 'target/project-inputs-extra'
ORACLE = Path.home() / '.local/bin/tsgo-oracle'
GO_DUMPER = R / 'typesyms/typesymdump-go'
RSS_LIMIT = 40 * 2**30


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_items(path, items, expected):
    with open(path, 'w') as f:
        for item in items:
            f.write(json.dumps(item) + '\n')
    Path(str(path).replace('.jsonl', '.expected')).write_text(str(expected))


def item(stage, name, ok, detail='', **ctx):
    row = {'stage': stage, 'id': f'{stage}/{name}', 'status': 'MATCH' if ok else 'FAIL', 'detail': detail}
    if ctx:
        row['ctx'] = ctx
    return row


def err_clean(path):
    """True when a goport stderr file has no panic and no unported line."""
    if not Path(path).exists():
        return True
    text = Path(path).read_text(errors='replace')
    return 'panicked at' not in text and not any(l.startswith('unported') for l in text.splitlines())


# ---- log parsers for the existing bash scripts ----

SWEEP = re.compile(r'^(\S+) exit=(\S+) diags=(\d+) oracle=(\d+) (\S+) ')


def parse_sweep(stage, log, runs):
    items = []
    for line in Path(log).read_text(errors='replace').splitlines():
        m = SWEEP.match(line)
        if not m:
            continue
        panics = re.search(r'panics=(\d+)', line)
        unported = re.search(r'unported=(\d+)', line)
        ok = (m[5] == 'MATCH' and (not panics or panics[1] == '0') and (not unported or unported[1] == '0')
              and err_clean(Path(runs) / f'{m[1]}.err'))
        items.append(item(stage, m[1], ok, line.strip()))
    return items


def parse_measure(stage, log, runs):
    items = []
    for line in Path(log).read_text(errors='replace').splitlines():
        m = re.match(r'^(query|hono) exit=(\S+) ', line)
        if m:
            out = Path(runs) / f'{m[1]}.out'
            ok = (out.exists() and out.read_bytes() == (R / 'oracle' / f'{m[1]}.txt').read_bytes()
                  and m[2] in ('0', '1') and err_clean(Path(runs) / f'{m[1]}.err'))
            items.append(item(stage, m[1], ok, line.strip() + ('' if ok else ' (vs oracle/%s.txt)' % m[1])))
        m = re.match(r'^([QH]-E\d+) (MATCH|DIFF)', line)
        if m:
            ok = m[2] == 'MATCH' and err_clean(Path(runs) / f'{m[1]}.err')
            items.append(item(stage, m[1], ok, line.strip()))
    return items


EMIT = re.compile(r'^(\S+) (MATCH|DIFF) oracle=(\d+) goport=(\d+) differ=(\d+) only=(\d+) rc=(\S+) oracle_rc=(\S+) \S+ panics=(\d+) unported=(\d+)')


def parse_emit(stage, log, runs):
    items = []
    for line in Path(log).read_text(errors='replace').splitlines():
        m = EMIT.match(line)
        if m:
            ok = m[2] == 'MATCH' and m[7] == m[8] and m[9] == '0' and m[10] == '0'
            items.append(item(stage, m[1], ok, line.strip()))
        elif ' WROTE-INTO-PROJECT' in line:
            items.append(item(stage, line.split()[0] + '/wrote-into-project', False, line.strip()[:300]))
    return items


def parse_build(stage, log, runs):
    items = []
    for line in Path(log).read_text(errors='replace').splitlines():
        m = re.match(r'^(repro|query-chain) (\S+) (MATCH|DIFF)', line)
        if m:
            items.append(item(stage, f'{m[1]}/{m[2]}', m[3] == 'MATCH', line.strip()))
    return items


# Editor limits the gate judges. Latency limits depend on host load, so they are only reported.
EDITOR_LIMITS = ('rss', 'growth', 'answers')


def cmd_editor(result_json, items_file, expected):
    sessions = json.loads(Path(result_json).read_text())['sessions'] if Path(result_json).exists() else []
    items = []
    for s in sessions:
        name = f"{s['project']}/{s['scenario']}"
        rec = s['rust'].get('cand')
        if s['go']['error'] or not rec:
            items.append(item('editor', name, False, f"Go session failed: {s['go']['error']}" if s['go']['error'] else 'no Rust session'))
            continue
        bad = [f'{k} {t}' for k, (ok, t) in rec['limits'].items() if k in EDITOR_LIMITS and not ok]
        slow = [f'{k} {t}' for k, (ok, t) in rec['limits'].items() if k not in EDITOR_LIMITS and not ok]
        detail = '; '.join(bad) or 'memory and answers within limits'
        items.append(item('editor', name, not bad, detail + (f" (latency, not judged: {'; '.join(slow)})" if slow else '')))
    write_items(items_file, items, int(expected))


PARSERS = {'measure': parse_measure, 'measure-extra': parse_sweep, 'sweep': parse_sweep, 'sweep-extra2': parse_sweep, 'sweep-wide': parse_sweep,
           'sweep-hono-runtime': parse_sweep, 'emit': parse_emit, 'build': parse_build}


def cmd_parse(stage, log, runs, items_file, expected):
    write_items(items_file, PARSERS[stage](stage, log, runs), int(expected))


# ---- Python stages ----

def cmd_f1(summary, items_file):
    rows = json.loads(Path(summary).read_text())['rows']
    items = [item('f1', f"{r['id']}", r['class'] == 'MATCH', f"{r['class']} {r['case']}") for r in rows if r['class'] != 'SKIPPED']
    listing = json.loads((REPO / 'target/continuation-r104-conformance-sample/list.json').read_text())
    write_items(items_file, items, sum(c['status'] == 'GENERATED' for c in listing['cases']))


def run_watched(command, cwd, stdout, timeout=1800):
    """Runs command; kills it over 40 GB RSS or the timeout. Returns (exit or reason, seconds, peak MiB)."""
    start, peak, killed = time.time(), 0, None
    proc = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    ps = psutil.Process(proc.pid)
    while proc.poll() is None:
        try:
            rss = sum(p.memory_info().rss for p in [ps] + ps.children(recursive=True))
        except psutil.Error:
            rss = 0
        peak = max(peak, rss)
        if rss > RSS_LIMIT:
            killed = 'killed-rss-over-40GB'
        elif time.time() - start > timeout:
            killed = 'timeout'
        if killed:
            proc.kill()
            proc.wait()
            break
        time.sleep(0.25)
    return killed or proc.returncode, round(time.time() - start, 2), peak >> 20


def load_compare_int():
    import importlib.util
    spec = importlib.util.spec_from_file_location('compare_int', R / 'typesyms/compare-int.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


TYPESYMS = {
    'query': (REPO / 'target/project-inputs/query/source/packages/query-core', 'tsconfig.prod.json'),
    'hono': (REPO / 'target/project-inputs/hono/source', 'tsconfig.build.json'),
    'effect': (REPO / 'target/project-inputs/effect/source/packages/effect', 'tsconfig.json'),
}


def cmd_typesyms(rs_bin, out_dir, items_file, *names):
    ci = load_compare_int()
    items = []
    for name in names:
        cwd, cfg = TYPESYMS[name]
        base = Path(out_dir) / name
        runs = {}
        # One dumper at a time: the Go effect dump is large.
        for side, binary in (('go', GO_DUMPER), ('rs', Path(rs_bin))):
            (base / side).mkdir(parents=True)
            with open(base / f'{side}.stderr', 'wb') as log:
                runs[side] = run_watched([str(binary), '-p', cfg, '-o', str(base / side)], cwd, log)
            print(name, side, 'exit/seconds/peakMiB', runs[side], flush=True)
        files, lines, missing, extra = ci.compare(base / 'go', base / 'rs')
        ok = runs['go'][0] == 0 and runs['rs'][0] == 0 and not files and not missing and not extra
        detail = (f"go={runs['go']} rs={runs['rs']} files={len(list((base / 'go').iterdir()))} "
                  f"diffFiles={len(files)} diffLines={lines} missing={len(missing)} extra={len(extra)}")
        print(name, detail, flush=True)
        items.append(item('typesyms', name, ok, detail, goDir=str(base / 'go'), rsDir=str(base / 'rs'),
                          exits=[runs['go'][0], runs['rs'][0]], diffFiles=[f for f, _ in files],
                          missing=missing, extra=extra, peakMiB={'go': runs['go'][2], 'rs': runs['rs'][2]}))
    write_items(items_file, items, len(names))


DETERMINISM = [
    ('zod', REPO, 'target/project-inputs/zod/source/packages/zod/tsconfig.json', R / 'oracle/zod.txt'),
    ('effect', REPO, 'target/project-inputs/effect/source/packages/effect/tsconfig.json', R / 'oracle-sweep/effect.txt'),
    ('elysia', X / 'elysia/src', 'tsconfig.json', X / 'elysia/oracle.txt'),
]


def cmd_determinism(goport, out_dir, items_file):
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True)
    items = []
    for name, cwd, cfg, oracle in DETERMINISM:
        outs, exits, clean = [], [], True
        for i in (1, 2, 3):
            o, e = out_dir / f'{name}-{i}.out', out_dir / f'{name}-{i}.err'
            with o.open('xb') as so, e.open('xb') as se:
                try:
                    exits.append(subprocess.run([goport, '-p', cfg], cwd=cwd, stdout=so, stderr=se, timeout=900).returncode)
                except subprocess.TimeoutExpired:
                    exits.append('timeout')
            outs.append(o.read_bytes())
            clean = clean and err_clean(e)
        same = len(set(outs)) == 1 and len(set(map(str, exits))) == 1
        equal_oracle = outs[0] == oracle.read_bytes()
        detail = (f"runs-identical={same} equal-oracle={equal_oracle} exits={exits} "
                  f"md5={hashlib.md5(outs[0]).hexdigest()[:8]} diags={outs[0].count(b'error TS')}")
        print(name, detail, flush=True)
        items.append(item('determinism', name, same and equal_oracle and clean and exits[0] in (0, 1), detail))
    write_items(items_file, items, len(DETERMINISM))


def cmd_corpus_diag(goport, commit, work, items_file):
    work = Path(work).resolve()
    work.mkdir(parents=True)
    # Same shard and runner as corpus-p5/run_p5.py (cases from corpus-full, 1,500-case shard from corpus-int3).
    for name, target in (('cases', R / 'corpus-full/cases'), ('list.json', R / 'corpus-full/list.json'),
                         ('shards', R / 'corpus-int3/shards')):
        (work / name).symlink_to(target)
    sys.path.insert(0, str(R / 'corpus-full'))
    import run_shard as rs
    import run_shard_parallel as rp
    rs.here, rs.GOPORT, rs.GOPORT_COMMIT = work, Path(goport), commit
    if os.environ.get('GOPORT_PIN_ACTIVE'):  # pin run: the runner asserts the pin oracle's hash
        rs.ORACLE_SHA256 = os.environ['GOPORT_PIN_ORACLE_SHA256']
    sys.argv = ['run_shard_parallel.py', '0', '--jobs', '8', '--results', str(work / 'results')]
    rp.main()
    result = json.loads((work / 'results/shard-0-result.json').read_text())
    shard = {c['id']: c for c in json.loads((work / 'shards/shard-0.json').read_text())['cases']}
    items = [item('corpus-diag', r['id'], r['class'] == 'MATCH', f"{r['class']} {r['source']}",
                  cwd=str(R / 'corpus-full/cases' / r['id']), tsconfig=shard[r['id']]['tsconfig'],
                  goportOut=str(work / 'results' / f"{r['id']}.goport.out")) for r in result['rows']]
    write_items(items_file, items, len(shard))


def cmd_corpus_emit(goport_emit, commit, work, items_file):
    work = Path(work).resolve()
    work.mkdir(parents=True)
    sys.path.insert(0, str(R / 'emit-corpus'))
    import run_emit_shard2 as es
    es.here = work  # results must stay under here; CORPUS already points at corpus-full.
    if os.environ.get('GOPORT_PIN_ACTIVE'):  # pin run: the runner asserts the pin oracle's hash
        es.ORACLE_SHA256 = os.environ['GOPORT_PIN_ORACLE_SHA256']
    items, expected = [], 0
    # Same 1,500 cases as emit-corpus results-int3/int4: shard 0 (998) + first 502 of shard 1.
    for shard, limit in ((0, None), (1, 502)):
        sys.argv = ['run_emit_shard2.py', str(shard), '--jobs', '8', '--results', str(work / 'results'),
                    '--goport', goport_emit, '--goport-commit', commit] + (['--limit', str(limit)] if limit else [])
        es.main()
        cases = json.loads((R / f'corpus-full/shards/shard-{shard}.json').read_text())['cases']
        expected += len(cases[:limit] if limit else cases)
        result = json.loads((work / f'results/shard-{shard}-result.json').read_text())
        for r in result['rows']:
            bad = r.get('inputsChanged') or r.get('caseDirChanged')
            detail = f"{r['class']} exit {r['oracleExit']}/{r['goportExit']} {r['source']}"
            if r.get('firstDifference'):
                detail += ' first=' + json.dumps(r['firstDifference'])[:200]
            items.append(item('corpus-emit', r['id'], r['class'] == 'MATCH' and not bad, detail + (' INPUTS-CHANGED' if bad else '')))
    write_items(items_file, items, expected)


# ---- allow-list ----

def load_allow(path):
    """Lines: <result id> | <condition> | <reason>. '#' starts a comment."""
    entries = {}
    for n, line in enumerate(Path(path).read_text().splitlines(), 1):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = [p.strip() for p in line.split('|', 2)]
        if len(parts) != 3 or not all(parts) or parts[1] not in CONDITIONS:
            sys.exit(f'{path}:{n}: need "<id> | <{"|".join(CONDITIONS)}> | <reason>"')
        entries[parts[0]] = {'id': parts[0], 'condition': parts[1], 'reason': parts[2], 'used': False}
    return entries


def single_threaded_equal(row, _file, evidence):
    """Oracle nondeterminism check: goport output must equal tsgo-oracle --singleThreaded output."""
    ctx = row['ctx']
    tmp = tempfile.mkdtemp(prefix='gate-st-', dir='/tmp')
    try:
        out = subprocess.run([str(ORACLE), '-p', ctx['tsconfig'], '--noEmit', '--pretty', 'false', '--singleThreaded',
                              '--tsBuildInfoFile', f'{tmp}/st.tsbuildinfo'], cwd=ctx['cwd'], capture_output=True,
                             timeout=120).stdout
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    (evidence / (row['id'].replace('/', '_') + '.singleThreaded.out')).write_bytes(out)
    return out == Path(ctx['goportOut']).read_bytes()


def same_chars(row, file, _evidence):
    """Order-only difference: same line count, and each differing line pair has the same characters."""
    ctx = row['ctx']
    a = (Path(ctx['goDir']) / file).read_text(errors='replace').split('\n')
    b = (Path(ctx['rsDir']) / file).read_text(errors='replace').split('\n')
    return len(a) == len(b) and all(x == y or sorted(x) == sorted(y) for x, y in zip(a, b))


CONDITIONS = {'single-threaded-equal': single_threaded_equal, 'same-chars': same_chars}


def apply_allow(row, entries, evidence):
    """Turns a FAIL row into ALLOWED when allow entries cover it and their conditions hold now."""
    ctx = row.get('ctx', {})
    if row['stage'] == 'typesyms':
        if ctx.get('missing') or ctx.get('extra') or ctx.get('exits') != [0, 0] or not ctx.get('diffFiles'):
            return
        keys = [(f"{row['id']}/{f}", f) for f in ctx['diffFiles']]
    else:
        keys = [(row['id'], None)]
    # An entry id may be a glob (fnmatch). An exact entry wins over a glob.
    def entry_for(k):
        return k if k in entries else next((e for e in entries if '*' in e and fnmatch.fnmatchcase(k, e)), None)
    matched = [(entry_for(k), f) for k, f in keys]
    if not all(e for e, _ in matched):
        return
    for e, f in matched:
        if not CONDITIONS[entries[e]['condition']](row, f, evidence):
            row['detail'] += f' (allow entry {e} condition {entries[e]["condition"]} did not hold for {f})'
            return
    for e, _ in matched:
        entries[e]['used'] = True
    row['status'] = 'ALLOWED'
    row['allowedBy'] = [{'id': e, 'file': f, 'condition': entries[e]['condition'], 'reason': entries[e]['reason']} for e, f in matched]


def cmd_finish(out, meta_json):
    out = Path(out)
    meta = json.loads(meta_json)
    entries = load_allow(meta['allowList']['path'])
    evidence = out / 'allow-checks'
    evidence.mkdir(exist_ok=True)
    stages = [json.loads(l) for l in (out / 'stages.jsonl').read_text().splitlines()]
    rows = []
    for st in stages:
        f = out / 'items' / f"{st['stage']}.jsonl"
        got = [json.loads(l) for l in f.read_text().splitlines()] if f.exists() else []
        exp_file = out / 'items' / f"{st['stage']}.expected"
        st['expected'] = int(exp_file.read_text()) if exp_file.exists() else None
        if st['expected'] is None or len(got) != st['expected']:
            got.append(item(st['stage'], '_results', False,
                            f"expected {st['expected']} results, got {len(got)}; rc={st['rc']}; see logs/{st['stage']}.log"))
        for row in got:
            if row['status'] == 'FAIL':
                apply_allow(row, entries, evidence)
        st['counts'] = {s: sum(r['status'] == s for r in got) for s in ('MATCH', 'ALLOWED', 'FAIL')}
        rows += got
    fails = sum(r['status'] == 'FAIL' for r in rows)
    meta.update(finishedUtc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), verdict='PASS' if fails == 0 else 'FAIL',
                stages=stages, unusedAllowEntries=[k for k, e in entries.items() if not e['used']], results=rows)
    meta['allowList']['entries'] = list(entries.values())
    (out / 'manifest.json').write_text(json.dumps(meta, indent=1) + '\n')

    print(f"\nGATE {meta['label']} ({meta['mode']})  commit {meta['commit'][:12]}  bins {meta['binsDir']}")
    print(f"{'stage':<20}{'results':>8}{'match':>8}{'allowed':>9}{'fail':>6}{'secs':>8}")
    for st in stages:
        c = st['counts']
        print(f"{st['stage']:<20}{sum(c.values()):>8}{c['MATCH']:>8}{c['ALLOWED']:>9}{c['FAIL']:>6}{st['seconds']:>8}")
    total = {s: sum(st['counts'][s] for st in stages) for s in ('MATCH', 'ALLOWED', 'FAIL')}
    print(f"{'TOTAL':<20}{sum(total.values()):>8}{total['MATCH']:>8}{total['ALLOWED']:>9}{total['FAIL']:>6}")
    for r in rows:
        if r['status'] != 'MATCH':
            why = ' | ' + r['allowedBy'][0]['reason'][:70] if r['status'] == 'ALLOWED' else ''
            print(f"  {r['status']:<8}{r['id']}: {r['detail'][:150]}{why}")
    print(f"manifest: {out / 'manifest.json'}")
    print(f"GATE {'PASS' if fails == 0 else 'FAIL'}" + (f' ({fails} not MATCH)' if fails else ''))
    sys.exit(0 if fails == 0 else 1)


if __name__ == '__main__':
    commands = {'parse': cmd_parse, 'f1': cmd_f1, 'typesyms': cmd_typesyms, 'determinism': cmd_determinism, 'editor': cmd_editor,
                'corpus-diag': cmd_corpus_diag, 'corpus-emit': cmd_corpus_emit, 'finish': cmd_finish}
    commands[sys.argv[1]](*sys.argv[2:])
PYEOF
py() { python3 -c "$PY" "$@"; }

# stage <name> <command...>: runs one stage, logs to logs/<name>.log, records rc and seconds.
stage() {
  local name=$1; shift
  echo "== $name"
  local s=$(date +%s.%N)
  "$@" > "$OUT/logs/$name.log" 2>&1
  local rc=$?
  local secs=$(python3 -c 'import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),1))' "$s" "$(date +%s.%N)")
  printf '{"stage":"%s","rc":%d,"seconds":%s}\n' "$name" "$rc" "$secs" >> "$OUT/stages.jsonl"
  echo "   rc=$rc ${secs}s, last line: $(tail -n 1 "$OUT/logs/$name.log" | cut -c1-150)"
}
# parse <name> <runs dir> <expected>: turns a bash stage log into items.
parse() { py parse "$1" "$OUT/logs/$1.log" "$2" "$OUT/items/$1.jsonl" "$3" >> "$OUT/logs/$1.log" 2>&1; }

# The existing scripts write to measure/<round>; a ../ round keeps their output under $OUT/runs.
RUNS_REL=../compat/gate/$LABEL/runs
cd "$REPO" || exit 2
stage measure bash "$TP/measure.sh" "$RUNS_REL/measure"; parse measure "$OUT/runs/measure" 8
stage measure-extra bash "$TP/measure-extra.sh" "$RUNS_REL/measure-extra"; parse measure-extra "$OUT/runs/measure-extra" 3
stage sweep bash "$TP/sweep.sh" "$RUNS_REL/sweep"; parse sweep "$OUT/runs/sweep" 12
stage sweep-extra2 bash "$X/sweep-extra2.sh" "../../continuation-r97-goport/compat/gate/$LABEL/runs/extra2"
parse sweep-extra2 "$OUT/runs/extra2" 31
# Wide real-world sweep (51 projects, 292 configs; target/project-inputs-wide), full mode only.
if [[ $MODE == full ]]; then
  stage sweep-wide bash "$HERE/sweep-wide.sh" "../../continuation-r97-goport/compat/gate/$LABEL/runs/wide"
  parse sweep-wide "$OUT/runs/wide" 292
fi
stage sweep-hono-runtime bash "$TP/sweep-hono-runtime.sh" "$RUNS_REL/hono-rt"; parse sweep-hono-runtime "$OUT/runs/hono-rt" 7
stage f1 python3 "$R/sample-f1/run-f1.py" "$BINS/goport" "$OUT/runs/f1"
py f1 "$OUT/runs/f1/summary.json" "$OUT/items/f1.jsonl" >> "$OUT/logs/f1.log" 2>&1
stage emit env JOBS=4 bash "$R/emit/compare-emit.sh" "$BINS/goport_emit" "gate-$LABEL"; parse emit "/tmp/goport-emit-gate-$LABEL" 45
TS_NAMES=(query hono); [[ $MODE == full ]] && TS_NAMES+=(effect)
stage typesyms py typesyms "$BINS/goport_typesyms" "$OUT/runs/typesyms" "$OUT/items/typesyms.jsonl" "${TS_NAMES[@]}"
build_seq() {
  local S=$HERE/compare-build.sh
  GOPORT_BUILD=$BINS/goport_build bash "$S" seq repro cold edits flags foreign
  GOPORT_BUILD=$BINS/goport_build bash "$S" seq query-chain cold edits flags foreign
}
stage build build_seq; parse build /tmp/goport-build 32
stage determinism py determinism "$BINS/goport" "$OUT/runs/determinism" "$OUT/items/determinism.jsonl"
# The editor leak in R122 and R123 passed every other stage. 2 projects x 4 scenarios = 8 sessions.
editor_bench() {
  flock /tmp/goport-lsguard.lock python3 "$HERE/ls_edit_bench.py" --rust "cand=$BINS/tsgo" \
    --projects query-core,hono --scenarios typing-paced,errfix-paced,imports,long --out "$OUT/runs/editor"
}
stage editor editor_bench
py editor "$OUT/runs/editor/result.json" "$OUT/items/editor.jsonl" 8 >> "$OUT/logs/editor.log" 2>&1
if [[ $MODE == full ]]; then
  stage corpus-diag py corpus-diag "$BINS/goport" "$COMMIT_FULL" "$OUT/runs/corpus-diag" "$OUT/items/corpus-diag.jsonl"
  stage corpus-emit py corpus-emit "$BINS/goport_emit" "$COMMIT_FULL" "$OUT/runs/corpus-emit" "$OUT/items/corpus-emit.jsonl"
fi

META=$(python3 - "$LABEL" "$MODE" "$STARTED" "$COMMIT" "$COMMIT_FULL" "$BINS" "$SELF" "$ALLOW" <<'EOF'
import hashlib, json, os, sys
from pathlib import Path
label, mode, started, commit_in, commit, bins, gate, allow = sys.argv[1:]
R = Path('/home/theo/Code/sandbox/ts-rust/target/continuation-r97-goport')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
scripts = [R / 'tools-port/measure.sh', R / 'tools-port/measure-extra.sh', R / 'tools-port/sweep.sh',
           R.parent / 'project-inputs-extra/sweep-extra2.sh', Path(gate).parent / 'sweep-wide.sh', R / 'tools-port/sweep-hono-runtime.sh',
           R / 'sample-f1/run-f1.py', R / 'emit/compare-emit.sh', R / 'typesyms/compare-int.py',
           R / 'build-mode/compare-build.sh', R / 'corpus-full/run_shard.py', R / 'corpus-full/run_shard_parallel.py',
           R / 'emit-corpus/run_emit_shard2.py', Path(gate).parent / 'ls_edit_bench.py']
print(json.dumps({
    'label': label, 'mode': mode, 'startedUtc': started, 'commit': commit, 'commitInput': commit_in or None,
    'binsDir': bins,
    'binaries': {b: {'path': f'{bins}/{b}', 'sha256': sha(f'{bins}/{b}'), 'bytes': Path(f'{bins}/{b}').stat().st_size}
                 for b in ('goport', 'goport_emit', 'goport_typesyms', 'goport_build', 'tsgo')},
    'oracle': {'path': str(Path.home() / '.local/bin/tsgo-oracle'), 'sha256': sha(Path.home() / '.local/bin/tsgo-oracle')},
    'goDumper': {'path': str(R / 'typesyms/typesymdump-go'), 'sha256': sha(R / 'typesyms/typesymdump-go')},
    'gate': {'path': gate, 'sha256': sha(gate)},
    'allowList': {'path': allow, 'sha256': sha(allow)},
    'scripts': {str(p): sha(p) for p in scripts},
    **({'upstreamPin': os.environ['GOPORT_PIN_ACTIVE']} if os.environ.get('GOPORT_PIN_ACTIVE') else {}),
}))
EOF
)
py finish "$OUT" "$META"
