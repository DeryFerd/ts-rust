#!/usr/bin/env python3
"""The batch.oracleRebase fragment and the class tables of the oracle rebase runs (scripts/goport/oracle-rebase.sh).

usage: oracle-rebase.py fragment --pin PIN --bins DIR --lsp-tool FILE --api-tool FILE [--wire 3] [--host H]
                                 --lsp DIR... --api DIR... [--known-diffs TSV] --out FILE
       oracle-rebase.py classes DIR... [--against DIR...] [--out FILE]

fragment: checks each run and writes {lsp, api} for batch.oracleRebase (reviewer ruling 10, bump C reviewer ruling
1 items 1 and 3; check-typechecker-batch.mjs reads it):
  lsp {runs [{label, dir, resultsSha256, host}], binsSha256, oracleSha256, toolSha256, bins}
  api {runs [...], binsSha256, oracleSha256, toolSha256, wire, bins, knownDiffs [{key, reason}]}
dir is relative to the repo root. resultsSha256 is oracle-compare.py --identity's. binsSha256 is the sha256 of
<bins>/tsgo (check-typechecker-batch.mjs requires the tsgo of the base gate manifest), oracleSha256 the oracle of
the pin (pin.py show), toolSha256 the sha256 of the oracle tool that ran, bins {dir, commit, listSha256 (the
sha256 of <bins>/bins.sha256)}. wire is the API --wire (only with --wire). knownDiffs come from the TSV
(<key> TAB <reason>, # comments). Each LSP run's summary.json must name that tsgo and only that oracle, and each
API battery of manifest.json that tsgo, oracle and tool (scriptSha) and the wire (none without --wire), or the tool
exits 2.

classes: per battery, the class counts of each results dir (all of one kind), and whether the runs agree on the
class and diff pointer of every request. With --against (the same kind, for example the runs of an earlier base
revision at the same pin), also the class changes from the first --against run to the first run, and per battery
the requests that are protected (same or oracle_error_same) in some --against run and in no run, and the other way.
Markdown on stdout, or to --out.
"""
import argparse, collections, importlib.util, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
ROOT = '/home/theo/Code/sandbox/ts-rust'  # the main checkout: target/ lives there, also for a worktree's tools
spec = importlib.util.spec_from_file_location('oracle_compare', os.path.join(HERE, 'oracle-compare.py'))
OC = importlib.util.module_from_spec(spec)
spec.loader.exec_module(OC)


def fail(msg):
    print(f'oracle-rebase.py: {msg}', file=sys.stderr)
    sys.exit(2)


def run_info(path):
    """(requests, head, info, kind) of a results dir (oracle-compare.py load())."""
    requests, head, info = OC.load(path)
    return requests, head, info, OC.kind_of(path, info)


def pin_oracle(pin):
    """The oracle sha256 of a pin (pin.py show of this checkout)."""
    out = subprocess.run([sys.executable, os.path.join(REPO, 'scripts/upstream/pin.py'), 'show', pin], capture_output=True, text=True)
    try:
        return json.loads(out.stdout)['oracle']['sha256']
    except (ValueError, KeyError):
        fail(f'pin.py show {pin} gives no oracle sha256: {out.stderr.strip()}')


def fragment(a):
    tsgo = OC.sha256_file(os.path.join(a.bins, 'tsgo'))
    oracle = pin_oracle(a.pin)
    bins = {'dir': os.path.relpath(os.path.realpath(a.bins), ROOT),
            'commit': open(os.path.join(a.bins, 'COMMIT')).read().strip(),
            'listSha256': OC.sha256_file(os.path.join(a.bins, 'bins.sha256'))}
    tools = {'lsp': OC.sha256_file(a.lsp_tool), 'api': OC.sha256_file(a.api_tool)}
    out = {}
    for kind, dirs in (('lsp', a.lsp), ('api', a.api)):
        runs = []
        for d in dirs:
            _, head, info, found = run_info(d)
            if found != kind:
                fail(f'{d} is not an {kind} results dir')
            ident = OC.identity(d, kind, info)
            problems = []
            if ident['goportSha256'] != [tsgo]:
                problems.append(f'tsgo {ident["goportSha256"]}, not {tsgo}')
            if ident['oracleSha256'] != [oracle]:
                problems.append(f'oracle {ident["oracleSha256"]}, not {oracle}')
            if kind == 'api':
                for name, rec in (OC.side_file(d, 'manifest.json').get('batteries') or {}).items():
                    if rec.get('scriptSha') != tools['api'] or rec.get('wire') != a.wire:
                        problems.append(f'battery {name}: tool {rec.get("scriptSha")} wire {rec.get("wire")}')
            if problems:
                fail(f'{d}: ' + '; '.join(problems[:5]))
            runs.append({'label': head['label'], 'dir': os.path.relpath(os.path.realpath(d), ROOT),
                         'resultsSha256': ident['resultsSha256'], **({'host': a.host} if a.host else {})})
        out[kind] = {'runs': runs, 'binsSha256': tsgo, 'oracleSha256': oracle, 'toolSha256': tools[kind], 'bins': bins}
    if a.wire is not None:
        out['api']['wire'] = a.wire
    known = []
    for line in open(a.known_diffs, encoding='utf-8') if a.known_diffs else []:
        if line.strip() and not line.startswith('#'):
            key, _, reason = line.rstrip('\n').partition('\t')
            if not OC.parse_key(key) or not reason.strip():
                fail(f'{a.known_diffs}: need <battery>/<trace>#<event> TAB <reason>: {line.strip()[:80]}')
            known.append({'key': key, 'reason': reason})
    out['api']['knownDiffs'] = known
    text = json.dumps(out, indent=1) + '\n'
    with open(a.out, 'w') as f:
        f.write(text)
    print(text, end='')


def table(title, rows, cols):
    lines = [f'**{title}**', '', '| ' + ' | '.join(cols) + ' |', '|' + '---|' * len(cols)]
    lines += ['| ' + ' | '.join(str(c) for c in row) + ' |' for row in rows]
    return lines + ['']


def classes(a):
    runs = [(d, *run_info(d)) for d in a.dirs]
    against = [(d, *run_info(d)) for d in a.against]
    kinds = {r[4] for r in runs + against}
    if len(kinds) != 1:
        fail(f'the dirs are of the kinds {sorted(map(str, kinds))}, not of one kind')
    out = []
    for d, requests, head, info, _ in runs + against:
        per = collections.defaultdict(collections.Counter)
        for key, (cls, _) in requests.items():
            per[key[0]][cls] += 1
        cols = sorted({cls for counter in per.values() for cls in counter})
        rows = [[b] + [per[b][c] for c in cols] for b in sorted(per)]
        rows.append(['total'] + [sum(per[b][c] for b in per) for c in cols])
        out += table(f'{head["label"]} ({os.path.relpath(os.path.realpath(d), ROOT)}): {head["requests"]} requests', rows, ['battery'] + cols)

    def agree(group, name):
        first = group[0]
        for d, requests, head, info, _ in group[1:]:
            keys = first[1].keys() | requests.keys()
            differ = [k for k in keys if (first[1].get(k), first[3]['detail'].get(k)) != (requests.get(k), info['detail'].get(k))]
            out.append(f'{name}: {first[2]["label"]} and {head["label"]}: {len(keys)} requests, {len(differ)} with another '
                       f'class or diff pointer' + (f' (first: {", ".join(OC.keytext(k) for k in sorted(differ)[:5])})' if differ else ''))
    agree(runs, 'runs')
    if len(against) > 1:
        agree(against, 'against')
    out.append('')
    if against:
        new, old = runs[0][1], against[0][1]
        moves = collections.Counter((old.get(k, ('absent',))[0], new.get(k, ('absent',))[0]) for k in old.keys() | new.keys())
        rows = [[f, t, n] for (f, t), n in sorted(moves.items(), key=lambda e: -e[1]) if f != t]
        out += table(f'class changes, {against[0][2]["label"]} -> {runs[0][2]["label"]} ({sum(n for (f, t), n in moves.items() if f == t)} '
                     'requests keep their class)', rows, ['from', 'to', 'requests'])

        def protected(group):
            return {k for _, requests, _, _, _ in group for k, (cls, _) in requests.items() if cls in OC.PROTECTED}
        now, before = protected(runs), protected(against)
        per = collections.defaultdict(lambda: [0, 0, 0])
        for k in before | now:
            per[k[0]][0 if k in before and k in now else 1 if k in before else 2] += 1
        rows = [[b, *per[b]] for b in sorted(per)] + [['total', *(sum(v[i] for v in per.values()) for i in range(3))]]
        out += table('protected requests (same or oracle_error_same in some run)', rows,
                     ['battery', 'in both', f'only --against ({len(against)} runs)', f'only the runs ({len(runs)})'])
        only = sorted(before - now)
        if only:
            out.append('first requests protected only --against: ' + ', '.join(
                f'{OC.keytext(k)} ({old.get(k, ("absent",))[0]} -> {new.get(k, ("absent",))[0]})' for k in only[:10]))
            out.append('')
    text = '\n'.join(out) + '\n'
    if a.out:
        with open(a.out, 'w') as f:
            f.write(text)
    print(text, end='')


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sub = p.add_subparsers(dest='cmd', required=True)
    f = sub.add_parser('fragment')
    f.add_argument('--pin', required=True)
    f.add_argument('--bins', required=True)
    f.add_argument('--lsp-tool', required=True)
    f.add_argument('--api-tool', required=True)
    f.add_argument('--wire', type=int, choices=[3])
    f.add_argument('--host')
    f.add_argument('--lsp', nargs='+', required=True)
    f.add_argument('--api', nargs='+', required=True)
    f.add_argument('--known-diffs')
    f.add_argument('--out', required=True)
    c = sub.add_parser('classes')
    c.add_argument('dirs', nargs='+')
    c.add_argument('--against', nargs='*', default=[])
    c.add_argument('--out')
    a = p.parse_args()
    fragment(a) if a.cmd == 'fragment' else classes(a)


if __name__ == '__main__':
    main()
