#!/usr/bin/env python3
"""Compares two gate manifests item by item: the base (last accepted revision) and a candidate.

usage: scripts/goport/gate-compare.py <base manifest.json> <new manifest.json> [--state FILE] [--out FILE]

Rules (docs/typechecker-accountability.md, "Protected set"). This file is their one implementation:
candidate.sh side and scripts/check-typechecker-batch.mjs both run it.
- Every base id must be in the new run. A removed id is a regression.
- A base MATCH item must be MATCH, or ALLOWED by an allow entry (same id and condition) that the base
  manifest's allow list has too. The single-threaded-equal entries exist because the oracle's trace order
  changes with threads, so those items change between MATCH and ALLOWED on the same bins
  (corpus-diag/04640: r130-full ALLOWED, r131-full MATCH, r131-full-2 ALLOWED, the last two on one bins
  dir). MATCH to ALLOWED by an entry the base did not have is a regression.
- An ALLOWED item in the new run must carry allowedBy: the gate verified its gate-allow.txt
  condition again in this run.
- A FAIL in the new run is a regression, except an item of an open defect below.
- A new id is listed. A new id that is FAIL is a regression.

Open defect editor-long-growth (items editor/<project>/long). A FAIL passes only when
- the batch in --state (default docs/typechecker-state/current.json) has an openDefects record
  with that id and a status that starts with "open",
- the new failure is growth only (no rss, no answers), and
- the Rust growth is at most the fixed cap of that project in LONG_CAP below (no ratchet on the base
  value). LONG_CAP is the one place of the caps; candidate.sh side and the batch check both run this
  file, and the output lists them in longCaps. Each cap is the highest Rust growth of a good build in the
  R126 to R131 and bump B gates + 0.15 MiB/edit: query-core 1.43 + 0.15 = 1.58, hono 1.13 + 0.15 = 1.28.
  The gate's own limit follows Go's slope, so the same bins can be MATCH or FAIL (editor/hono/long on
  b2b7dca1f: MATCH in r131-full at limit 1.88, FAIL in r131-full-2 at limit 1.00, both 1.13 MiB/edit).
  A project without a cap has no allowance: its FAIL is a regression.

How a cap is lowered (caps only go down; only Theo can raise one):
- By hand: a batch that lowers the growth of a project (a fix) can lower its LONG_CAP value to that
  growth + 0.15. This file is a protected path, so the batch lists it in allowedChangedFiles, and the
  reviewer checks the value against the gate runs. The new value applies from the next revision.
- By itself: the gate's normal limit (2 x Go + 1 MiB/edit, ls_edit_bench.py) is never under
  NORMAL_LIMIT (1.00, at Go growth 0), so a Rust growth at or under 1.00 passes it in every run. When the
  base gate's Rust growth of a project is at or under 1.00, the cap of that project is 1.00 in this
  compare: its item must be MATCH, and its Rust growth must stay at or under 1.00. Each accepted
  revision then keeps the cap lowered for the next one. A MATCH at a higher growth (a steep Go slope)
  does not lower the cap, because the next run of the same bins can FAIL.
The base growth comes from a growth FAIL detail, or else from the base gate's runs/editor/result.json
(for a MATCH item). When it is unknown, a FAIL is a regression. When every project's cap is 1.00, root
closes the openDefects record, and from then on every FAIL is a regression.

Prints one JSON object, and writes it to --out when given. Exit 0: no regression.
Exit 1: regressions. Exit 2: bad input.
"""
import argparse, fnmatch, hashlib, json, os, re, sys

ROOT = '/home/theo/Code/sandbox/ts-rust'
# The fixed Rust growth cap (MiB/edit) of editor/<project>/long while the open defect editor-long-growth
# is in the batch: the highest growth of a good build + 0.15 (see the docstring).
LONG_CAP = {'query-core': 1.58, 'hono': 1.28}
# The lowest value of the gate's normal growth limit (2 x Go + 1 MiB/edit, at Go growth 0).
NORMAL_LIMIT = 1.0
OPEN_DEFECTS = {'editor-long-growth': 'editor/*/long'}
GROWTH = re.compile(r'^growth (-?[0-9.]+) MiB/edit \(limit ([0-9.]+)')
RUST_GROWTH = re.compile(r'^(-?[0-9.]+) MiB/edit')


def fail(msg):
    print(f'gate-compare.py: {msg}', file=sys.stderr)
    sys.exit(2)


def load(path):
    """(manifest, items by id, summary) of one gate manifest."""
    try:
        data = open(path, 'rb').read()
        m = json.loads(data)
    except (OSError, ValueError) as e:
        fail(f'cannot read {path}: {e}')
    if not isinstance(m.get('results'), list):
        fail(f'{path}: no results list')
    items, counts = {}, {}
    for r in m['results']:
        if r.get('id') in items or r.get('status') not in ('MATCH', 'ALLOWED', 'FAIL'):
            fail(f'{path}: duplicate id or unknown status in {r.get("id")}')
        items[r['id']] = r
        counts[r['status']] = counts.get(r['status'], 0) + 1
    head = {'manifest': os.path.abspath(path), 'sha256': hashlib.sha256(data).hexdigest(), 'label': m.get('label'),
            'commit': m.get('commit'), 'upstreamPin': m.get('upstreamPin'), 'mode': m.get('mode'),
            'verdict': m.get('verdict'), 'counts': counts}
    return m, items, head


def judged(detail):
    """The judged failures of an editor item ("growth ...; rss ..."), without the latency note."""
    return [p.strip() for p in (detail or '').split(' (latency, not judged:')[0].split(';') if p.strip()]


def growth(item):
    """Growth in MiB/edit of an editor item that failed on growth, else None."""
    for part in judged(item.get('detail')) if item['status'] == 'FAIL' else []:
        m = GROWTH.match(part)
        if m:
            return float(m.group(1))
    return None


def run_growth(manifest_path, manifest, item):
    """Rust growth in MiB/edit of an editor/<project>/long item: from its FAIL detail, or else from the
    gate's own editor run (runs/editor/result.json next to the manifest), which records it for a MATCH
    item too. None when neither has it or the run used other bins than the manifest."""
    g = growth(item)
    if g is not None:
        return g
    try:
        run = json.load(open(os.path.join(os.path.dirname(os.path.abspath(manifest_path)), 'runs', 'editor', 'result.json')))
    except (OSError, ValueError):
        return None
    project, scenario = item['id'].split('/')[1:3]
    for s in run.get('sessions') or []:
        cand = (s.get('rust') or {}).get('cand') or {}
        if s.get('project') != project or s.get('scenario') != scenario:
            continue
        if os.path.dirname(cand.get('binary') or '') != os.path.normpath(manifest.get('binsDir') or ''):
            return None
        m = RUST_GROWTH.match(str((cand.get('limits') or {}).get('growth', [None, ''])[1]))
        return float(m.group(1)) if m else None
    return None


def open_defects(state_path):
    try:
        batch = json.load(open(state_path))['batch']
    except (OSError, KeyError, ValueError) as e:
        fail(f'cannot read the batch from {state_path}: {e}')
    return {d.get('id') for d in batch.get('openDefects') or [] if str(d.get('status', '')).startswith('open')}


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('base')
    p.add_argument('new')
    p.add_argument('--state', default=f'{ROOT}/docs/typechecker-state/current.json')
    p.add_argument('--out')
    a = p.parse_args()
    bm, base, bhead = load(a.base)
    nm, new, nhead = load(a.new)
    defects = open_defects(a.state)
    # Allow entries of the base allow list, by (entry id, condition).
    base_allow = {(e['id'], e['condition']) for e in (bm.get('allowList') or {}).get('entries', [])}
    regressions, fixed, known_open, reallowed = [], [], [], []
    # The cap of each project for this compare: LONG_CAP, or NORMAL_LIMIT once the base growth is at or under it.
    caps = {}
    for project, cap in LONG_CAP.items():
        b = base.get(f'editor/{project}/long')
        bg = run_growth(a.base, bm, b) if b else None
        lowered = bg is not None and bg <= NORMAL_LIMIT + 1e-9
        caps[project] = {'cap': NORMAL_LIMIT if lowered else cap, 'openCap': cap, 'baseGrowth': bg, 'lowered': lowered}

    def regress(i, b, n, why):
        regressions.append({'id': i, 'base': b['status'] if b else 'NEW', 'new': n['status'] if n else 'REMOVED', 'why': why,
                            'detail': (n or b)['detail']})

    for i, n in new.items():
        b = base.get(i)
        if n['status'] == 'ALLOWED':
            entries = n.get('allowedBy') or []
            fresh = [f"{e.get('id')} ({e.get('condition')})" for e in entries if (e.get('id'), e.get('condition')) not in base_allow]
            if not entries:
                regress(i, b, n, 'ALLOWED without a verified allow-list condition')
            elif b is not None and b['status'] == 'MATCH':
                if fresh:
                    regress(i, b, n, 'base MATCH is ALLOWED by an allow entry the base did not have: ' + ', '.join(fresh))
                else:
                    reallowed.append({'id': i, 'conditions': sorted({e.get('condition') for e in entries})})
            elif b is not None and b['status'] == 'FAIL':
                fixed.append(i)
        elif n['status'] == 'FAIL':
            defect = next((d for d, pat in OPEN_DEFECTS.items() if fnmatch.fnmatchcase(i, pat)), None)
            if b is None:
                regress(i, b, n, 'new id is FAIL')
            elif defect is None:
                regress(i, b, n, 'base MATCH is not MATCH' if b['status'] == 'MATCH' else 'FAIL')
            elif defect not in defects:
                regress(i, b, n, f'open defect record {defect} is missing or not open')
            elif growth(n) is None or not all(x.startswith('growth ') for x in judged(n['detail'])):
                regress(i, b, n, 'fails on more than growth')
            else:
                g, project = growth(n), i.split('/')[1]
                c = caps.get(project)
                if c is None:
                    regress(i, b, n, f'no long-growth cap for {project} in gate-compare.py LONG_CAP')
                elif c['baseGrowth'] is None:
                    regress(i, b, n, 'base growth unknown (no growth FAIL detail and no runs/editor/result.json of these bins)')
                elif c['lowered']:
                    regress(i, b, n, f'cap lowered to {NORMAL_LIMIT:.2f}: base growth {c["baseGrowth"]:.2f} is at or under the '
                                     'normal limit, so the item must be MATCH')
                elif g > c['cap'] + 1e-9:
                    regress(i, b, n, f'growth {g:.2f} > cap {c["cap"]:.2f} of {project}')
                else:
                    known_open.append({'id': i, 'defect': defect, 'growth': g, 'cap': c['cap'], 'baseGrowth': c['baseGrowth'],
                                       'baseStatus': b['status'], 'detail': n['detail']})
        elif b is not None and b['status'] == 'FAIL':
            fixed.append(i)
    for i, b in base.items():
        if i not in new:
            regress(i, b, None, 'removed id')
    # A lowered cap stays lowered while the defect is open: a MATCH item of that project must keep its growth at
    # or under NORMAL_LIMIT, so the next compare, with this run as its base, lowers it again.
    for project, c in caps.items():
        i = f'editor/{project}/long'
        n = new.get(i)
        if 'editor-long-growth' in defects and c['lowered'] and n is not None and n['status'] != 'FAIL':
            c['newGrowth'] = g = run_growth(a.new, nm, n)
            if g is None or g > NORMAL_LIMIT + 1e-9:
                regress(i, base[i], n, f'growth {"unknown" if g is None else f"{g:.2f}"} after the cap of {project} was lowered '
                                       f'to {NORMAL_LIMIT:.2f} (base growth {c["baseGrowth"]:.2f})')

    # Allow entries the new run used that the base allow list did not have. The reviewer checks them.
    used = {(e['id'], e['condition']) for r in new.values() for e in r.get('allowedBy') or []}
    out = {'base': bhead, 'new': nhead,
           'capRule': f'editor/<project>/long FAIL passes while openDefects has editor-long-growth (status open), the new '
                      f'failure is growth only and its Rust growth <= the fixed cap of the project (gate-compare.py LONG_CAP: '
                      + ', '.join(f'{p} {c:.2f}' for p, c in LONG_CAP.items()) + ' MiB/edit). A cap is lowered to '
                      f'{NORMAL_LIMIT:.2f} (item must be MATCH) once the base Rust growth of that project is at or under '
                      f'{NORMAL_LIMIT:.2f}, the lowest normal limit',
           'longCaps': caps,
           'pinChanged': bhead['upstreamPin'] != nhead['upstreamPin'], 'modeChanged': bhead['mode'] != nhead['mode'],
           'allowListChanged': (nm.get('allowList') or {}).get('sha256') != (bm.get('allowList') or {}).get('sha256'),
           'newAllowEntries': [{'id': i, 'condition': c} for i, c in sorted(used - base_allow)],
           'regressions': regressions, 'knownOpen': known_open, 'reallowed': reallowed, 'fixed': sorted(fixed),
           'newIds': sorted(i for i in new if i not in base),
           'counts': {'baseItems': len(base), 'items': len(new), 'regressions': len(regressions),
                      'knownOpen': len(known_open), 'reallowed': len(reallowed), 'fixed': len(fixed)}}
    text = json.dumps(out, indent=1)
    if a.out:
        with open(a.out, 'w') as f:
            f.write(text + '\n')
    print(text)
    sys.exit(1 if regressions else 0)


if __name__ == '__main__':
    main()
