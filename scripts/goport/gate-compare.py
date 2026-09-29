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

Tools. The manifest records the sha256 of every tool that judges the items: oracle, goDumper, gate,
allowList, each stage script (scripts; most of them live under target/, which no protected path covers)
and the cached Go outputs (oracleCaches). Each hash must equal the base run's hash. A changed or removed
tool is a regression unless the batch in --state lists that exact change in gateToolChanges:
{"key": "<key as in toolChanges>", "from": "<base sha256>", "to": "<new sha256>", "reason": "..."}; the
reviewer judges each listed change. A tool that the base run did not record is listed in newTools only.

Id map (pin bumps). A new Go pin can renumber the corpus cases, so the same case has another id in the
new run (corpus-diag/04640 at 52168999f3dc is corpus-diag/04704 at 16c25522e123). The batch in --state
can name a map in gateIdMap {"path": "<TSV, relative to the repo root or absolute>", "sha256": "..."}.
The file must have that sha256. It is used only when both manifests record an upstreamPin and the pins
differ; at one pin it has no effect (idMap.applied false), so it can neither move nor remove an id.
'#' lines, blank lines and the header line "oldId TAB newId TAB source" are skipped. Each other line is
- "<old id> TAB <new id> TAB <case path>": the case moved to a new id, or
- "<old id> TAB - TAB <case path> TAB <upstream commit>": the removal form. Go removed the case between
  the two pins, in the cited commit (7 to 40 hex digits). The reviewer checks the commit.
Only the corpus families (CASE_PATH) can have lines, and both ids of a line are in one family (the part
before the first '/'). The case path of a corpus item is the source word at its fixed place in the
detail: "<class> <case path>" (corpus-diag) and "<class> exit <go>/<goport> <case path>" (corpus-emit);
notes can follow it. Bad input (exit 2): two lines with one old id, one new id, or one case path in one
family.
When the map is used:
- A base id with a line is compared with the new item of its new id: the same item under another id.
- The line's case path must equal the case path of the base item and of the new item. Else the line is
  broken and its base id is a removed id, so a map cannot pair two different cases.
- A removal line needs the case path of the base item, and the new run must not hold that case path
  in the family. Then its base id is not compared and is listed in idMap.removed. Else the line is
  broken and its base id is a removed id.
- A family with a line is a mapped family. A base id of a mapped family without a working line is a
  removed id, never compared with the new item of the same id (that id can be another case now).
  The ids of the other families are compared as before.
- A base allow entry moves only with its own case: an entry whose id is a base item that a working
  line moves applies to the new id of that line. Any other entry of a mapped family (an old pin's id,
  a removed case or a glob) gives no allowance.
- A line whose old id is not a base id is unused (listed in idMap.unused).
The output has idMap {path, sha256, lines, applied, mapped, removed, broken, unused} only when the batch
names a map, so the output without a map stays the same.

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


def read_batch(state_path):
    try:
        return json.load(open(state_path))['batch']
    except (OSError, KeyError, ValueError) as e:
        fail(f'cannot read the batch from {state_path}: {e}')


def open_defects(batch):
    return {d.get('id') for d in batch.get('openDefects') or [] if str(d.get('status', '')).startswith('open')}


def family(i):
    return i.split('/', 1)[0]


# The case path of a corpus item (see the docstring): gate.sh cmd_corpus_diag and cmd_corpus_emit write it.
CASE_PATH = {'corpus-diag': re.compile(r'^\S+ (\S+)(?: |$)'), 'corpus-emit': re.compile(r'^\S+ exit \S+/\S+ (\S+)(?: |$)')}


def case_path(item):
    """The case path of a corpus gate item, or None when its detail does not have one."""
    m = CASE_PATH[family(item['id'])].match(item.get('detail') or '')
    return m[1] if m else None


def pins_differ(a, b):
    """True when two upstream pins (hex, maybe abbreviated) are known and name other commits."""
    pin = re.compile(r'^[0-9a-f]{7,64}$')
    if not all(isinstance(p, str) and pin.match(p.lower()) for p in (a, b)):
        return False
    a, b = a.lower(), b.lower()
    return not (a.startswith(b) or b.startswith(a))


def load_id_map(ref):
    """(lines {old id: (new id or None for a removal, case path, line number, commit or None)}, path, sha256) of
    batch.gateIdMap {path, sha256}."""
    if not isinstance(ref, dict) or not isinstance(ref.get('path'), str) or not re.match(r'^[0-9a-f]{64}$', str(ref.get('sha256'))):
        fail(f'gateIdMap needs a path and a sha256: {json.dumps(ref)}')
    path = ref['path'] if os.path.isabs(ref['path']) else os.path.join(ROOT, ref['path'])
    try:
        data = open(path, 'rb').read()
        text = data.decode()
    except (OSError, UnicodeDecodeError) as e:
        fail(f'cannot read the gate id map: {e}')
    if hashlib.sha256(data).hexdigest() != ref['sha256']:
        fail(f'gate id map {path} does not have the sha256 {ref["sha256"]} that gateIdMap names')
    lines, targets, cases = {}, set(), set()
    for n, line in enumerate(text.splitlines(), 1):
        cells = line.split('\t')
        if not line.strip() or line.startswith('#') or cells[0] == 'oldId':
            continue
        removal = len(cells) == 4 and cells[1] == '-'
        if not (len(cells) == 3 or removal) or not all(c.strip() == c and c for c in cells) or '-' in (cells[0], cells[2]) \
                or (not removal and cells[1] == '-'):
            fail(f'gate id map line {n}: need "<old id> TAB <new id> TAB <case path>" or "<old id> TAB - TAB <case path> TAB <commit>"')
        old, to, source = cells[:3]
        if removal and not re.match(r'^[0-9a-f]{7,40}$', cells[3]):
            fail(f'gate id map line {n}: a removal cites the upstream commit that removed the case (7 to 40 hex digits), not {cells[3]}')
        if '/' not in old or family(old) not in CASE_PATH or not (removal or ('/' in to and family(to) == family(old))):
            fail(f'gate id map line {n}: {old} and {to} are not ids of one corpus family ({", ".join(CASE_PATH)})')
        dup = old if old in lines else to if to in targets else source if (family(old), source) in cases else None
        if dup:
            fail(f'gate id map line {n}: {dup} is in two lines')
        lines[old] = (None if removal else to, source, n, cells[3] if removal else None)
        cases.add((family(old), source))
        if not removal:
            targets.add(to)
    return lines, path, ref['sha256']


def tool_hashes(m):
    """key -> sha256 of every tool the manifest records."""
    h = {}
    for k in ('oracle', 'goDumper', 'gate', 'allowList'):
        v = m.get(k)
        if isinstance(v, dict) and v.get('sha256'):
            h[k] = v['sha256']
    for path, sha in (m.get('scripts') or {}).items():
        h[f'script:{path}'] = sha
    for path, sha in (m.get('oracleCaches') or {}).items():
        h[f'oracleCache:{path}'] = sha
    return h


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('base')
    p.add_argument('new')
    p.add_argument('--state', default=f'{ROOT}/docs/typechecker-state/current.json')
    p.add_argument('--out')
    a = p.parse_args()
    bm, base, bhead = load(a.base)
    nm, new, nhead = load(a.new)
    batch = read_batch(a.state)
    defects = open_defects(batch)
    # The id map of a pin bump (see the docstring): moved maps a base id to its new id, dropped holds the
    # base ids that a removal line removes, and gone says why a base id of a mapped family has neither.
    lines, id_map, moved, gone, dropped = {}, None, {}, {}, set()
    if batch.get('gateIdMap') is not None:
        lines, path, sha = load_id_map(batch['gateIdMap'])
        id_map = {'path': path, 'sha256': sha, 'lines': len(lines), 'applied': pins_differ(bhead['upstreamPin'], nhead['upstreamPin']),
                  'mapped': 0, 'removed': [], 'broken': [], 'unused': []}
        if not id_map['applied']:
            lines = {}
    mapped_families = {family(old) for old in lines}
    # The case paths of the new items of each mapped family: a removal line needs its case to be gone.
    new_cases = {(family(i), case_path(r)) for i, r in new.items() if family(i) in mapped_families}
    for old, (to, source, n, commit) in sorted(lines.items(), key=lambda e: e[1][2]):
        b, t = base.get(old), new.get(to)
        if b is None:
            id_map['unused'].append(old)
        elif case_path(b) != source:
            gone[old] = f'removed id (id map line {n}: {source} is not the case path of {old}, {case_path(b)})'
            id_map['broken'].append(old)
        elif to is None and (family(old), source) in new_cases:
            gone[old] = f'removed id (id map line {n} removes the case {source}, but the new run holds it)'
            id_map['broken'].append(old)
        elif to is None:
            dropped.add(old)
            id_map['removed'].append({'id': old, 'source': source, 'commit': commit, 'line': n, 'base': b['status']})
        elif t is None:
            gone[old] = f'removed id (id map line {n}: its new id {to} is not in the new run)'
        elif case_path(t) != source:
            gone[old] = f'removed id (id map line {n}: {to} is the case {case_path(t)}, not {source})'
            id_map['broken'].append(old)
        else:
            moved[old] = to
    if id_map:
        id_map['mapped'] = len(moved)

    def new_id(i):
        """The id of base id (or base allow entry id) i in the new run, or None when the map gives it none. In a
        mapped family only a working line gives one, so an allow entry moves only with its own case."""
        return moved.get(i) if family(i) in mapped_families else i

    # Allow entries of the base allow list, by (entry id at the new pin, condition).
    base_allow = {(new_id(e['id']), e['condition']) for e in (bm.get('allowList') or {}).get('entries', [])
                  if new_id(e['id']) is not None}
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
                            'detail': (n or b)['detail'], **({'baseId': b['id']} if b and b['id'] != i else {})})

    # The base item of each new id (the same id, or the base id that the id map moves to it).
    base_of = {new_id(i): i for i in base if new_id(i) is not None}
    for i, n in new.items():
        b = base.get(base_of.get(i))
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
        t = new_id(i)
        if i in dropped:
            continue  # removed by a removal line at a pin change: listed in idMap.removed for the reviewer
        if t is None:
            regress(i, b, None, gone.get(i) or f'removed id (the id map has no line for it, and its family {family(i)} is mapped)')
        elif t not in new:
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

    # Tools: every hash the base recorded must be equal in the new run, or be listed in batch.gateToolChanges.
    listed = {(c.get('key'), c.get('from'), c.get('to')) for c in batch.get('gateToolChanges') or []}
    bt, nt = tool_hashes(bm), tool_hashes(nm)
    tool_changes = []
    for k, bsha in sorted(bt.items()):
        nsha = nt.get(k)
        if nsha == bsha:
            continue
        ok = (k, bsha, nsha) in listed
        tool_changes.append({'key': k, 'from': bsha, 'to': nsha, 'listed': ok})
        if not ok:
            regressions.append({'id': f'tool/{k}', 'base': bsha, 'new': nsha or 'REMOVED',
                                'why': 'tool changed and not listed in batch.gateToolChanges' if nsha else 'tool removed',
                                'detail': k})

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
           **({'idMap': id_map} if id_map else {}),
           'allowListChanged': (nm.get('allowList') or {}).get('sha256') != (bm.get('allowList') or {}).get('sha256'),
           'newAllowEntries': [{'id': i, 'condition': c} for i, c in sorted(used - base_allow)],
           'toolChanges': tool_changes, 'newTools': sorted(k for k in nt if k not in bt),
           'regressions': regressions, 'knownOpen': known_open, 'reallowed': reallowed, 'fixed': sorted(fixed),
           'newIds': sorted(i for i in new if i not in base_of),
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
