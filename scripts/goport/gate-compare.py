#!/usr/bin/env python3
"""Compares two gate manifests item by item: the base (last accepted revision) and a candidate.

usage: scripts/goport/gate-compare.py <base manifest.json> <new manifest.json> [--state FILE] [--out FILE]

Rules (docs/typechecker-accountability.md, "Protected set"). This file is their one implementation:
candidate.sh side and scripts/check-typechecker-batch.mjs both run it.
- Every base id must be in the new run. A removed id is a regression.
- A base MATCH item must be MATCH, or ALLOWED by an allow entry (same id, condition and case path) that
  the base manifest's allow list has too ("reallowed"). The single-threaded-equal entries exist because the
  oracle's trace order changes with threads, so those items change between MATCH and ALLOWED on the same bins
  (corpus-diag/04640: r130-full ALLOWED, r131-full MATCH, r131-full-2 ALLOWED, the last two on one bins
  dir). MATCH to ALLOWED by an entry the base did not have is a regression.
- An ALLOWED item in the new run must carry allowedBy: the gate verified its gate-allow.txt
  condition again in this run.
- Case paths of allow entries. A corpus id names another case at another Go pin, so an allow entry of a
  CASE_PATH family (corpus-diag, corpus-emit, f1) names its case path (gate-allow.txt "<id> | <case path> |
  <condition> | <reason>"), and gate.sh applies it only to the item of that id with that case path. The
  case path of an entry is its path; an entry of the old form (gate.sh before case paths, which applied it
  by id only) has the case path of the item of its id in that run, the one case it could allow there, and
  none when that run has no such item. An ALLOWED item of such a family whose allowedBy entry names another
  case path, or none, is a regression. An entry of such a family without a case path gives no allowance.
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
differ; at one pin it has no effect (idMap.applied false), so it cannot move an id.
'#' lines, blank lines and the header line "oldId TAB newId TAB source" are skipped. Each other line is
"<old id> TAB <new id> TAB <case path>": the case moved to a new id. A line "<old id> TAB - TAB <case path>"
removes a case that Go removed (the removal check below). Without such a line, a base case that the new run
does not hold is a removed id, also when Go removed it.
Only the corpus families (MAP_FAMILIES) can have lines, and both ids of a line are in one family (the part
before the first '/'). The case path of a corpus item is the source word at its fixed place in the
detail: "<class> <case path>" (corpus-diag, and f1) and "<class> exit <go>/<goport> <case path>"
(corpus-emit); notes can follow it. Bad input (exit 2): a line of another form (also "-" as the old id or the
case path), and two lines with one old id, one new id, or one case path in one family.
When the map is used:
- A base id with a line is compared with the new item of its new id: the same item under another id.
- The line's case path must equal the case path of the base item and of the new item. Else the line is
  broken and its base id is a removed id, so a map cannot pair two different cases. Layout move: when the
  new pin has the layout "typescript" (microsoft/TypeScript, tsc/), the new item's case path is the line's
  case path moved as below (an old _submodules/TypeScript/tests/cases path is under testdata/tests/cases),
  and a base allow entry that moves with its case has its case path moved the same way.
- A family with a line is a mapped family. A base id of a mapped family without a working line is a
  removed id, never compared with the new item of the same id (that id can be another case now).
  The ids of the other families are compared as before.
- A base allow entry moves only with its own case: an entry whose id is a base item that a working
  line moves applies to the new id of that line, with its own case path. Any other entry of a mapped
  family (an old pin's id, a case without a line or a glob) gives no allowance.
- A line whose old id is not a base id is unused (listed in idMap.unused).
- Removal check (Go at both pins). A removal line removes its base id (listed in idMap.removed, not a
  regression) only when its case path is the case path of the base item, the case file is in the base pin's
  Go checkout, the new pin's Go checkout has neither that path nor its moved path, and no new item of the
  family has either path. The Go checkouts and layouts come from `scripts/upstream/pin.py show <pin>` of this
  checkout. The moved path: at a new pin of layout "typescript" (microsoft/TypeScript, tsc/) an old
  _submodules/TypeScript/tests/cases/<p> is testdata/tests/cases/<p>, or the new name that the pin's
  testdata/promotedTestCollisions.txt gives. A removal line that fails the check is broken, and its base id is a
  removed id.
The output has idMap {path, sha256, lines, applied, mapped, broken, unused} only when the batch
names a map, so the output without a map stays the same. A map with removal lines adds idMap.removed.

Prints one JSON object, and writes it to --out when given. Exit 0: no regression.
Exit 1: regressions. Exit 2: bad input.
"""
import argparse, fnmatch, hashlib, json, os, re, subprocess, sys

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


# The case path of an item whose detail names a Go test case (see the docstring): gate.sh cmd_corpus_diag,
# cmd_corpus_emit and cmd_f1 write it, and its allow step reads it the same way. Allow entries of these
# families carry a case path. Only the corpus families (MAP_FAMILIES) can have gate id map lines.
CASE_PATH = {'corpus-diag': re.compile(r'^\S+ (\S+)(?: |$)'), 'corpus-emit': re.compile(r'^\S+ exit \S+/\S+ (\S+)(?: |$)'),
             'f1': re.compile(r'^\S+ (\S+)(?: |$)')}
MAP_FAMILIES = ('corpus-diag', 'corpus-emit')


def case_path(item):
    """The case path of a gate item of a CASE_PATH family, or None (another family, or a detail without one)."""
    pattern = CASE_PATH.get(family(item['id']))
    m = pattern.match(item.get('detail') or '') if pattern else None
    return m[1] if m else None


def entry_path(e, items):
    """The case path of an allow entry (a base allow list entry, or an allowedBy entry of a new item) of a
    CASE_PATH family, by the docstring: its path, else the case path of the item of its id in items (the old
    form, applied by id). None for other families and when neither is known."""
    if family(str(e.get('id'))) not in CASE_PATH:
        return None
    if e.get('path') is not None:
        return e['path']
    return case_path(items[e['id']]) if e.get('id') in items else None


def pins_differ(a, b):
    """True when two upstream pins (hex, maybe abbreviated) are known and name other commits."""
    pin = re.compile(r'^[0-9a-f]{7,64}$')
    if not all(isinstance(p, str) and pin.match(p.lower()) for p in (a, b)):
        return False
    a, b = a.lower(), b.lower()
    return not (a.startswith(b) or b.startswith(a))


def load_id_map(ref):
    """(lines {old id: (new id, case path, line number)}, path, sha256) of batch.gateIdMap {path, sha256}."""
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
        if len(cells) != 3 or not all(c.strip() == c and c for c in cells) or '-' in (cells[0], cells[2]):
            fail(f'gate id map line {n}: need "<old id> TAB <new id> TAB <case path>" or "<old id> TAB - TAB <case path>"')
        old, to, source = cells
        if not all('/' in i and family(i) in MAP_FAMILIES for i in (old, to) if i != '-') or (to != '-' and family(to) != family(old)):
            fail(f'gate id map line {n}: {old} and {to} are not ids of one corpus family ({", ".join(MAP_FAMILIES)})')
        dup = old if old in lines else to if to != '-' and to in targets else source if (family(old), source) in cases else None
        if dup:
            fail(f'gate id map line {n}: {dup} is in two lines')
        lines[old] = (to, source, n)
        cases.add((family(old), source))
        targets.add(to)
    return lines, path, ref['sha256']


OLD_CASES = '_submodules/TypeScript/tests/cases/'


def go_pin(pin):
    """(Go checkout, layout) of a pin, from pin.py show of this checkout."""
    pin_py = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'upstream', 'pin.py')
    run = subprocess.run([sys.executable, pin_py, 'show', pin], capture_output=True, text=True)
    if run.returncode != 0:
        fail(f'pin.py show {pin}: {run.stderr.strip()}')
    rec = json.loads(run.stdout)
    return rec['goCheckout'], rec.get('layout', 'typescript-go')


def moved_path(source, go, layout):
    """The case path of an old-layout case at a new pin (the docstring's removal check)."""
    if layout != 'typescript' or not source.startswith(OLD_CASES):
        return source
    text = open(os.path.join(go, 'testdata/promotedTestCollisions.txt'), encoding='utf-8').read()
    rel = source[len(OLD_CASES):]
    return 'testdata/tests/cases/' + dict(re.findall(r'^renamed-promoted\S* (\S+) -> (\S+)$', text, re.M)).get(rel, rel)


def removal_problem(old, source, b, new, go_base, go_new):
    """Why the removal line of base item b (id old, case path source) fails the removal check, or None."""
    (bgo, _), (ngo, nlayout) = go_base, go_new
    if case_path(b) != source:
        return f'{source} is not the case path of {old}, {case_path(b)}'
    if not os.path.isfile(os.path.join(bgo, source)):
        return f'{source} is not in the base pin Go checkout {bgo}'
    paths = sorted({source, moved_path(source, ngo, nlayout)})
    there = [q for q in paths if os.path.isfile(os.path.join(ngo, q))]
    if there:
        return f'the new pin Go checkout {ngo} has {", ".join(there)}'
    held = sorted(i for i, r in new.items() if family(i) == family(old) and case_path(r) in paths)
    return f'the new run holds the case: {", ".join(held)}' if held else None


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
    # The id map of a pin bump (see the docstring): moved maps a base id to its new id, and gone says why a
    # base id of a mapped family has none.
    lines, id_map, moved, gone, removed = {}, None, {}, {}, {}
    if batch.get('gateIdMap') is not None:
        lines, path, sha = load_id_map(batch['gateIdMap'])
        id_map = {'path': path, 'sha256': sha, 'lines': len(lines), 'applied': pins_differ(bhead['upstreamPin'], nhead['upstreamPin']),
                  'mapped': 0, 'broken': [], 'unused': []}
        if not id_map['applied']:
            lines = {}
    mapped_families = {family(old) for old in lines}
    go = {}  # 'base' and 'new': (Go checkout, layout), read when a line needs them

    def pins():
        if not go:
            go.update(base=go_pin(bhead['upstreamPin']), new=go_pin(nhead['upstreamPin']))
        return go['base'], go['new']

    def at_new(source):
        """A base case path as the new pin names it (the layout move; unchanged at an old-layout new pin)."""
        if not lines or not source or not source.startswith(OLD_CASES):
            return source
        (_, (ngo, nlayout)) = pins()
        return moved_path(source, ngo, nlayout)

    for old, (to, source, n) in sorted(lines.items(), key=lambda e: e[1][2]):
        b, t = base.get(old), new.get(to)
        if b is None:
            id_map['unused'].append(old)
        elif to == '-':
            why = removal_problem(old, source, b, new, *pins())
            if why:
                gone[old] = f'removed id (id map line {n} removes it, but {why})'
                id_map['broken'].append(old)
            else:
                removed[old] = source
        elif case_path(b) != source:
            gone[old] = f'removed id (id map line {n}: {source} is not the case path of {old}, {case_path(b)})'
            id_map['broken'].append(old)
        elif t is None:
            gone[old] = f'removed id (id map line {n}: its new id {to} is not in the new run)'
        elif case_path(t) != at_new(source):
            gone[old] = f'removed id (id map line {n}: {to} is the case {case_path(t)}, not {at_new(source)})'
            id_map['broken'].append(old)
        else:
            moved[old] = to
    if id_map:
        id_map['mapped'] = len(moved)

    if removed:
        id_map['removed'] = [{'id': i, 'path': p} for i, p in sorted(removed.items())]

    def new_id(i):
        """The id of base id (or base allow entry id) i in the new run, or None when the map gives it none. In a
        mapped family only a working line gives one, so an allow entry moves only with its own case."""
        return moved.get(i) if family(i) in mapped_families else i

    # Allow entries of the base allow list, by (entry id at the new pin, condition, case path). An entry of a CASE_PATH
    # family without a case path gives no allowance.
    base_allow = {(new_id(e['id']), e['condition'], at_new(entry_path(e, base)) if family(e['id']) in mapped_families else entry_path(e, base))
                  for e in (bm.get('allowList') or {}).get('entries', [])
                  if new_id(e['id']) is not None and (entry_path(e, base) is not None or family(e['id']) not in CASE_PATH)}
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
            entries = [(e.get('id'), e.get('condition'), entry_path(e, new)) for e in n.get('allowedBy') or []]
            fresh = [f"{e} ({c}{', ' + p if p else ''})" for e, c, p in entries if (e, c, p) not in base_allow]
            other = [f'{e} ({p})' for e, _, p in entries if family(i) in CASE_PATH and (p is None or p != case_path(n))]
            if not entries:
                regress(i, b, n, 'ALLOWED without a verified allow-list condition')
            elif other:
                regress(i, b, n, f'ALLOWED by an allow entry of another case than {case_path(n)}: ' + ', '.join(other))
            elif b is not None and b['status'] == 'MATCH':
                if fresh:
                    regress(i, b, n, 'base MATCH is ALLOWED by an allow entry the base did not have: ' + ', '.join(fresh))
                else:
                    reallowed.append({'id': i, 'conditions': sorted({c for _, c, _ in entries})})
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
        if i in removed:
            continue
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
    used = {(e.get('id'), e.get('condition'), entry_path(e, new)) for r in new.values() for e in r.get('allowedBy') or []}
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
           'newAllowEntries': [{'id': i, 'condition': c, 'path': p}
                               for i, c, p in sorted(used - base_allow, key=lambda k: tuple(x or '' for x in k))],
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
