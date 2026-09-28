#!/usr/bin/env python3
"""Per-name compare of two goport test results (goport-tests.sh results.json). Read only.

usage: compare-tests.py <base results.json> <new results.json> [--name-map TSV] [--out FILE]

Every base name with status "ok" is protected. For each one, in its base suite:
  retained   ok in new
  lost       failed or ignored in new
  unrun      "unrun" in new, or missing from a new suite that is missing or incomplete
  absent     missing from a complete new suite
A base name that is not ok and is ok in new is recovered. A new name is one that no base name maps to.

--name-map TSV: one line per moved or renamed test, `<old suite>\t<old name>\t<new suite>\t<new name>`,
with more tab columns (the evidence) ignored. "-" as the new suite and name means the test was removed
(a pin bump that deletes a Go test); it is reported as removedByMap and does not block. Blank lines, lines
that start with # and a first line that starts with "oldSuite" (a header) are skipped. Two base names may
not map to one new name. The reviewer checks each entry against its evidence. check-typechecker-batch.mjs
reads the same format.

Output: JSON with "base", "new" and "nameMap" (path, sha256), then per suite and in "total":
  retained, recovered, newNames: counts
  lost, absent, unrun: lists (in "total" each entry is "<suite>: <name>")
  removedByMap: base ok names that the map removes; list per suite, count in total
  recoveredNames, newFailed: lists per suite (newFailed: new names that fail), counts in total
and "mapUnused" (map lines whose old name is not in base) and "verdict" (PASS or FAIL). With --out the
JSON goes to FILE and stdout gets one summary line. Exit 1 when any protected name is lost, absent or
unrun; exit 2 on bad input.
"""
import argparse
import hashlib
import json
import sys

LISTS = ('lost', 'absent', 'unrun')


def die(msg):
    print(f'compare-tests.py: {msg}', file=sys.stderr)
    sys.exit(2)


def load(path):
    try:
        raw = open(path, 'rb').read()
        doc = json.loads(raw)
        if not isinstance(doc.get('suites'), dict):
            raise ValueError('no "suites" object')
    except (OSError, ValueError) as err:
        die(f'{path}: {err}')
    return doc, hashlib.sha256(raw).hexdigest()


def load_map(path):
    try:
        raw = open(path, 'rb').read()
        lines = raw.decode('utf-8').splitlines()
    except (OSError, UnicodeDecodeError) as err:
        die(f'{path}: {err}')
    entries = {}
    for i, line in enumerate(lines, 1):
        if not line.strip() or line.startswith('#') or (i == 1 and line.startswith('oldSuite')):
            continue
        f = line.split('\t')
        if len(f) < 4 or not all(f[:4]):
            die(f'{path}:{i}: need 4 tab columns (old suite, old name, new suite, new name)')
        if (f[0], f[1]) in entries:
            die(f'{path}:{i}: {f[0]} {f[1]} is mapped twice')
        entries[(f[0], f[1])] = None if f[2] == '-' and f[3] == '-' else (f[2], f[3])
    return entries, hashlib.sha256(raw).hexdigest()


def compare(base, new, name_map):
    new_suites, incomplete = new['suites'], set(new.get('incomplete', []))
    claimed = set()
    suites = {}
    for suite, names in sorted(base['suites'].items()):
        r = {'retained': 0, 'recovered': 0, 'lost': [], 'absent': [], 'unrun': [], 'removedByMap': [],
             'recoveredNames': []}
        for name, was in sorted(names.items()):
            if (suite, name) in name_map and name_map[(suite, name)] is None:
                if was == 'ok':
                    r['removedByMap'].append(name)
                continue
            to_suite, to_name = name_map.get((suite, name), (suite, name))
            if (to_suite, to_name) in claimed:
                die(f'two base names map to {to_suite} {to_name}')
            claimed.add((to_suite, to_name))
            now = new_suites.get(to_suite, {}).get(to_name)
            label = name if (to_suite, to_name) == (suite, name) else f'{name} -> {to_suite}: {to_name}'
            if was != 'ok':
                if now == 'ok':
                    r['recovered'] += 1
                    r['recoveredNames'].append(label)
            elif now == 'ok':
                r['retained'] += 1
            elif now in ('failed', 'ignored'):
                r['lost'].append(label)
            elif now == 'unrun' or to_suite not in new_suites or to_suite in incomplete:
                r['unrun'].append(label)
            else:
                r['absent'].append(label)
        suites[suite] = r
    for suite, names in sorted(new_suites.items()):
        r = suites.setdefault(suite, {'retained': 0, 'recovered': 0, 'lost': [], 'absent': [], 'unrun': [],
                                      'removedByMap': [], 'recoveredNames': []})
        fresh = [n for n in names if (suite, n) not in claimed]
        r['newNames'] = len(fresh)
        r['newFailed'] = sorted(n for n in fresh if names[n] == 'failed')
    for r in suites.values():
        r.setdefault('newNames', 0)
        r.setdefault('newFailed', [])
    total = {'retained': sum(r['retained'] for r in suites.values()),
             'recovered': sum(r['recovered'] for r in suites.values()),
             'newNames': sum(r['newNames'] for r in suites.values())}
    for key in LISTS:
        total[key] = [f'{s}: {n}' for s, r in suites.items() for n in r[key]]
    for key in ('removedByMap', 'recoveredNames', 'newFailed'):
        total[key] = sum(len(r[key]) for r in suites.values())
    unused = sorted(f'{s}: {n}' for s, n in name_map if n not in base['suites'].get(s, {}))
    return suites, total, unused


def main():
    ap = argparse.ArgumentParser(description='Per-name compare of two goport-tests.sh results.json files.')
    ap.add_argument('base')
    ap.add_argument('new')
    ap.add_argument('--name-map')
    ap.add_argument('--out')
    a = ap.parse_args()
    base, base_sha = load(a.base)
    new, new_sha = load(a.new)
    name_map, map_sha = load_map(a.name_map) if a.name_map else ({}, None)
    suites, total, unused = compare(base, new, name_map)
    bad = sum(len(total[k]) for k in LISTS)
    doc = {
        'base': {'path': a.base, 'sha256': base_sha, 'source': base.get('source'), 'pin': base.get('pin')},
        'new': {'path': a.new, 'sha256': new_sha, 'source': new.get('source'), 'pin': new.get('pin'),
                'incomplete': new.get('incomplete', [])},
        'nameMap': {'path': a.name_map, 'sha256': map_sha, 'entries': len(name_map)} if a.name_map else None,
        'suites': suites,
        'total': total,
        'mapUnused': unused,
        'verdict': 'FAIL' if bad else 'PASS',
    }
    text = json.dumps(doc, indent=1, ensure_ascii=False) + '\n'
    if a.out:
        with open(a.out, 'w', encoding='utf-8') as f:
            f.write(text)
        t = total
        print(f"{doc['verdict']}: retained {t['retained']}, recovered {t['recovered']}, lost {len(t['lost'])}, "
              f"absent {len(t['absent'])}, unrun {len(t['unrun'])}, removedByMap {t['removedByMap']}, "
              f"new names {t['newNames']} ({t['newFailed']} failed), map unused {len(unused)} ({a.out})")
    else:
        sys.stdout.write(text)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
