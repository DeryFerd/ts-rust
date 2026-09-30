#!/usr/bin/env python3
"""Per-name compare of two goport test results (goport-tests.sh results.json). Read only.

usage: compare-tests.py <base results.json> <new results.json> [--name-map TSV] [--out FILE]

A results file that ends in .gz is read as gzip (docs/goport-protected/tests-r131.json.gz). Its
sha256 in the output is the sha256 of the file as stored. Each file must have a "pin" of 7 to 64 hex
characters (the Go pin that goport-tests.sh ran at), or the tool exits 2.

Every base name with status "ok" is protected. For each one, in its base suite:
  retained   ok in new
  lost       failed or ignored in new
  unrun      "unrun" in new, or missing from a new suite that is missing or incomplete
  absent     missing from a complete new suite
A base name that is not ok and is ok in new is recovered. A new name is one that no base name maps to.

--name-map TSV: one line per moved, renamed or removed test,
`<old suite>\t<old name>\t<new suite>\t<new name>\t<evidence>` (more tab cells belong to the evidence,
which must not be empty). "-" as the new suite and name means the test was removed; it is reported as
removedByMap and does not block. Blank lines, lines that start with # and a first line whose first cell
is "oldSuite" (a header) are skipped. Two base names may not map to one new name (exit 2). A map line
that is not an identity is rejected (mapRejected, exit 1) when:
  - its old name is still in the new results (a moved or removed test leaves no copy behind), except a
    removal line of a go_baselines_reference name that is "ignored" in go_baselines_reference of the new
    results: a stale Go reference file that no Go test at the new pin writes, which the reference walk
    lists as ignored (bump C reviewer ruling 1 item 5). Such lines are counted on their own in
    mapRemovedIgnored, and the reviewer checks the Go evidence of each. A removal line of a name that is
    ok or failed in the new results, or of an ignored name of another suite (a libtest #[ignore]), is
    rejected,
  - its new name is a base name (so a map cannot swap a lost name for a passing one, or chain), or
  - it removes a name, the Go pin did not change and the suite is not a kept-crate suite.
The reviewer checks each entry against its evidence. check-typechecker-batch.mjs applies the same
format and rules.

Output: JSON with "base", "new" and "nameMap" (path, sha256), then per suite and in "total":
  retained, recovered, newNames: counts
  lost, absent, unrun: lists (in "total" each entry is "<suite>: <name>")
  removedByMap: base ok names that the map removes; list per suite, count in total
  recoveredNames, newFailed: lists per suite (newFailed: new names that fail), counts in total
and "mapRejected" ("line <n>: <reason>"), "mapRemovedIgnored" ("<suite>: <name>" of the removal lines
above), "mapUnused" (map lines whose old name is not in base) and
"verdict" (PASS or FAIL). With --out the JSON goes to FILE and stdout gets one summary line. Exit 1 when
any protected name is lost, absent or unrun or a map line is rejected; exit 2 on bad input.
"""
import argparse
import gzip
import hashlib
import json
import re
import sys
import zlib

LISTS = ('lost', 'absent', 'unrun')
HEX_HASH = re.compile(r'[0-9a-fA-F]{7,64}')  # use fullmatch
# Suites of the kept crates: stages 5 and 6 move or delete their tests without a Go pin change.
KEPT_CRATE_SUITE = re.compile(r'^ts_(scanner|ast|diagnostics|path|core|jsnum)_lib$')
# The only suite whose "ignored" names a removal line may keep (stale Go reference files, ruling 1 item 5).
STALE_REFERENCE_SUITE = 'go_baselines_reference'


def die(msg):
    print(f'compare-tests.py: {msg}', file=sys.stderr)
    sys.exit(2)


def load(path):
    """The results doc of a .json or .json.gz file and the sha256 of the file bytes."""
    try:
        raw = open(path, 'rb').read()
        doc = json.loads(gzip.decompress(raw) if path.endswith('.gz') else raw)
        if not isinstance(doc, dict) or not isinstance(doc.get('suites'), dict):
            raise ValueError('no "suites" object')
        # A pin that is not a hash would count as a pin change and let a map line remove a name.
        if not isinstance(doc.get('pin'), str) or not HEX_HASH.fullmatch(doc['pin']):
            raise ValueError(f'"pin" must be 7 to 64 hex characters, not {doc.get("pin")!r}')
    except (OSError, EOFError, ValueError, zlib.error) as err:
        die(f'{path}: {err}')
    return doc, hashlib.sha256(raw).hexdigest()


def load_map(path):
    """{(old suite, old name): (line, (new suite, new name) or None)} and the sha256 of the file."""
    try:
        raw = open(path, 'rb').read()
        lines = raw.decode('utf-8').splitlines()
    except (OSError, UnicodeDecodeError) as err:
        die(f'{path}: {err}')
    entries = {}
    for i, line in enumerate(lines, 1):
        f = line.split('\t')
        if not line.strip() or line.startswith('#') or (i == 1 and f[0] == 'oldSuite'):
            continue
        if len(f) < 5 or not all(c.strip() for c in f[:5]):
            die(f'{path}:{i}: need old suite, old name, new suite, new name and evidence (5 tab columns)')
        if (f[0], f[1]) in entries:
            die(f'{path}:{i}: {f[0]} {f[1]} is mapped twice')
        entries[(f[0], f[1])] = (i, None if f[2] == '-' and f[3] == '-' else (f[2], f[3]))
    return entries, hashlib.sha256(raw).hexdigest()


def same_hash(a, b):
    """Two abbreviated or full git hashes name the same object (check-typechecker-batch.mjs sameHash)."""
    if not isinstance(a, str) or not isinstance(b, str):
        return False
    x, y = a.lower(), b.lower()
    return bool(HEX_HASH.fullmatch(x) and HEX_HASH.fullmatch(y)) and (x.startswith(y) or y.startswith(x))


def rejected_map_lines(base, new, name_map):
    """The map lines that could hide a lost name, as "line <n>: <reason>", and the removal lines of
    go_baselines_reference names that are "ignored" in the new results, as "<suite>: <name>"."""
    before, after = base['suites'], new['suites']
    pin_changed = not same_hash(base['pin'], new['pin'])  # load() checked that both pins are hashes
    out, ignored = [], []
    for (suite, name), (line, to) in sorted(name_map.items(), key=lambda e: e[1][0]):
        if to == (suite, name):
            continue
        if to is None and suite == STALE_REFERENCE_SUITE and after.get(suite, {}).get(name) == 'ignored':
            ignored.append(f'{suite}: {name}')
        elif name in after.get(suite, {}):
            out.append(f'line {line}: {suite} {name} is still in the new results')
        if to and to[1] in before.get(to[0], {}):
            out.append(f'line {line}: the new name {to[0]} {to[1]} is a base name')
        if to is None and not pin_changed and not KEPT_CRATE_SUITE.match(suite):
            out.append(f'line {line}: removes {suite} {name}, but the Go pin did not change and {suite} '
                       'is not a kept-crate suite')
    return out, ignored


def compare(base, new, name_map):
    new_suites, incomplete = new['suites'], set(new.get('incomplete', []))
    claimed = set()
    suites = {}
    for suite, names in sorted(base['suites'].items()):
        r = {'retained': 0, 'recovered': 0, 'lost': [], 'absent': [], 'unrun': [], 'removedByMap': [],
             'recoveredNames': []}
        for name, was in sorted(names.items()):
            to = name_map[(suite, name)][1] if (suite, name) in name_map else (suite, name)
            if to is None:
                if was == 'ok':
                    r['removedByMap'].append(name)
                continue
            to_suite, to_name = to
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
    rejected, removed_ignored = rejected_map_lines(base, new, name_map)
    bad = sum(len(total[k]) for k in LISTS) + len(rejected)
    doc = {
        'base': {'path': a.base, 'sha256': base_sha, 'source': base.get('source'), 'pin': base.get('pin')},
        'new': {'path': a.new, 'sha256': new_sha, 'source': new.get('source'), 'pin': new.get('pin'),
                'incomplete': new.get('incomplete', [])},
        'nameMap': {'path': a.name_map, 'sha256': map_sha, 'entries': len(name_map)} if a.name_map else None,
        'suites': suites,
        'total': total,
        'mapRejected': rejected,
        'mapRemovedIgnored': removed_ignored,
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
              f"new names {t['newNames']} ({t['newFailed']} failed), map rejected {len(rejected)}, "
              f"map removed ignored {len(removed_ignored)}, map unused {len(unused)} ({a.out})")
    else:
        sys.stdout.write(text)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
