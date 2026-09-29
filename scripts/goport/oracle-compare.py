#!/usr/bin/env python3
"""Compares two LSP or API oracle results request by request: the base (last accepted revision) and a candidate.

usage: scripts/goport/oracle-compare.py <base results dir> <new results dir> [--out FILE]

A results dir is <out-root>/results/<label> of `scripts/goport/lsp_oracle.py check` or
`scripts/goport/api_oracle.py check`. Each traces/<battery>/**/<trace>.json there lists the requests of
one trace with their class. A request is keyed by battery, trace and event (LSP "i", API "event").
A base request is protected when its class is "same" or "oracle_error_same" (goport gives the oracle's
answer, or the oracle's error). Per request:
- retained: protected in the base and in the new run
- recovered: not protected in the base, protected in the new run
- lost: protected in the base, another class in the new run (not an unrun class)
- unrun: protected in the base, not_run, skipped_method or skipped in the new run
- absent: protected in the base, and the new run has no such request or trace
- newRequests: only in the new run
Both sides must use the same goldens (one oracle and pin). At a pin bump, Go's answers change, so the
reviewer checks each loss against Go at the new pin.

Prints one JSON object {base, new, protectedClasses, total, batteries, lostFirst}, and writes it to
--out when given. Exit 0: no loss. Exit 1: a protected base request is lost, unrun or absent.
Exit 2: bad input.
"""
import argparse, collections, json, os, sys

PROTECTED = ('same', 'oracle_error_same')
UNRUN = ('not_run', 'skipped_method', 'skipped')
FIELDS = ('retained', 'recovered', 'lost', 'unrun', 'absent', 'newRequests')


def fail(msg):
    print(f'oracle-compare.py: {msg}', file=sys.stderr)
    sys.exit(2)


def load(results_dir):
    """{(battery, trace, event): (class, method)} of one results dir, and its head."""
    tdir = os.path.join(results_dir, 'traces')
    if not os.path.isdir(tdir):
        fail(f'no traces/ in {results_dir}')
    requests, traces = {}, 0
    for d, _, files in sorted(os.walk(tdir)):
        for f in sorted(files):
            if not f.endswith('.json'):
                continue
            try:
                t = json.load(open(os.path.join(d, f)))
            except (OSError, ValueError) as e:
                fail(f'cannot read {os.path.join(d, f)}: {e}')
            traces += 1
            for e in t.get('events') or []:
                event = e.get('i', e.get('event'))
                requests[(t['battery'], t['trace'], str(event))] = (e['class'], e.get('method'))
    if not traces:
        fail(f'no trace results in {tdir}')
    return requests, {'dir': os.path.abspath(results_dir), 'label': os.path.basename(os.path.normpath(results_dir)),
                      'traces': traces, 'requests': len(requests)}


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('base')
    p.add_argument('new')
    p.add_argument('--out')
    a = p.parse_args()
    base, bhead = load(a.base)
    new, nhead = load(a.new)
    total, per = collections.Counter(), collections.defaultdict(collections.Counter)
    lost = []
    for key, (cls, method) in base.items():
        now = new.get(key)
        if cls not in PROTECTED:
            field = 'recovered' if now and now[0] in PROTECTED else None
        elif now is None:
            field = 'absent'
        elif now[0] in PROTECTED:
            field = 'retained'
        else:
            field = 'unrun' if now[0] in UNRUN else 'lost'
        if field:
            total[field] += 1
            per[key[0]][field] += 1
        if field in ('lost', 'unrun', 'absent'):
            lost.append({'battery': key[0], 'trace': key[1], 'event': key[2], 'method': method, 'base': cls,
                         'new': now[0] if now else 'absent'})
    for key in new.keys() - base.keys():
        total['newRequests'] += 1
        per[key[0]]['newRequests'] += 1
    out = {'base': bhead, 'new': nhead, 'protectedClasses': list(PROTECTED),
           'total': {k: total[k] for k in FIELDS},
           'batteries': {b: {k: c[k] for k in FIELDS} for b, c in sorted(per.items())},
           'lostFirst': lost[:50]}
    text = json.dumps(out, indent=1)
    if a.out:
        with open(a.out, 'w') as f:
            f.write(text + '\n')
    print(text)
    sys.exit(1 if lost else 0)


if __name__ == '__main__':
    main()
