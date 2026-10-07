#!/usr/bin/env python3
"""Prints the README table from run.sh results: median times, the speedup over tsc 6, and the
geometric mean speedup over tsc 7. usage: scripts/bench-apps/summary.py <work-dir>"""
import json, math, sys
from pathlib import Path

R = Path(sys.argv[1]) / 'results'
APPS = ['vscode', 'sentry', 'playwright', 'typeorm', 'excalidraw', 'trpc-server']
TOOLS = ['tsc6', 'tsc7', 'tsc-rs', 'bun']

rows, vs7 = [], {t: [] for t in TOOLS}
for app in APPS:
    if not (R / f'{app}.json').exists():
        continue
    med = {r['command']: r['median'] for r in json.load(open(R / f'{app}.json'))['results']}
    cells = [f'{med[t]:.2f}s' + ('' if t == 'tsc6' else f' ({med["tsc6"] / med[t]:.1f}×)') for t in TOOLS]
    rows.append(f'| {app} | ' + ' | '.join(cells) + ' |')
    for t in TOOLS:
        vs7[t].append(med['tsc7'] / med[t])
    print(app, (R / f'{app}.errors').read_text().replace('\n', ' '))

print('\n| App | ' + ' | '.join(TOOLS) + ' |\n| --- |' + ' ---: |' * len(TOOLS))
print('\n'.join(rows) + '\n')
for t in TOOLS:
    print(f'{t}: {math.exp(sum(map(math.log, vs7[t])) / len(vs7[t])):.2f}× the speed of tsc7 (geometric mean)')
