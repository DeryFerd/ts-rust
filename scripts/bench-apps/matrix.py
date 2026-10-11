#!/usr/bin/env python3
"""Print the preparation and timing matrices for the selected benchmark suite."""
import json
import sys

suite = sys.argv[1]
if suite not in ['all', 'apps', 't3']:
    raise SystemExit(f'unknown suite: {suite}')
prepare, bench = [], []
if suite in ['all', 'apps']:
    for project in ['vscode', 'sentry', 'playwright', 'typeorm', 'excalidraw', 'trpc']:
        prepare.append(project)
        bench.append({'project': project, 'case': 'trpc-server' if project == 'trpc' else project,
                      'path': '', 'mode': ''})
if suite in ['all', 't3']:
    prepare.append('t3code')
    for project in ['apps/server', 'apps/web', 'apps/mobile', 'packages/client-runtime', 'packages/shared']:
        for mode in ['noeffect', 'effect']:
            bench.append({'project': 't3code', 'case': f't3-{project.replace("/", "-")}-{mode}',
                          'path': project, 'mode': mode})
print('prepare=' + json.dumps({'project': prepare}))
print('bench=' + json.dumps({'include': bench}))
