#!/usr/bin/env python3
"""Verify the fresh benchmark's Rust/Go diagnostics before publishing its tables."""
import sys
from pathlib import Path

results = Path(sys.argv[1]) / 'results'
apps = ['vscode', 'sentry', 'playwright', 'typeorm', 'excalidraw', 'trpc-server']
projects = ['apps-server', 'apps-web', 'apps-mobile', 'packages-client-runtime', 'packages-shared']


def compare(stem: str, effect_only: bool = False) -> None:
    def diagnostics(tool: str) -> list[str]:
        lines = (results / f'{stem}.{tool}.diag').read_text().splitlines()
        return [line for line in lines if not effect_only or 'TS377' in line]
    rust, go = diagnostics('tsc-rs'), diagnostics('tsc7')
    if rust != go:
        raise SystemExit(f'{stem}: Rust/Go diagnostics differ; see saved preflight output')
    print(f'{stem}: MATCH ({len(rust)} diagnostics)')


for app in apps:
    compare(app)
for project in projects:
    compare(f't3-{project}-noeffect')
    # effect-tsgo has its own TypeScript pin. Compare its Effect rules only;
    # the plain pinned TypeScript comparison above covers TypeScript errors.
    compare(f't3-{project}-effect', effect_only=True)
