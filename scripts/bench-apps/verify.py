#!/usr/bin/env python3
"""Verify the fresh benchmark's Rust/Go diagnostics before publishing its tables."""
import sys
import re
from pathlib import Path

apps = ['vscode', 'sentry', 'playwright', 'typeorm', 'excalidraw', 'trpc-server']
projects = ['apps-server', 'apps-web', 'apps-mobile', 'packages-client-runtime', 'packages-shared']


def records(text: str, effect_only: bool = False) -> list[tuple[str, ...]]:
    """Keep each diagnostic header with its complete indented message chain."""
    diagnostics = []
    current = None
    for line in text.splitlines():
        header = re.search(r'(?:error|warning|message|suggestion) TS(\d+):', line)
        if header:
            current = [line] if not effect_only or header[1].startswith('377') else None
            if current is not None:
                diagnostics.append(current)
        elif current is not None and line.startswith((' ', '\t')):
            current.append(line)
        else:
            current = None
    return sorted(tuple(diagnostic) for diagnostic in diagnostics)


def compare(results: Path, stem: str, effect_only: bool = False) -> None:
    def diagnostics(tool: str) -> list[tuple[str, ...]]:
        return sorted(record for stream in ['stdout', 'stderr']
                      for record in records((results / f'{stem}.{tool}.{stream}').read_text(), effect_only))
    rust, go = diagnostics('tsc-rs'), diagnostics('tsc7')
    if rust != go:
        raise SystemExit(f'{stem}: Rust/Go diagnostics differ; see saved preflight output')
    print(f'{stem}: MATCH ({len(rust)} diagnostics)')


if __name__ == '__main__':
    results = Path(sys.argv[1]) / 'results'
    for app in apps:
        compare(results, app)
    for project in projects:
        compare(results, f't3-{project}-noeffect')
        # effect-tsgo has its own TypeScript pin. Compare its Effect rules only;
        # the plain pinned TypeScript comparison above covers TypeScript errors.
        compare(results, f't3-{project}-effect', effect_only=True)
