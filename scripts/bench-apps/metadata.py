#!/usr/bin/env python3
"""Save compiler identities, input revisions and runner details with the raw results."""
import hashlib
import json
import os
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

work = Path(sys.argv[1])
results = work / 'results'
results.mkdir(parents=True, exist_ok=True)


def command(*args: str, cwd: Path | None = None) -> str:
    try:
        run = subprocess.run(args, cwd=cwd, capture_output=True, text=True, check=False)
    except OSError:
        return 'unavailable (failed to launch)'
    return run.stdout.strip() if run.returncode == 0 else f'unavailable (exit {run.returncode})'


def digest(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


compiler_platform, bun_platform = {
    ('Linux', 'x86_64'): ('linux-x64', 'linux-x64'),
    ('Darwin', 'arm64'): ('darwin-arm64', 'darwin-aarch64'),
}[(platform.system(), platform.machine())]
tools = {
    'tsc-rs': Path(os.environ.get('RS_BIN', work / f'node_modules/@tsc-rs/{compiler_platform}/lib/tsc')),
    'tsc-rs-fast': Path(os.environ.get('RS_BIN', work / f'node_modules/@tsc-rs/{compiler_platform}/lib/tsc')),
    'tsc7': work / f'node_modules/@typescript/typescript-{compiler_platform}/lib/tsc',
    'bun': work / f'bun-{bun_platform}/bun',
}
metadata = {
    'date': datetime.now(timezone.utc).isoformat(),
    'source': command('git', 'rev-parse', 'HEAD'),
    'compilerTree': command('git', 'rev-parse', 'HEAD:crates/ts_goport'),
    'run': f"https://github.com/{os.environ.get('GITHUB_REPOSITORY', '')}/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}",
    'build': 'release PGO, static musl, no BOLT' if compiler_platform == 'linux-x64' else 'release PGO, no BOLT',
    'host': platform.platform(),
    'cpu': command('lscpu') if compiler_platform == 'linux-x64' else command('sysctl', 'machdep.cpu.brand_string', 'hw.ncpu', 'hw.memsize'),
    'memory': Path('/proc/meminfo').read_text() if Path('/proc/meminfo').exists() else None,
    'node': command('node', '--version'),
    'pnpm': command('pnpm', '--version'),
    'hyperfine': command('hyperfine', '--version'),
    'rust': command('rustc', '-vV'),
    'rounds': int(os.environ.get('RUNS', '5')),
    'warmups': 1,
    'tools': {name: {'version': command(str(path), '--revision' if name == 'bun' else '--version'),
                     'sha256': digest(path)} for name, path in tools.items() if path.exists()},
    'inputs': {},
    'packages': {},
}
for repo in sorted((work / 'repos').glob('*')):
    if not (repo / '.git').exists():
        continue
    locks = {str(path.relative_to(repo)): digest(path) for path in
             [repo / 'pnpm-lock.yaml', repo / 'yarn.lock', repo / 'package-lock.json'] if path.exists()}
    metadata['inputs'][repo.name] = {'commit': command('git', 'rev-parse', 'HEAD', cwd=repo), 'locks': locks}
for name in ['typescript', 'ts6', 'tsc-rs', '../effectgo/node_modules/@effect/tsgo', '../ts6effect/node_modules/@effect/language-service']:
    path = (work / name[3:] if name.startswith('../') else work / 'node_modules' / name) / 'package.json'
    if path.exists():
        package = json.loads(path.read_text())
        metadata['packages'][package['name'] + (' (ts6)' if name == 'ts6' else '')] = package['version']
for name in ['package-lock.json', 'effectgo/package-lock.json', 'ts6effect/package-lock.json']:
    path = work / name
    metadata[name] = digest(path)
build = Path(os.environ.get('RS_BIN', '/nonexistent')).parent / 'build.json'
if build.exists():
    metadata['compilerBuild'] = json.loads(build.read_text())
case = os.environ.get('BENCH_CASE')
(results / (f'metadata-{case}.json' if case else 'metadata.json')).write_text(json.dumps(metadata, indent=2) + '\n')
print(json.dumps(metadata, indent=2))
