#!/usr/bin/env python3
"""Pin-aware front end for the unmodified corpus runners, as gate.sh uses them.

usage: corpus.py diag|emit SHARD --goport BIN --commit SHA --work DIR [--jobs N] [--limit N (emit)]
  diag  corpus-full/run_shard_parallel.py (tsgo-oracle vs goport diagnostics)
  emit  emit-corpus/run_emit_shard2.py    (tsgo-oracle vs goport_emit output trees)
Cases, list.json and shards come from corpus-full. Results go to DIR/results (DIR must be new).
With GOPORT_PIN set, the script re-runs itself under scripts/upstream/pin.py exec, so the
runners see the pin oracle, corpus and shards, and assert the pin oracle's sha256 instead of
their built-in one. Unset: the runners behave as they always did.
"""
import argparse
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
R = HERE.parents[1] / 'target/continuation-r97-goport'

if os.environ.get('GOPORT_PIN') and not os.environ.get('GOPORT_PIN_ACTIVE'):
    os.execvp(sys.executable, [sys.executable, str(HERE / 'pin.py'), 'exec', '--', sys.executable, *sys.argv])

ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
ap.add_argument('kind', choices=['diag', 'emit'])
ap.add_argument('shard')
ap.add_argument('--goport', required=True)
ap.add_argument('--commit', required=True)
ap.add_argument('--work', required=True, type=Path)
ap.add_argument('--jobs', default='8')
ap.add_argument('--limit')
args = ap.parse_args()
if args.limit and args.kind == 'diag':
    ap.error('--limit works with emit only')
work = args.work.resolve()
work.mkdir(parents=True)
pinned = os.environ.get('GOPORT_PIN_ORACLE_SHA256') if os.environ.get('GOPORT_PIN_ACTIVE') else None
limit = ['--limit', args.limit] if args.limit else []
if args.kind == 'diag':
    for name in ('cases', 'list.json', 'shards'):
        (work / name).symlink_to(R / 'corpus-full' / name)
    sys.path.insert(0, str(R / 'corpus-full'))
    import run_shard as rs
    import run_shard_parallel as rp
    rs.here, rs.GOPORT, rs.GOPORT_COMMIT = work, Path(args.goport), args.commit
    if pinned:
        rs.ORACLE_SHA256 = pinned
    sys.argv = ['run_shard_parallel.py', args.shard, '--jobs', args.jobs, '--results', str(work / 'results')]
    rp.main()
else:
    sys.path.insert(0, str(R / 'emit-corpus'))
    import run_emit_shard2 as es
    es.here = work
    if pinned:
        es.ORACLE_SHA256 = pinned
    sys.argv = ['run_emit_shard2.py', args.shard, '--jobs', args.jobs, '--results', str(work / 'results'),
                '--goport', args.goport, '--goport-commit', args.commit, *limit]
    es.main()
