#!/usr/bin/env python3
"""Records the evidence, both PASS verdicts and the acceptance of the current bound revision of a
goport batch (protectedSet "goport", docs/typechecker-accountability.md "Protected set").

Run after `candidate.sh side` finished (SIDE DONE) and both independent agents returned PASS on the
verdict request. It reads the side evidence in --evidence (the cache dir that `candidate.sh
verdict-request` prints): tests.json, gate.json, gate-compare.json, bound.json, lsp.json, api.json
and quality.json. The LSP and API records must compare with the base results of protectedBase and
show no lost, unrun or absent request. Every failed gate run of the source that side kept
(gate-compare-fail-<label>.json) needs a flake note for each regressed item (failed_gate_runs), or
the acceptance is refused. The batch keeps every gate run of the source in gateRuns (the failed runs
with their regressions and flake notes, then the batch gate), and the check requires the same flake
notes, so a failed run stays in the state after the acceptance. The history row and both verdicts
carry goportTestsSha256, gateSha256 and nameMapSha256 (null without a name map). It sets the state to ready/PASS, runs the local check, and
records the acceptance only when the check passes.

Usage:
  scripts/goport/accept_revision.py --revision 132 --evidence <cache dir>
      --scope "<one line>" --outcome "<one line>" [--extra evidence.json] [--profile release]
Run from the repository root. --extra is a JSON object merged into the batch (e.g. cliAudit).
--profile names the cargo profile of the bound runs (release for correctness evidence).
"""
import argparse, datetime, glob, hashlib, json, os, re, subprocess, sys, tempfile

ROOT = os.getcwd()  # the repository root (run from there)
AUDITOR = 'aae6dbb734c07335a'
REVIEWER = 'a0bc38f3370585da3'
RULE = 'goport-protected-set'


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def rel(path):
    """A path under the repository root as the state writes it (relative); others stay absolute."""
    path = os.path.abspath(path)
    return os.path.relpath(path, ROOT) if path.startswith(ROOT + '/') else path


def named(text, name, path=False):
    """True when text names name as a whole word: 'r132-full' does not match 'r132-full-2', and an item id
    does not match a longer id. With path, name may also be one segment of a path (a gate label)."""
    before, after = (r'(?<![\w.-])', r'(?![\w.-])') if path else (r'(?<![\w./-])', r'(?![\w.-]|/\w)')
    return re.search(before + re.escape(name) + after, text) is not None


def failed_gate_runs(state, rev, cache, used=None):
    """The failed gate runs of this source that candidate.sh side kept in the evidence cache
    (gate-compare-fail-<label>.json, next to gate-fail-<label>.json), oldest first. The run with label
    used (the batch's own gate, compared again) is left out. Each regressed item gets the key of a flake
    note (scripts/state record note flake-r<rev>-<name>) whose text names the item id and the run label,
    or None. The repeat-run rule: a failed run is a loss unless the reviewer accepts its flake note."""
    notes = {k: json.dumps(v) for k, v in state.items() if k.startswith(f'flake-r{rev}-')}
    runs = []
    for path in sorted(glob.glob(f'{cache}/gate-compare-fail-*.json'), key=os.path.getmtime):
        label = os.path.basename(path)[len('gate-compare-fail-'):-len('.json')]
        if label == used:
            continue
        out = json.load(open(path))
        regs = [{'id': r['id'], 'base': r['base'], 'new': r['new'], 'why': r['why'],
                 'flake': next((k for k, t in sorted(notes.items()) if named(t, r['id']) and named(t, label, True)), None)}
                for r in out['regressions']]
        runs.append({'label': label, 'manifest': out['new']['manifest'], 'sha256': out['new']['sha256'], 'compare': path,
                     'regressions': regs})
    return runs


def export():
    return json.loads(subprocess.check_output(['node', 'scripts/state.mjs', 'export']))


def put(state, tag):
    """Imports state through scripts/state.mjs. Each call writes a temp file of its own, so two runs at
    the same time (parallel sims) do not corrupt each other's import."""
    with tempfile.NamedTemporaryFile('w', prefix=f'accept-{tag}-', suffix='.json') as f:
        json.dump(state, f)
        f.flush()
        subprocess.check_call(['node', 'scripts/state.mjs', 'import', f.name])


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--revision', type=int, required=True)
    p.add_argument('--evidence', required=True, help='evidence cache dir of candidate.sh side')
    p.add_argument('--scope', required=True)
    p.add_argument('--extra')
    p.add_argument('--outcome', required=True, help='one-line measured outcome for the history row')
    p.add_argument('--profile', default='release', help='cargo profile of the bound runs')
    a = p.parse_args()
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    s = export()
    b = s['batch']
    row = b['recoveryHistory'][-1]
    if row['revision'] != a.revision or b['recoveryRevision'] != a.revision:
        sys.exit(f'current revision is R{row["revision"]}, not R{a.revision}')
    if b.get('protectedSet') != 'goport':
        sys.exit(f'batch {b["id"]} is not a goport batch (protectedSet "goport"); the legacy roster is retired')
    fp, rev, C = b['sourceFingerprint'], f'r{a.revision}', os.path.abspath(a.evidence)
    ev = {}
    for k in ('tests', 'gate', 'gate-compare', 'bound', 'lsp', 'api', 'quality'):
        if not os.path.exists(f'{C}/{k}.json'):
            sys.exit(f'missing {C}/{k}.json: run candidate.sh side to SIDE DONE first')
        ev[k] = json.load(open(f'{C}/{k}.json'))
    tests, gate, gc, bound, lsp, api, quality = (ev[k] for k in ('tests', 'gate', 'gate-compare', 'bound', 'lsp', 'api', 'quality'))
    base = b['protectedBase']
    problems = []
    if os.path.realpath(tests['base']) != os.path.realpath(base['tests']['path']) or tests['baseSha256'] != base['tests']['sha256']:
        problems.append(f"tests.json base {tests['base']} is not the protected base {base['tests']['path']}")
    if os.path.realpath(gc['base']['manifest']) != os.path.realpath(base['gate']['path']):
        problems.append(f"gate-compare base {gc['base']['manifest']} is not the protected base {base['gate']['path']}")
    if any(tests['compare'][k] for k in ('lost', 'absent', 'unrun')) or gc['counts']['regressions']:
        problems.append('tests.json or gate-compare.json reports a loss or a regression')
    for name, x, ref in (('lsp', lsp, base.get('lsp')), ('api', api, base.get('api'))):
        if not ref or os.path.realpath(x['base']['dir']) != os.path.realpath(ref['dir']):
            problems.append(f"{name}.json base {x['base']['dir']} is not the protected base {(ref or {}).get('dir')}")
        if any(x['compare'][k] for k in ('lost', 'absent', 'unrun')):
            problems.append(f'{name}.json reports lost, unrun or absent requests')
    if quality.get('keptCrateWarnings', 0) or quality['tsGoportWarnings']:
        problems.append('quality.json reports clippy warnings')
    if bound.get('sourceFingerprint') != fp or quality.get('sourceFingerprint') != fp:
        problems.append(f'bound runs or quality record another source than {fp[:12]}')
    for k, c in (('tests', tests['commit']), ('gate', gate['commit'])):
        if not b['commit'].startswith(c[:9]) and not c.startswith(b['commit']):
            print(f'note: {k} evidence ran on commit {c[:9]}, the batch commit is {b["commit"][:9]} (same crates tree)')
    fruns = failed_gate_runs(s, a.revision, C, gate['label'])
    for run in fruns:
        for r in run['regressions']:
            if not r['flake']:
                problems.append(f"failed gate run {run['label']}: {r['id']} {r['base']} -> {r['new']} ({r['why']}) has no flake note "
                                f"flake-r{a.revision}-<name> that names {r['id']} and {run['label']}")
    if problems:
        sys.exit('refused:\n  ' + '\n  '.join(problems))

    runs = [{'manifest': rel(m), 'sha256': sha(m)} for m in bound['manifests']]
    proj = lambda cfg: {'runner': f'goport --profile {a.profile} ({b["commit"]}), bound runs {",".join(bound["rounds"])}', 'runs': runs,
                        'config': cfg, 'complete': True, 'exitCode': 0, 'diagnostics': 0, 'oracleDiagnostics': 0, 'matchesOracle': True,
                        'repeatIdentical': True, 'date': now[:10], 'sourceFingerprint': fp}
    b['ordinaryQuery'] = proj('target/project-inputs/query/source/packages/query-core/tsconfig.prod.json')
    b['latestHono'] = proj('target/project-inputs/hono/source/tsconfig.build.json')
    b['goportTests'] = {'results': rel(tests['results']), 'sha256': tests['sha256'], 'base': base['tests']['path'],
                        'baseSha256': base['tests']['sha256'], 'compare': tests['compare'],
                        'nameMap': tests.get('nameMap'), 'testbin': rel(tests['testbin']), 'commit': tests['commit'],
                        'compareOutput': {'path': rel(tests['compareOutput']), 'sha256': sha(tests['compareOutput'])}}
    b['gate'] = {'manifest': rel(gate['manifest']), 'sha256': gate['sha256']}
    b['gateCompare'] = {'base': base['gate']['path'], 'baseSha256': base['gate']['sha256'], 'new': rel(gate['manifest']),
                        'sha256': gate['sha256'], 'regressions': gc['counts']['regressions'],
                        'knownOpen': [f"{k['id']} growth {k['growth']:.2f} (cap {k['cap']:.2f}, base {k['baseGrowth']:.2f})"
                                      for k in gc['knownOpen']],
                        'output': {'path': rel(f'{C}/gate-compare.json'), 'sha256': sha(f'{C}/gate-compare.json')}}
    # Every gate run of the source, oldest first, the batch gate last (repeat-run rule). The check reads
    # it, requires each kept gate-compare-fail-<label>.json in it and a flake note for each regression.
    gate_run = lambda label, manifest, digest, compare, regs: {
        'label': label, 'manifest': rel(manifest), 'sha256': digest, 'compare': {'path': rel(compare), 'sha256': sha(compare)},
        'regressions': regs}
    b['gateRuns'] = [gate_run(r['label'], r['manifest'], r['sha256'], r['compare'], r['regressions']) for r in fruns] + [
        gate_run(gate['label'], gate['manifest'], gate['sha256'], f'{C}/gate-compare.json', [])]
    b['gateVerdict'] = {'label': gate['label'], 'verdict': gate['verdict'], 'host': gate['host'], 'counts': gate['counts'],
                        'failing': [f"{f['id']} {f['detail']}" for f in gate['failing']]}
    oracle = lambda x: {'label': x['label'], 'summary': rel(x['summary']), 'dir': rel(x['resultsDir']), 'host': x.get('host'),
                        'result': f"{x['requests']:,} requests: {x['same']:,} same, {x['diff']} diff, {x['crash']} crash, "
                                  f"{x['timeout']} timeout, {x['goportError']} goport_error",
                        'base': {'label': x['base']['label'], 'dir': rel(x['base']['dir'])}, 'compare': x['compare'],
                        'output': {'path': rel(x['compareOutput']), 'sha256': sha(x['compareOutput'])}}
    b['languageServerOracle'], b['apiOracle'] = oracle(lsp), oracle(api)
    b['quality'] = {'record': rel(f'{C}/quality.json'),
                    'result': f"rustfmt {quality['rustfmtExit']}, clippy {quality['clippyExit']}, {quality['tsGoportWarnings']} "
                              f"ts_goport warnings, {quality.get('keptCrateWarnings', 0)} kept crate warnings, "
                              f"fingerprint unchanged {quality['fingerprintUnchanged']}"}
    b['qualityEvidence'] = {'sourceFingerprint': fp, 'dir': rel(C)}
    if a.extra:
        b.update(json.load(open(a.extra)))
    # The three evidence hashes that the check binds in the history row and both verdicts.
    hashes = {'goportTestsSha256': tests['sha256'], 'gateSha256': gate['sha256'],
              'nameMapSha256': (tests.get('nameMap') or {}).get('sha256')}
    verdict = lambda role, agent: {'role': role, 'agent': agent, 'verdict': 'PASS', 'batchId': b['id'], 'sourceFingerprint': fp,
                                   **hashes, 'utc': now}
    b['auditor'] = verdict('audit_accepted_roster', AUDITOR)
    b['reviewer'] = verdict('independent_reviewer', REVIEWER)
    b.setdefault('verdictHistory', []).extend([b['auditor'], b['reviewer']])
    row.update({**hashes, 'status': 'full_measured', 'outcome': a.outcome,
                'ordinaryQuery': 'complete, 0 diagnostics, matches tsgo-oracle', 'hono': 'complete, 0 diagnostics, matches tsgo-oracle'})
    s['status'], s['decision'], s['updated'] = 'ready', 'PASS', now
    put(s, f'{rev}-a')
    check = subprocess.run(['node', 'scripts/check-typechecker-batch.mjs', 'docs/typechecker-state'], capture_output=True, text=True)
    result = json.loads(check.stdout)
    print(json.dumps({'verdict': result['verdict'], 'reasons': result['reasons']}))
    if check.returncode != 0:
        sys.exit('local check did not pass; acceptance not recorded')
    s = export()
    b = s['batch']
    b['localCheck'] = {'command': 'node scripts/check-typechecker-batch.mjs docs/typechecker-state', 'exit': 0, 'verdict': 'PASS',
                       'rule': result.get('rule'), 'ranUtc': now}
    b['acceptance'] = {'acceptedUtc': now, 'scope': a.scope, 'acceptedBy': 'root, with both independent PASS verdicts',
                       'rules': [f'{RULE} (standing, Theo 2026-09-28; base {base["batch"]} R{base["revision"]})']}
    b['compilerAccepted'], b['passingCredit'] = True, True
    b['nextPermittedAction'] = f'R{a.revision} accepted.'
    s['latestAcceptedHono'] = {'date': now[:10], 'sourceFingerprint': fp, 'complete': True, 'diagnostics': 0, 'matchesOracle': True, 'runs': runs}
    s['reason'], s['updated'] = f'Batch {b["id"]} accepted at R{a.revision}.', now
    put(s, f'{rev}-b')


if __name__ == '__main__':
    main()
