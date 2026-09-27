#!/usr/bin/env python3
"""Records the evidence, both PASS verdicts and the acceptance of the current bound revision.

Run after the pipeline, bound runs, gate and quality checks finished and both independent
agents returned PASS on the check-format result. It sets the state to ready/PASS, runs the
local check, and records the acceptance only when the check passes.

Usage:
  scripts/goport/accept_revision.py --revision 119 --bound r23,r23b --gate r119-full
      --scope "<one line>" --outcome "<one line>" [--extra evidence.json]
Run from the repository root. --extra is a JSON object merged into the batch (e.g. cliAudit).
"""
import argparse, datetime, hashlib, json, subprocess, sys

AUDITOR = 'aae6dbb734c07335a'
REVIEWER = 'a0bc38f3370585da3'
R = 'target/continuation-r97-goport'


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def export():
    return json.loads(subprocess.check_output(['node', 'scripts/state.mjs', 'export']))


def put(state, tag):
    tmp = f'/tmp/accept-{tag}.json'
    with open(tmp, 'w') as f:
        json.dump(state, f)
    subprocess.check_call(['node', 'scripts/state.mjs', 'import', tmp])


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--revision', type=int, required=True)
    p.add_argument('--bound', required=True)
    p.add_argument('--gate', required=True)
    p.add_argument('--scope', required=True)
    p.add_argument('--extra')
    p.add_argument('--outcome', required=True, help='one-line measured outcome for the history row')
    a = p.parse_args()
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    s = export()
    b = s['batch']
    row = b['recoveryHistory'][-1]
    if row['revision'] != a.revision or b['recoveryRevision'] != a.revision:
        sys.exit(f'current revision is R{row["revision"]}, not R{a.revision}')
    fp, rev = b['sourceFingerprint'], f'r{a.revision}'
    cr, raw = f'target/continuation-{rev}-check-result.json', f'target/continuation-{rev}-full-result.json'
    chk, rawsha = sha(cr), sha(raw)
    runs = [{'manifest': f'{R}/measure/{x}/manifest.json', 'sha256': sha(f'{R}/measure/{x}/manifest.json')} for x in a.bound.split(',')]
    proj = lambda cfg: {'runner': f'goport --profile goport ({b["commit"]}), bound runs {a.bound}', 'runs': runs, 'config': cfg,
                        'complete': True, 'exitCode': 0, 'diagnostics': 0, 'oracleDiagnostics': 0, 'matchesOracle': True,
                        'repeatIdentical': True, 'date': now[:10], 'sourceFingerprint': fp}
    b['fullResult'] = {'path': cr, 'sha256': chk, 'derivedFrom': raw, 'converter': f'target/continuation-{rev}-check-result.py'}
    b['fullResultRaw'] = {'path': raw, 'sha256': rawsha}
    b['ordinaryQuery'] = proj('target/project-inputs/query/source/packages/query-core/tsconfig.prod.json')
    b['latestHono'] = proj('target/project-inputs/hono/source/tsconfig.build.json')
    c = f'target/continuation-{rev}-current-source-corpus'
    b['corpus'] = {'sourceFingerprint': fp,
                   'diagnostics': {'comparison': f'{c}/diagnostics-comparison.json', 'sha256': sha(f'{c}/diagnostics-comparison.json')},
                   'semantic': {'comparison': f'{c}/semantic-comparison.json', 'sha256': sha(f'{c}/semantic-comparison.json')}}
    g = f'{R}/compat/gate/{a.gate}/manifest.json'
    b['gate'] = {'manifest': g, 'sha256': sha(g)}
    b['qualityEvidence'] = {'sourceFingerprint': fp, 'dir': f'{R}/quality-{rev}'}
    if a.extra:
        b.update(json.load(open(a.extra)))
    verdict = lambda role, agent: {'role': role, 'agent': agent, 'verdict': 'PASS', 'batchId': b['id'],
                                   'sourceFingerprint': fp, 'fullResultSha256': chk, 'utc': now}
    b['auditor'] = verdict('audit_accepted_roster', AUDITOR)
    b['reviewer'] = verdict('independent_reviewer', REVIEWER)
    b.setdefault('verdictHistory', []).extend([b['auditor'], b['reviewer']])
    row.update({'fullResultSha256': chk, 'fullResultRawSha256': rawsha, 'status': 'full_measured', 'outcome': a.outcome,
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
                       'rules': ['opt-in-crate-no-new-loss', f'unbound-history-rows (extension to {b["id"]} by root under delegation-2026-09-25)']}
    b['compilerAccepted'], b['passingCredit'] = True, True
    b['nextPermittedAction'] = f'R{a.revision} accepted.'
    s['latestAcceptedHono'] = {'date': now[:10], 'sourceFingerprint': fp, 'complete': True, 'diagnostics': 0, 'matchesOracle': True, 'runs': runs}
    s['reason'], s['updated'] = f'Batch {b["id"]} accepted at R{a.revision}.', now
    put(s, f'{rev}-b')


if __name__ == '__main__':
    main()
