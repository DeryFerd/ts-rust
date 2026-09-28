#!/usr/bin/env python3
"""Records a new bound revision in the saved typechecker state before any measurement.

With --new-batch it first saves the current batch record under docs/typechecker-batches/,
adds it to batchRecords, opens the new batch and extends the two approved rules to it with
the same pins (root under delegation-2026-09-25, as for the earlier goport batches).
Without --new-batch it adds the revision to the current batch (refused when that batch is
already accepted).

Before any write it checks the batch checkout: fp.py must equal --fingerprint, --commit must
be HEAD, and every .rs file changed since the previous revision's commit must be rustfmt clean
(rustfmt --edition 2024). It records scripts/goport/roster_fp.py of the checkout as
batch.rosterFingerprint and as rosterFingerprint on the new history row.

Usage:
  scripts/goport/open_revision.py --revision 119 --fingerprint <sha256> --commit <sha>
      --hypothesis "<text>" --change "<text>" [--new-batch <batch-id> --origin "<text>"] [--dry-run]
Writes through scripts/state (export, then import). --dry-run runs the checks and prints the
new history row, but writes nothing. Run from the repository root.
"""
import argparse, copy, datetime, hashlib, json, os, subprocess, sys

KEEP = ['checkout', 'allowedChangedFiles', 'writerOutputDirectory', 'requiredRetained', 'phase',
        'implementer', 'inheritedExpectationMappings', 'carryForward']
RULES = ['opt-in-crate-no-new-loss', 'unbound-history-rows']
AUDITOR = {'role': 'audit_accepted_roster', 'agent': 'aae6dbb734c07335a', 'verdict': 'PENDING'}
REVIEWER = {'role': 'independent_reviewer', 'agent': 'a0bc38f3370585da3', 'verdict': 'PENDING'}


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def git(checkout, *args):
    return subprocess.check_output(['git', '-C', checkout, *args])


def first_field(script, checkout):
    """First output field of fp.py or roster_fp.py ("<sha256> <file count>")."""
    return subprocess.check_output(['python3', f'scripts/goport/{script}', checkout], text=True).split()[0]


def unformatted(checkout, base):
    """.rs files changed or added since commit base (working tree, untracked included) that
    rustfmt --edition 2024 would change. Each file is formatted alone from stdin, so the
    result does not depend on unchanged child modules."""
    names = git(checkout, 'diff', '--name-only', '-z', '--diff-filter=d', base, '--', '*.rs').split(b'\0')
    names += git(checkout, 'ls-files', '--others', '--exclude-standard', '-z', '--', '*.rs').split(b'\0')
    bad = []
    for name in sorted({n.decode() for n in names if n}):
        data = open(os.path.join(checkout, name), 'rb').read()
        run = subprocess.run(['rustfmt', '--edition', '2024', '--emit', 'stdout'], input=data, capture_output=True)
        if run.returncode != 0 or run.stdout != data:
            bad.append(name)
    return bad


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--revision', type=int, required=True)
    p.add_argument('--fingerprint', required=True)
    p.add_argument('--commit', required=True)
    p.add_argument('--hypothesis', required=True)
    p.add_argument('--change', required=True)
    p.add_argument('--new-batch')
    p.add_argument('--origin', default='')
    p.add_argument('--dry-run', action='store_true')
    a = p.parse_args()
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    s = json.loads(subprocess.check_output(['node', 'scripts/state.mjs', 'export']))
    old = s['batch']
    last = old['recoveryHistory'][-1]
    if a.revision != last['revision'] + 1:
        sys.exit(f'revision {a.revision} is not the next revision ({last["revision"] + 1})')
    if not a.new_batch and old.get('compilerAccepted') is True:
        sys.exit(f'batch {old["id"]} is accepted; open R{a.revision} with --new-batch')

    checkout = old['checkout']
    head = git(checkout, 'rev-parse', 'HEAD').decode().strip()
    if git(checkout, 'rev-parse', '--verify', f'{a.commit}^{{commit}}').decode().strip() != head:
        sys.exit(f'--commit {a.commit} is not HEAD of {checkout} ({head[:12]})')
    fp = first_field('fp.py', checkout)
    if fp != a.fingerprint:
        sys.exit(f'--fingerprint {a.fingerprint[:12]} does not match fp.py of {checkout} ({fp[:12]})')
    base = last.get('commit') or old.get('commit')
    if not base:
        sys.exit(f'R{last["revision"]} has no commit; cannot find the .rs files changed since it')
    bad = unformatted(checkout, base)
    if bad:
        sys.exit(f'rustfmt --edition 2024 would change {len(bad)} file(s) changed since {base}:\n  ' + '\n  '.join(bad))
    roster = first_field('roster_fp.py', checkout)
    previous_fp = old['sourceFingerprint']

    record = None
    if a.new_batch:
        if old.get('compilerAccepted') is not True:
            sys.exit('the current batch is not accepted; finish it before opening a new one')
        record = f"docs/typechecker-batches/{old['id']}.json"
        if os.path.exists(record):
            sys.exit(f'{record} exists')
        text = subprocess.check_output(['node', 'scripts/state.mjs', 'batch', '--with-history'])
        s['batchRecords'].append({'path': record, 'sha256': hashlib.sha256(text).hexdigest(), 'bytes': len(text)})
        b = {k: copy.deepcopy(old[k]) for k in KEEP if k in old}
        b.update({'id': a.new_batch, 'previousBatch': {'id': old['id'], 'archive': s['batchRecords'][-1]},
                  'latestHono': old.get('latestHono'), 'origin': a.origin,
                  'compilerEditsAuthorized': True, 'productionEditsAuthorized': True, 'semanticEditsAuthorized': True,
                  'testEditsAuthorized': False, 'runtimeAuthorized': True, 'expectedCompilerRecoveries': [],
                  'expectationUpdates': [], 'verdictHistory': [], 'focusedResults': [], 'runtimeToolHandles': [],
                  'commands': [], 'interruptedRuns': [], 'recoveryHistory': old['recoveryHistory']})
        for rid in RULES:
            prev = [r for r in s['acceptanceRuleChanges'] if r['id'] == rid][-1]
            r = copy.deepcopy(prev)
            r.update(batchId=a.new_batch, extendedUtc=now, extendedBy='root under delegation-2026-09-25; same pins and scope')
            s['acceptanceRuleChanges'].append(r)
        s['reason'] = f"Batch {old['id']} accepted at R{last['revision']}. Batch {a.new_batch} opened at R{a.revision}."
    else:
        b = old
        s['reason'] = f'R{a.revision} bound in batch {b["id"]}.'
    b.update({'recoveryRevision': a.revision, 'hypothesis': a.hypothesis, 'sourceFingerprint': a.fingerprint,
              'beforeEditingSourceFingerprint': previous_fp, 'sourceBindingStatus': 'SOURCE_BOUND',
              'commit': a.commit, 'rosterFingerprint': roster, 'fullResult': None, 'fullOutcome': None, 'corpus': None,
              'ordinaryQuery': None, 'completedRuns': [], 'compilerAccepted': False, 'passingCredit': False,
              'auditor': dict(AUDITOR), 'reviewer': dict(REVIEWER),
              'nextPermittedAction': f'Run the R{a.revision} pipeline.'})
    row = {'revision': a.revision, 'hypothesis': a.hypothesis, 'hypothesisLabel': b['id'].replace('recovery-continuation-', ''),
           'phase': 'recovery-continuation', 'sourceFingerprint': a.fingerprint, 'beforeEditingSourceFingerprint': previous_fp,
           'rosterFingerprint': roster, 'fullResultSha256': None, 'status': 'bound_before_full_measurement',
           'recordedUtc': now, 'commit': a.commit, 'change': a.change}
    b['recoveryHistory'] = b['recoveryHistory'] + [row]
    s['batch'] = b
    s['status'], s['decision'], s['updated'] = 'active', 'REVIEW', now
    if a.dry_run:
        print(json.dumps({'dryRun': True, 'batch': b['id'], 'batchRecord': record, 'row': row}, indent=1))
        return
    if record:
        with open(record, 'xb') as f:
            f.write(text)
    tmp = f'/tmp/open-revision-{a.revision}.json'
    with open(tmp, 'w') as f:
        json.dump(s, f)
    subprocess.check_call(['node', 'scripts/state.mjs', 'import', tmp])


if __name__ == '__main__':
    main()
