#!/usr/bin/env python3
"""Records a new bound revision in the saved typechecker state before any measurement.

With --new-batch it first saves the current batch record under docs/typechecker-batches/,
adds it to batchRecords, opens the new batch and extends the two approved rules to it with
the same pins (root under delegation-2026-09-25, as for the earlier goport batches).
Without --new-batch it adds the revision to the current batch.

Usage:
  scripts/goport/open_revision.py --revision 119 --fingerprint <sha256> --commit <sha>
      --hypothesis "<text>" --change "<text>" [--new-batch <batch-id> --origin "<text>"]
Writes through scripts/state (export, then import). Run from the repository root.
"""
import argparse, copy, datetime, hashlib, json, os, subprocess, sys

KEEP = ['checkout', 'allowedChangedFiles', 'writerOutputDirectory', 'requiredRetained', 'phase',
        'implementer', 'inheritedExpectationMappings', 'carryForward']
RULES = ['opt-in-crate-no-new-loss', 'unbound-history-rows']
AUDITOR = {'role': 'audit_accepted_roster', 'agent': 'aae6dbb734c07335a', 'verdict': 'PENDING'}
REVIEWER = {'role': 'independent_reviewer', 'agent': 'a0bc38f3370585da3', 'verdict': 'PENDING'}


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--revision', type=int, required=True)
    p.add_argument('--fingerprint', required=True)
    p.add_argument('--commit', required=True)
    p.add_argument('--hypothesis', required=True)
    p.add_argument('--change', required=True)
    p.add_argument('--new-batch')
    p.add_argument('--origin', default='')
    a = p.parse_args()
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    s = json.loads(subprocess.check_output(['node', 'scripts/state.mjs', 'export']))
    old = s['batch']
    last = old['recoveryHistory'][-1]['revision']
    if a.revision != last + 1:
        sys.exit(f'revision {a.revision} is not the next revision ({last + 1})')
    if a.new_batch:
        if old.get('compilerAccepted') is not True:
            sys.exit('the current batch is not accepted; finish it before opening a new one')
        record = f"docs/typechecker-batches/{old['id']}.json"
        with open(record, 'x') as f:
            f.write(subprocess.check_output(['node', 'scripts/state.mjs', 'batch', '--with-history'], text=True))
        s['batchRecords'].append({'path': record, 'sha256': sha(record), 'bytes': os.path.getsize(record)})
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
        s['reason'] = f"Batch {old['id']} accepted at R{last}. Batch {a.new_batch} opened at R{a.revision}."
    else:
        b = old
        s['reason'] = f'R{a.revision} bound in batch {b["id"]}.'
    b.update({'recoveryRevision': a.revision, 'hypothesis': a.hypothesis, 'sourceFingerprint': a.fingerprint,
              'beforeEditingSourceFingerprint': old['sourceFingerprint'], 'sourceBindingStatus': 'SOURCE_BOUND',
              'commit': a.commit, 'fullResult': None, 'fullOutcome': None, 'corpus': None, 'ordinaryQuery': None,
              'completedRuns': [], 'compilerAccepted': False, 'passingCredit': False,
              'auditor': dict(AUDITOR), 'reviewer': dict(REVIEWER),
              'nextPermittedAction': f'Run the R{a.revision} pipeline.'})
    b['recoveryHistory'] = b['recoveryHistory'] + [{
        'revision': a.revision, 'hypothesis': a.hypothesis, 'hypothesisLabel': b['id'].replace('recovery-continuation-', ''),
        'phase': 'recovery-continuation', 'sourceFingerprint': a.fingerprint, 'beforeEditingSourceFingerprint': old['sourceFingerprint'],
        'fullResultSha256': None, 'status': 'bound_before_full_measurement', 'recordedUtc': now, 'commit': a.commit, 'change': a.change}]
    s['batch'] = b
    s['status'], s['decision'], s['updated'] = 'active', 'REVIEW', now
    tmp = f'/tmp/open-revision-{a.revision}.json'
    with open(tmp, 'w') as f:
        json.dump(s, f)
    subprocess.check_call(['node', 'scripts/state.mjs', 'import', tmp])


if __name__ == '__main__':
    main()
