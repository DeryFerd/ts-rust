#!/usr/bin/env python3
"""Dev-loop metrics from the Claude Code transcripts of ts-rust sessions, for one time window.

usage: scripts/audit/metrics.py --since 2026-09-28T08:00 [--until ISO] [--json]

Reads every ~/.claude/projects/-home-theo-Code-sandbox-ts-rust*/**.jsonl (main sessions and
subagents) and docs/typechecker-state/history.jsonl. Compare the output with the baseline table
in recommendations.md (window 2026-09-24 to 2026-09-28T08:00, before the dev-loop fixes).
"""
import argparse, glob, json, os, re, statistics
from datetime import datetime, timezone

PROJECTS = os.path.expanduser('~/.claude/projects/-home-theo-Code-sandbox-ts-rust')
REPO = '/home/theo/Code/sandbox/ts-rust'
POLL = re.compile(r'\b(until|while)\b[^\n]*\bdo\b[^\n]*\bsleep\b|for \w+ in[^\n]*;\s*do[^\n]*sleep|^\s*sleep \d')
FINISHED = re.compile(r'Finished `([\w-]+)` profile \[[^\]]*\] target\(s\) in ((\d+)m )?([\d.]+)s')
# A Bash call that writes outside /tmp or starts a job. Verifiers and profilers work in Bash and write a report
# only at the end, so their first Edit/Write measures their work, not their setup; the first action measures setup.
ACTION = re.compile(r"""(?<![0-9&])>{1,2}\s*(?!/dev/|/tmp/|/proc/|&)["$\w./~]|\btee\b|sed -i|open\([^)]*['"][wa]['"]|\.write_text\(|systemd-run|remote\.sh (run|job)\b|run-cargo-capped|\bcargo (build|test|run)|git worktree add|git merge\b(?!-)|git commit|git add|git push|\bstrace\b|perf (record|stat|trace)|hyperfine|/bin/tsgo\s|tsgo-oracle\s+-p|\brustfmt\b(?!.*--(check|version))""")


def ts(s):
    return datetime.fromisoformat(s.replace('Z', '+00:00')).timestamp()


def text_of(content):
    if isinstance(content, str):
        return content
    return '\n'.join(x.get('text', '') for x in content or [] if isinstance(x, dict) and x.get('type') == 'text')


def scan(path, lo, hi):
    """Tool calls ((name, input, result text, is_error, seconds)) and active time of one transcript."""
    pending, calls, first, last = {}, [], None, None
    for line in open(path, errors='replace'):
        try:
            d = json.loads(line)
        except ValueError:
            continue
        t = d.get('timestamp')
        if not t:
            continue
        t = ts(t)
        if not lo <= t <= hi:
            continue
        first, last = first or t, t
        if d.get('type') == 'assistant':
            for x in d['message'].get('content', []):
                if x.get('type') == 'tool_use':
                    pending[x['id']] = (x['name'], x.get('input', {}), t)
        elif d.get('type') == 'user' and isinstance(d['message'].get('content'), list):
            for x in d['message']['content']:
                if isinstance(x, dict) and x.get('type') == 'tool_result' and x.get('tool_use_id') in pending:
                    name, inp, t0 = pending.pop(x['tool_use_id'])
                    calls.append((name, inp, text_of(x.get('content')), bool(x.get('is_error')), t - t0))
    return calls, (last - first) if first else 0.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--since', required=True)
    ap.add_argument('--until')
    ap.add_argument('--json', action='store_true')
    a = ap.parse_args()
    lo = ts(a.since if 'T' in a.since else a.since + 'T00:00:00Z')
    hi = ts(a.until) if a.until else datetime.now(timezone.utc).timestamp()
    files = {}
    for p in glob.glob(f'{PROJECTS}*/**/*.jsonl', recursive=True):
        if os.path.basename(p) != 'journal.jsonl' and os.path.getmtime(p) >= lo:
            files.setdefault(os.path.basename(p), p)  # one copy per transcript
    m = dict(transcripts=0, subagents=0, toolCalls=0, subagentHours=0.0, pollCalls=0, shortPollCalls=0, pollHours=0.0,
             waitGuardDenials=0, goalNoAskDenials=0, askUserQuestions=0, askBlockedHours=0.0,
             rawSsh=0, rawRsync=0, remoteShRun=0, remoteShLook=0, remoteShJob=0, journalParses=0, wfstatus=0,
             facts=0, perfSh=0, candidateSh=0, hostWaits=0, acceptedRevisions=0)
    builds, first_edit, first_action = {}, [], []
    for name, path in files.items():
        calls, active = scan(path, lo, hi)
        if not calls:
            continue
        sub = '/subagents/' in path
        m['transcripts'] += 1
        m['subagents'] += sub
        m['toolCalls'] += len(calls)
        if sub:
            m['subagentHours'] += active / 3600
            edits = [i for i, c in enumerate(calls) if c[0] in ('Edit', 'Write')]
            if edits:
                first_edit.append(edits[0])
            acts = [i for i, c in enumerate(calls) if c[0] in ('Edit', 'Write') or
                    (c[0] == 'Bash' and ACTION.search(c[1].get('command', '') if isinstance(c[1], dict) else ''))]
            if acts:
                first_action.append(acts[0])
        for tool, inp, res, err, secs in calls:
            cmd = inp.get('command', '') if isinstance(inp, dict) else ''
            if tool == 'Bash' and sub and POLL.search(cmd):
                m['pollCalls'] += 1
                m['pollHours'] += secs / 3600
                # A wait cut into chunks of 2 minutes or less: one model turn per chunk.
                m['shortPollCalls'] += isinstance(inp.get('timeout'), (int, float)) and inp['timeout'] <= 120000
            m['waitGuardDenials'] += err and 'wait-guard:' in res
            # remote.sh prints one of these when a job waits for a host lock or for any free host.
            m['hostWaits'] += len(re.findall(r'remote\.sh: (?:waiting for the [\w-]+ lock|no free, quiet host)', res))
            m['goalNoAskDenials'] += err and 'goal-no-ask:' in res
            if tool == 'AskUserQuestion':
                m['askUserQuestions'] += 1
                m['askBlockedHours'] += secs / 3600
            if tool == 'Bash':
                m['rawSsh'] += bool(re.search(r'(^|[;&|(]\s*)ssh\s', cmd))
                m['rawRsync'] += bool(re.search(r'(^|[;&|(]\s*)rsync\s[^|;&]*\s[\w.-]+:/', cmd))
                m['remoteShRun'] += bool(re.search(r'remote\.sh run\b', cmd))
                m['remoteShLook'] += bool(re.search(r'remote\.sh (look|status)\b', cmd))
                m['remoteShJob'] += bool(re.search(r'remote\.sh job\b', cmd))
                m['facts'] += bool(re.search(r'goport/facts\b', cmd))
                m['journalParses'] += 'journal.jsonl' in cmd
                m['wfstatus'] += 'wfstatus' in cmd
                m['perfSh'] += bool(re.search(r'perf\.sh\b', cmd))
                m['candidateSh'] += 'candidate.sh' in cmd
                for f in FINISHED.finditer(res):
                    b = builds.setdefault(f.group(1), [0, 0.0])
                    b[0] += 1
                    b[1] += (int(f.group(3) or 0) * 60 + float(f.group(4))) / 3600
    m['shortPollsPerSubagentHour'] = round(m['shortPollCalls'] / m['subagentHours'], 2) if m['subagentHours'] else None
    m['medianCallsBeforeFirstEdit'] = statistics.median(first_edit) if first_edit else None
    m['medianCallsBeforeFirstAction'] = statistics.median(first_action) if first_action else None
    m['builds'] = {k: {'count': n, 'hours': round(h, 1)} for k, (n, h) in sorted(builds.items())}
    revs = {}
    for line in open(f'{REPO}/docs/typechecker-state/history.jsonl'):
        d = json.loads(line)
        v = d.get('value', {})
        if d.get('kind') == 'revision' and lo <= ts(d.get('recordedUtc', '1970-01-01T00:00:00Z')) <= hi:
            revs[v['revision']] = v  # the last line for a revision is its current row
    m['revisions'] = len(revs)
    m['acceptedRevisions'] = sum(v.get('status') == 'full_measured' for v in revs.values())
    # Share of subagent time spent in wait loops (job, build or host queue). 0.25 from 2026-09-28 to 10-01, 0.60 from 10-01 to 10-03.
    m['pollShare'] = round(m['pollHours'] / m['subagentHours'], 2) if m['subagentHours'] else None
    m['formatOnlyRevisions'] = sum(bool(re.search(r"format.only|rustfmt.only", v.get("hypothesis", ""), re.I)) for v in revs.values())
    m['carryForwardRevisions'] = sum(bool(v.get('rosterCarryForward')) for v in revs.values())
    for k in ('subagentHours', 'pollHours', 'askBlockedHours'):
        m[k] = round(m[k], 1)
    if a.json:
        print(json.dumps(m, indent=1))
    else:
        for k, v in m.items():
            print(f'{k:28} {v}')


if __name__ == '__main__':
    main()
