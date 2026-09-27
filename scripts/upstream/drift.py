#!/usr/bin/env python3
"""Upstream drift: which Rust code in crates/ts_goport each upstream Go change touches.

usage: drift.py O N --out DIR [--repo PATH] [--subdir SUBDIR] [--hold OWNER=PATTERN]...

O and N are commits in --repo (default: the current pin's goCheckout in UPSTREAM.json).
The tool reads git objects only, never a working tree. --subdir is the Go root in the repo:
'' for microsoft/typescript-go (default), 'tsc' for microsoft/TypeScript. The new module path
github.com/microsoft/TypeScript/tsc is read as github.com/microsoft/typescript-go.

The Go-to-Rust map comes from the Rust sources: a leading comment that names a Go file
(optionally "lines A-B" or "lines A to B"), and `// Go: <file>.go:<line> <Name>` markers.
A changed Go declaration maps to the Rust functions whose marker names it.

--hold OWNER=PATTERN marks items that must wait. PATTERN is a crate-relative Rust path glob
(src/checker/**) or lane:<name>. Repeat it for each pattern.

Writes into DIR:
  queue.tsv       one row per upstream commit in O..N, oldest first
  rust-drift.tsv  one row per Rust file that the net O..N change reaches
  lanes/<lane>.md one work list per lane, in upstream order, with the PR, the Go files and
                  the Rust functions to update. Items with no lane are in lanes/other.md.
"""
import argparse
import collections
import fnmatch
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CRATE = REPO / 'crates/ts_goport'
LANES = [
    ('checker', {'checker', 'binder', 'evaluator', 'nodebuilder', 'pseudochecker', 'diagnostics', 'jsnum'}),
    ('syntax', {'ast', 'scanner', 'parser', 'astnav'}),
    ('emit', {'printer', 'transformers', 'sourcemap', 'outputpaths'}),
    ('program', {'compiler', 'module', 'modulespecifiers', 'tsoptions', 'tspath', 'vfs', 'bundled', 'packagejson',
                 'core', 'collections', 'stringutil', 'json', 'symlinks', 'semver', 'nativepath', 'osutil', 'locale',
                 'diagnosticwriter', 'repo', 'glob', 'tracing', 'debug'}),
    ('contentmapper', {'contentmapper', 'spanmap', 'transpile'}),
    ('build', {'execute', 'cmd'}),
    ('ls', {'ls', 'format'}),
    ('server', {'lsp', 'project', 'fswatch', 'jsonrpc'}),
    ('api', {'api', 'ipc'}),
]
LANE_OF = {pkg: lane for lane, pkgs in LANES for pkg in pkgs}


def git(*args, repo):
    return subprocess.run(['git', '-C', str(repo), *args], check=True, capture_output=True, text=True).stdout


class Blobs:
    """Reads `<rev>:<path>` through one `git cat-file --batch` process. Missing -> None."""

    def __init__(self, repo):
        self.p = subprocess.Popen(['git', '-C', str(repo), 'cat-file', '--batch'], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE)

    def read(self, rev, path):
        self.p.stdin.write(f'{rev}:{path}\n'.encode())
        self.p.stdin.flush()
        head = self.p.stdout.readline().split()
        if head[-1] == b'missing':
            return None
        data = self.p.stdout.read(int(head[2]))
        self.p.stdout.read(1)
        return data.decode('utf-8', 'replace').replace('github.com/microsoft/TypeScript/tsc', 'github.com/microsoft/typescript-go')


# ---- Go side ----

def kind_of(path):
    """prod | gen | test | harness | baseline | testdata | other, for a Go-root-relative path."""
    if path.startswith('testdata/baselines/reference/'):
        return 'baseline'
    if path.startswith('testdata/'):
        return 'testdata'
    if not path.endswith('.go') or not path.startswith(('internal/', 'cmd/')):
        return 'other'
    if path.endswith('_test.go') or '/fourslash/tests/' in path:
        return 'test'
    if path.startswith(('internal/fourslash/', 'internal/testutil/', 'internal/testrunner/')):
        return 'harness'
    if path.endswith('_generated.go') or 'stringer' in path:
        return 'gen'
    return 'prod'


def package_of(path):
    parts = path.split('/')
    return 'cmd' if parts[0] == 'cmd' else parts[1]


FUNC = re.compile(r'^func (?:\((?:\w+ )?\*?(\w+)(?:\[[^\]]*\])?\) )?(\w+)')
TOP = re.compile(r'^(type|var|const) (\w+)')


def decls(text):
    """Top-level Go declarations: key -> (body md5, first line, last line). Methods are Recv.Name."""
    out, lines, i = {}, (text or '').split('\n'), 0
    while i < len(lines):
        line = lines[i]
        m, t = FUNC.match(line), TOP.match(line)
        if m or t:
            j = i
            if line.rstrip().endswith(('{', '(')):
                j = i + 1
                while j < len(lines) and not lines[j].startswith(('}', ')')):
                    j += 1
            key = (m[1] + '.' if m and m[1] else '') + (m[2] if m else t[2])
        elif line.startswith(('type (', 'var (', 'const (')):
            j = i + 1
            while j < len(lines) and not lines[j].startswith(')'):
                j += 1
            first = next((x.split()[0] for x in lines[i + 1:j] if x.strip() and not x.strip().startswith('//')), '?')
            key = line.split()[0] + '(' + first
        else:
            i += 1
            continue
        out[key] = (hashlib.md5('\n'.join(lines[i:j + 1]).encode()).hexdigest(), i + 1, j + 1)
        i = j + 1
    return out


def decl_changes(old, new):
    do, dn = decls(old), decls(new)
    changed = [k for k in do if k in dn and do[k][0] != dn[k][0]]
    return changed, [k for k in dn if k not in do], [k for k in do if k not in dn], do


HUNK = re.compile(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@')


def hunks(old, new):
    """[(old start, old count, lines changed)] of a -U0 diff."""
    with tempfile.TemporaryDirectory() as d:
        a, b = Path(d, 'a'), Path(d, 'b')
        a.write_text(old or '')
        b.write_text(new or '')
        out = subprocess.run(['git', 'diff', '--no-index', '-U0', str(a), str(b)], capture_output=True, text=True).stdout
    res = []
    for line in out.split('\n'):
        m = HUNK.match(line)
        if m:
            oc, nc = int(m[2] if m[2] is not None else 1), int(m[4] if m[4] is not None else 1)
            res.append((int(m[1]), oc, oc + nc))
    return res


def changed_files(repo, a, b, subdir):
    """[(status, old path, new path, added, deleted)] between two commits, Go-root-relative."""
    pre = subdir.rstrip('/') + '/' if subdir else ''
    spec = [pre] if pre else []
    names = git('diff-tree', '-r', '-M', '-z', '--name-status', a, b, '--', *spec, repo=repo).split('\0')
    stats = git('diff-tree', '-r', '-M', '-z', '--numstat', a, b, '--', *spec, repo=repo).split('\0')
    rows, i = [], 0
    while i < len(names) - 1:
        st = names[i][0]
        if st in 'RC':
            old, new, i = names[i + 1], names[i + 2], i + 3
        else:
            old = new = names[i + 1]
            i += 2
        rows.append([st, None if st == 'A' else old[len(pre):], None if st == 'D' else new[len(pre):]])
    k = 0
    for row in rows:
        add, dele = stats[k].split('\t')[:2]
        k += 3 if row[0] in 'RC' else 1
        row += [0 if add == '-' else int(add), 0 if dele == '-' else int(dele)]
    return rows


# ---- Rust side ----

MARK = re.compile(r'// Go: ([\w./-]+\.go):(\d+) (\S+)')
HEADER_GO = re.compile(r'`?((?:internal/|cmd/)?(?:[\w-]+/)+[\w-]+\.go)`?(?:[^\n]*?\blines? (\d+)\s*(?:-|to|–|\.\.)\s*(\d+))?')


def go_path(p):
    return p if p.startswith(('internal/', 'cmd/')) else 'internal/' + p


def rust_index():
    """markers: (go file, name) -> ['rs:line name']; by_base: (go base name, name) -> same;
    headers: go file -> [(rust file, start, end)] (start/end None when the header gives no lines)."""
    markers, by_base, headers = collections.defaultdict(list), collections.defaultdict(list), collections.defaultdict(list)
    for base in ('src', 'tests'):
        for path in sorted((CRATE / base).rglob('*.rs')):
            rel = str(path.relative_to(CRATE))
            text = path.read_text(errors='replace').split('\n')
            for n, line in enumerate(text, 1):
                m = MARK.search(line)
                if m:
                    # Marker names: Name, Recv.Name, (*Recv).Name, Name(...).
                    full = re.sub(r'^\(\*?(\w+)(?:\[[^\]]*\])?\)', r'\1', m[3]).split('(')[0]
                    loc = f'{rel}:{n} {full}'
                    for name in {full, full.rsplit('.', 1)[-1]}:
                        markers[(go_path(m[1]), name)].append(loc)
                        by_base[(m[1].rsplit('/', 1)[-1], name)].append(loc)
            for line in text[:60]:
                s = line.strip()
                if s and not s.startswith(('//', '/*', '*')):
                    break
                for m in HEADER_GO.finditer(s):
                    entry = (rel, int(m[2]) if m[2] else None, int(m[3]) if m[3] else None)
                    if entry not in headers[go_path(m[1])]:
                        headers[go_path(m[1])].append(entry)
    return markers, by_base, headers


class Mapper:
    def __init__(self):
        self.markers, self.by_base, self.headers = rust_index()
        self.home = {}
        for (gofile, _), locs in self.markers.items():
            for loc in locs:
                self.home.setdefault(gofile, collections.Counter())[loc.split(':')[0]] += 1

    def decl(self, gofile, key):
        """Rust 'file:line name' locations whose marker names this Go declaration (Recv.Name first)."""
        base = gofile.rsplit('/', 1)[-1]
        for name in (key, key.split('.')[-1].split('(')[-1]):
            hits = self.markers.get((gofile, name)) or self.by_base.get((base, name))
            if hits:
                return sorted(set(hits))
        return []

    def files_for(self, gofile, line=None):
        """Rust files for a Go file (and line): ranged header, then plain header, then marker home."""
        heads = self.headers.get(gofile, [])
        if line is not None:
            hit = [r for r, a, b in heads if a is not None and a <= max(line, 1) <= b]
            if hit:
                return hit[:1]
        plain = [r for r, a, _ in heads if a is None]
        if plain:
            return plain[:1]
        if gofile in self.home:
            return [self.home[gofile].most_common(1)[0][0]]
        return [heads[0][0]] if heads else []


# ---- report ----

FEAT = {'add', 'adds', 'implement', 'port', 'support', 'expose', 'feat', 'introduce', 'enable', 'generate', 'allow',
        'content', 'completion', 'new', 'auto-import'}
REF = {'refactor', 'move', 'rename', 'remove', 'delete', 'cleanup', 'clean', 'simplify', 'inline', 'reduce', 'speed',
       'optimize', 'cache', 'parallelize', 'decouple', 'drop', 'split', 'replace', 'unify', 'reuse', 'make', 'switch',
       'convert', 'perf', 'lazily', 'lazy', 'build', 'bump', 'update', 'upgrade', 'chore'}
PERF = re.compile(r'\b(perf|faster|speed|alloc|quadratic|memory|wasted work|fast path|lazily|parallel|concurren)', re.I)


def kind(subject, files):
    kinds = {f['kind'] for f in files}
    if not kinds & {'prod', 'gen'}:
        return 'test/baseline only' if kinds & {'test', 'harness', 'baseline', 'testdata'} else 'infra/tooling only'
    prefix = re.match(r'^\s*([a-z]+)(\([^)]*\))?:', subject, re.I)
    word = (re.sub(r'^\s*(\[[^\]]*\]\s*|[a-z]+(\([^)]*\))?:\s*|API:\s*)', '', subject, flags=re.I).split() or [''])[0]
    word = word.lower().strip('`')
    if prefix and prefix[1].lower() == 'fix':
        return 'bug fix'
    if prefix and prefix[1].lower() == 'feat' or word in FEAT:
        return 'feature'
    if prefix and prefix[1].lower() in ('perf', 'refactor', 'chore') or PERF.search(subject) or word in REF:
        return 'refactor/perf'
    return 'bug fix'


def pr_of(subject, new_repo):
    m = re.search(r'\((?:microsoft/(typescript-go|TypeScript))?#(\d+)\)\s*$', subject)
    if not m:
        return '', ''
    repo = m[1] or ('TypeScript' if new_repo else 'typescript-go')
    tag = ('tsgo#' if repo == 'typescript-go' else 'ts#') + m[2]
    return tag, f'https://github.com/microsoft/{repo}/pull/{m[2]}'


class Holds:
    def __init__(self, specs):
        self.paths, self.lanes = [], {}
        for spec in specs:
            owner, _, pattern = spec.partition('=')
            if not owner or not pattern:
                sys.exit(f'--hold wants OWNER=PATTERN, got {spec!r}')
            if pattern.startswith('lane:'):
                self.lanes[pattern[5:]] = owner
            else:
                self.paths.append((owner, pattern))

    def path(self, rust_file):
        return next((o for o, p in self.paths if fnmatch.fnmatchcase(rust_file, p)), None)

    def item(self, lanes, rust_files):
        """{owner: [reasons]} for one item."""
        held = collections.defaultdict(list)
        for lane in lanes:
            if lane in self.lanes:
                held[self.lanes[lane]].append(f'lane {lane}')
        for f in sorted(rust_files):
            owner = self.path(f)
            if owner:
                held[owner].append(f)
        return held


def analyze(args):
    repo, sub = Path(args.repo), args.subdir
    new_repo = bool(sub)
    blobs = Blobs(repo)
    pre = sub.rstrip('/') + '/' if sub else ''
    o = git('rev-parse', '--verify', args.old + '^{commit}', repo=repo).strip()
    n = git('rev-parse', '--verify', args.new + '^{commit}', repo=repo).strip()
    log = git('log', '--reverse', '--format=%H%x09%cs%x09%s', f'{o}..{n}', '--', *([pre] if pre else []), repo=repo)
    mapper, holds = Mapper(), Holds(args.hold)
    alias = {}  # path at a later commit -> path at O, for renames inside the range
    items = []
    for idx, row in enumerate(filter(None, log.split('\n')), 1):
        sha, date, subject = row.split('\t', 2)
        files = []
        for st, old, new, add, dele in changed_files(repo, sha + '^', sha, sub):
            path = new or old
            files.append({'status': st, 'old': old, 'new': new, 'add': add, 'del': dele, 'kind': kind_of(path),
                          'pkg': package_of(path) if kind_of(path) in ('prod', 'gen') else None})
            if st == 'R':
                alias[new] = alias.get(old, old)
        prod = [f for f in files if f['kind'] in ('prod', 'gen')]
        lane_lines = collections.Counter()
        for f in prod:
            lane_lines[LANE_OF.get(f['pkg'], 'other:' + f['pkg'])] += f['add'] + f['del']
        funcs, new_decls, new_files, unmapped, rust_files = [], [], [], [], set()
        for f in prod:
            at_o = alias.get(f['old'], f['old']) if f['old'] else None
            if f['kind'] == 'gen':
                targets = mapper.files_for(at_o) if at_o else []
                rust_files.update(targets)
                funcs.append((f['new'] or f['old'], None, 'generated: regenerate ' + (' '.join(targets) or '(no Rust file)')))
                continue
            if f['status'] == 'A':
                new_files.append(f['new'])
                continue
            changed, added, removed, _ = decl_changes(blobs.read(sha + '^', pre + f['old']),
                                                       blobs.read(sha, pre + f['new']) if f['new'] else '')
            hit = missed = False
            for key in changed + removed:
                locs = mapper.decl(at_o, key)
                if locs:
                    hit = True
                    for loc in locs:
                        rust_files.add(loc.split(':')[0])
                        funcs.append((at_o, key, loc + (' (removed upstream)' if key in removed else '')))
                else:
                    missed = True
                    where = ' '.join(mapper.files_for(at_o)) or 'no Rust file'
                    funcs.append((at_o, key, f'{where} (no marker)' + (' (removed upstream)' if key in removed else '')))
            home = mapper.files_for(at_o)
            for key in added:
                new_decls.append((f['new'], key, home[0] if home else None))
            if home and (added or missed or not hit):
                rust_files.update(home)
            if not home and not hit:
                unmapped.append(at_o)
        lanes = sorted(lane_lines)
        items.append({
            'n': idx, 'sha': sha, 'date': date, 'subject': subject, 'pr': pr_of(subject, new_repo), 'files': files,
            'kind': kind(subject, files), 'lanes': lanes,
            'owner': lane_lines.most_common(1)[0][0] if len(lanes) > 1 else (lanes[0] if lanes else ''),
            'go_add': sum(f['add'] for f in prod if f['kind'] == 'prod'),
            'go_del': sum(f['del'] for f in prod if f['kind'] == 'prod'),
            'cc_baselines': sum(1 for f in files if f['kind'] == 'baseline' and re.search(
                r'/reference/(submodule\w*/)?(compiler|conformance)/', (f['new'] or f['old']))),
            'funcs': funcs, 'new_decls': new_decls, 'new_files': new_files, 'unmapped': unmapped,
            'rust_files': sorted(rust_files), 'held': holds.item(lanes, rust_files),
        })
    net = net_drift(repo, blobs, pre, o, n, mapper, holds)
    return {'old': o, 'new': n, 'items': items, 'net': net}


def net_drift(repo, blobs, pre, o, n, mapper, holds):
    """Per Rust file: Go hunks, Go lines and marked declarations that the net O..N change reaches."""
    per = collections.defaultdict(lambda: {'hunks': 0, 'lines': 0.0, 'decls': set(), 'go': set(), 'lanes': set()})
    for st, old, new, add, dele in changed_files(repo, o, n, pre.rstrip('/')):
        path = new or old
        k = kind_of(path)
        if k not in ('prod', 'gen') or not old:
            continue
        a, b = blobs.read(o, pre + old), blobs.read(n, pre + new) if new else ''
        if a == b:
            continue
        lane = LANE_OF.get(package_of(path), 'other')
        changed, _, removed, d_old = decl_changes(a, b) if k == 'prod' else ([], [], [], {})
        spans = [(d_old[key][1], d_old[key][2], key) for key in changed + removed]
        for start, count, lines in hunks(a, b):
            end = start + max(count, 1) - 1
            keys = [key for s, e, key in spans if s <= end and start <= e]
            locs = [loc for key in keys for loc in mapper.decl(old, key)]
            targets = sorted({loc.split(':')[0] for loc in locs}) or mapper.files_for(old, start)
            for t in targets:
                per[t]['hunks'] += 1
                per[t]['lines'] += lines / len(targets)
                per[t]['go'].add(old)
                per[t]['lanes'].add(lane)
            for loc in locs:
                per[loc.split(':')[0]]['decls'].add(loc)
    return [{'rust': r, 'hunks': v['hunks'], 'lines': round(v['lines']), 'decls': len(v['decls']),
             'go': sorted(v['go']), 'lanes': sorted(v['lanes']), 'held': holds.path(r) or ''}
            for r, v in sorted(per.items(), key=lambda kv: -kv[1]['lines'])]


def held_text(held):
    return '; '.join(f'blocked on {owner} ({", ".join(reasons[:4])}{", ..." if len(reasons) > 4 else ""})'
                     for owner, reasons in held.items())


def write(res, out, o_key, n_key):
    out.mkdir(parents=True, exist_ok=True)
    with open(out / 'queue.tsv', 'w') as f:
        f.write('n\tsha\tdate\tpr\tkind\tlanes\tgo_add\tgo_del\tcc_baselines\trust_targets\theld\tsubject\n')
        for it in res['items']:
            targets = it['rust_files'] + [f'NEW:{p}' for p in it['new_files']] + [f'UNMAPPED:{p}' for p in it['unmapped']]
            f.write('\t'.join(map(str, [it['n'], it['sha'][:9], it['date'], it['pr'][0], it['kind'], ','.join(it['lanes']),
                                        it['go_add'], it['go_del'], it['cc_baselines'], ' '.join(targets),
                                        ','.join(it['held']), it['subject']])) + '\n')
    with open(out / 'rust-drift.tsv', 'w') as f:
        f.write('rust_file\tgo_hunks\tgo_lines\tmarked_decls_to_update\tlanes\theld\tgo_files\n')
        for r in res['net']:
            f.write('\t'.join(map(str, [r['rust'], r['hunks'], r['lines'], r['decls'], ','.join(r['lanes']), r['held'],
                                        ' '.join(r['go'])])) + '\n')
    lanes_dir = out / 'lanes'
    lanes_dir.mkdir(exist_ok=True)
    by_lane = collections.defaultdict(list)
    for it in res['items']:
        for lane in it['lanes'] or ['other']:
            by_lane[lane if not lane.startswith('other:') else 'other'].append(it)
    for lane in [name for name, _ in LANES] + ['other']:
        its = by_lane.get(lane, [])
        held = sum(1 for it in its if it['held'])
        sync = sum(1 for it in its if len(it['lanes']) > 1)
        lines = [f'# Lane {lane}: {o_key}..{n_key}', '',
                 f'{len(its)} items: {len(its) - held} ready, {held} blocked, {sync} sync points. Port the items in this '
                 'order, one change per upstream PR, and cite the PR. A blocked item waits for the owner of its Rust '
                 'files. A sync point changes several lanes; its owner lane (most Go lines) ports it.', '']
        for it in its:
            pr, url = it['pr']
            head = f'## {it["n"]}. ' + (f'[{pr}]({url}) ' if pr else '') + f'{it["subject"]} ({it["sha"][:9]}, {it["date"]})'
            status = held_text(it['held']) or 'ready'
            if len(it['lanes']) > 1:
                status += f'; sync point, owner {it["owner"]} (lanes {", ".join(it["lanes"])})'
            lines += [head, f'- status: {status}',
                      f'- kind: {it["kind"]}; production Go +{it["go_add"]}/-{it["go_del"]}; '
                      f'compiler/conformance baselines changed: {it["cc_baselines"]}']
            mine = [f for f in it['files'] if f['kind'] in ('prod', 'gen') and
                    (lane == 'other' or LANE_OF.get(f['pkg']) == lane)]
            if mine:
                lines.append('- Go files: ' + ', '.join(f'`{f["new"] or f["old"]}` +{f["add"]}/-{f["del"]}' +
                                                        (' (new)' if f['status'] == 'A' else '') for f in mine))
            other = collections.Counter(f['kind'] for f in it['files'] if f['kind'] not in ('prod', 'gen'))
            if other:
                lines.append('- other files: ' + ', '.join(f'{k} {v}' for k, v in sorted(other.items())))
            mine_paths = {f['old'] for f in mine} | {f['new'] for f in mine}
            funcs = [(g, key, loc) for g, key, loc in it['funcs'] if lane == 'other' or g in mine_paths
                     or any(p and p == g for p in mine_paths)]
            if funcs:
                lines.append('- Rust to update:')
                lines += [f'  - `{loc}`' + (f' (Go `{g}` {key})' if key else f' (Go `{g}`)') for g, key, loc in funcs]
            news = [(g, key, home) for g, key, home in it['new_decls'] if lane == 'other' or g in mine_paths]
            if news:
                lines.append('- new Go declarations (no Rust yet): ' + ', '.join(
                    f'`{g}` {key}' + (f' -> `{home}`' if home else '') for g, key, home in news))
            if it['unmapped']:
                lines.append('- Go files with no Rust port: ' + ', '.join(f'`{p}`' for p in it['unmapped']))
            lines.append('')
        (lanes_dir / f'{lane}.md').write_text('\n'.join(lines))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('old')
    ap.add_argument('new')
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--repo')
    ap.add_argument('--subdir', default='')
    ap.add_argument('--hold', action='append', default=[])
    args = ap.parse_args()
    if not args.repo:
        cfg = json.loads((REPO / 'UPSTREAM.json').read_text())
        args.repo = cfg['pins'][cfg['current']]['goCheckout']
    res = analyze(args)
    write(res, args.out, res['old'][:12], res['new'][:12])
    items = res['items']
    per_lane = collections.Counter(l for it in items for l in it['lanes'])
    print(f'{res["old"][:12]}..{res["new"][:12]}: {len(items)} commits, '
          f'{sum(1 for it in items if it["lanes"])} change production Go, '
          f'{sum(1 for it in items if it["held"])} blocked, {len(res["net"])} Rust files reached')
    print('lanes: ' + ', '.join(f'{k} {v}' for k, v in per_lane.most_common()))
    print(f'wrote {args.out}/queue.tsv, rust-drift.tsv, lanes/*.md')


if __name__ == '__main__':
    main()
