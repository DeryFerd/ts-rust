#!/usr/bin/env python3
"""Writes the old-name map from a typescript-go layout test run to a microsoft/TypeScript (tsc/) layout run.

usage: layout-name-map.py <base results.json[.gz]> <new results.json[.gz]> --out MAP.tsv
                          [--absent FILE.tsv] [--collisions FILE] [--remove-absent]

The two files are goport-tests.sh results. The base pin must have the layout "typescript-go" and the new
pin the layout "typescript" (`pin.py show`). The map (compare-tests.py --name-map format, one explicit line
per moved or removed name) follows the upstream layout change 5f647a841a ("Apply the TypeScript 7 repository
layout"): no TypeScript submodule, TestLocal runs every case, the submodule* reference dirs are merged into
reference/<dir>, no .diff files.

  go_baselines_submodule  "<kind> submodule/<suite>/<name>"  ->  go_baselines_local "<kind> local/<suite>/<name>"
  go_baselines_transpile  "<kind> submodule/transpile/<n>"   ->  go_baselines_transpile "<kind> local/transpile/<n>"
  go_baselines_submodule_shards "compiler_runner::test_submodule <i>/4"
                                  ->  go_baselines_local_shards "compiler_runner::test_local <i>/4"
  go_baselines "compiler_runner::test_local"  ->  removed (TestLocal runs in the 4 shards)
  go_baselines_reference  "submodule/<dir>/<file>"  ->  "<dir>/<file>";
                          "*.diff" and "submoduleAccepted/..." and "submoduleTriaged/..."  ->  removed

The collisions (--collisions, default <new pin goCheckout>/testdata/promotedTestCollisions.txt) change a name:
an "identical" submodule case was merged into the local case of the same name, so its names are removed; a
"renamed-promoted" case gets its new file name (a variant suffix "(opt=value)" stays). Every other name keeps its
key. The map has a line for every base name that the rules move or remove, whatever its status, and never
maps two base names to one new name or to another base name (exit 2 if the rules would).

A mapped name that is missing from the new results is "absent" in compare-tests.py. --absent writes each such
base name with its status and a reason: the case file is not at the new pin, the case is there but not this
configuration or subtest, or the reference file is not there. --remove-absent also maps them to "-" with that
reason as the evidence (for review: the accountability rules need upstream evidence for a removed name).

Last stdout line: a summary. Exit 0, or 2 on bad input.
"""
import argparse
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PIN_PY = ROOT / 'scripts' / 'upstream' / 'pin.py'
LAYOUT = '5f647a841a layout'
# The baseline file extensions of the compiler runner (after the configured name).
REF_EXTS = ('.types', '.symbols', '.js', '.errors.txt', '.sourcemap.txt', '.js.map', '.trace.json', '.contentmapper')
SUBMODULE_COPIES = ('submoduleAccepted/', 'submoduleTriaged/')


def die(msg):
    print(f'layout-name-map.py: {msg}', file=sys.stderr)
    sys.exit(2)


def load(path):
    try:
        raw = open(path, 'rb').read()
        doc = json.loads(gzip.decompress(raw) if path.endswith('.gz') else raw)
    except (OSError, EOFError, ValueError) as err:
        die(f'{path}: {err}')
    if not isinstance(doc, dict) or not isinstance(doc.get('suites'), dict) or not isinstance(doc.get('pin'), str):
        die(f'{path}: not a goport-tests.sh results file (no "suites" or "pin")')
    return doc, hashlib.sha256(raw).hexdigest()


def pin_record(pin):
    run = subprocess.run([sys.executable, str(PIN_PY), 'show', pin], capture_output=True, text=True)
    if run.returncode != 0:
        die(f'pin.py show {pin}: {run.stderr.strip()}')
    return json.loads(run.stdout)


def load_collisions(path):
    """{(suite, old file name): new file name, or None for an identical (merged) case}."""
    out = {}
    try:
        lines = open(path, encoding='utf-8').read().splitlines()
    except OSError as err:
        die(f'{path}: {err}')
    for i, line in enumerate(lines, 1):
        f = line.split()
        if not f or f[0].startswith('#'):
            continue
        if f[0] == 'identical' and len(f) == 2:
            old, new = f[1], None
        elif f[0].startswith('renamed-promoted') and len(f) == 4 and f[2] == '->':
            old, new = f[1], f[3]
        else:
            die(f'{path}:{i}: not "identical <path>" or "renamed-promoted* <old> -> <new>"')
        suite = old.split('/', 1)[0]
        if new is not None and (new.split('/', 1)[0] != suite or os.path.dirname(new) != os.path.dirname(old)):
            die(f'{path}:{i}: the rename moves the case to another dir')
        out[(suite, os.path.basename(old))] = None if new is None else os.path.basename(new)
    return out


def split_ext(name):
    """("stem", ".ext") of a case file name: the last extension (x.d.ts: "x.d", ".ts")."""
    stem, ext = os.path.splitext(name)
    return stem, ext


class Renamer:
    def __init__(self, collisions):
        # {(suite, old stem): (old file, new stem or None)}
        self.stems = {}
        for (suite, old), new in collisions.items():
            self.stems[(suite, split_ext(old)[0])] = (old, None if new is None else split_ext(new)[0])

    def case(self, suite, cname):
        """(new configured name or None when merged, collision kind) of "<stem>[(<variant>)]<ext>"."""
        for (s, stem), (old, new_stem) in self.stems.items():
            if s != suite:
                continue
            ext = split_ext(old)[1]
            if cname == old or (cname.startswith(stem + '(') and cname.endswith(')' + ext)):
                if new_stem is None:
                    return None, 'identical'
                return new_stem + cname[len(stem):], 'renamed-promoted'
        return cname, None

    def reference(self, suite, file):
        """As case(), for a baseline file "<stem>[(<variant>)]<baseline ext>"."""
        for (s, stem), (_, new_stem) in self.stems.items():
            if s != suite or not file.startswith(stem):
                continue
            rest = file[len(stem):]
            if rest.startswith('(') or rest in REF_EXTS:
                if new_stem is None:
                    return None, 'identical'
                return new_stem + rest, 'renamed-promoted'
        return file, None


def build(base, new, renamer):
    """[(old suite, old name, new suite or None, new name or None, evidence)] for every moved or removed name."""
    lines = []
    b = base['suites']

    def subtests(suite, new_suite):
        for name in sorted(b.get(suite, {})):
            kind, _, key = name.partition(' ')
            where, _, rest = key.partition('/')
            if where != 'submodule' or '/' not in rest:
                continue
            case_suite, cname = rest.split('/', 1)
            new_cname, why = renamer.case(case_suite, cname)
            if new_cname is None:
                lines.append((suite, name, None, None,
                              f'promotedTestCollisions.txt identical: merged into local/{case_suite}/{cname}'))
                continue
            ev = f'{LAYOUT}: submodule case in testdata/tests/cases, TestLocal runs it'
            if why:
                ev += f'; promotedTestCollisions.txt {why}: {cname} -> {new_cname}'
            lines.append((suite, name, new_suite, f'{kind} local/{case_suite}/{new_cname}', ev))

    subtests('go_baselines_submodule', 'go_baselines_local')
    subtests('go_baselines_transpile', 'go_baselines_transpile')
    for name in sorted(b.get('go_baselines_submodule_shards', {})):
        m = re.fullmatch(r'compiler_runner::test_submodule (\d+/\d+)', name)
        if m:
            lines.append(('go_baselines_submodule_shards', name, 'go_baselines_local_shards',
                          f'compiler_runner::test_local {m.group(1)}',
                          f'{LAYOUT}: no TestSubmodule; TestLocal runs every case in the shards'))
    if 'compiler_runner::test_local' in b.get('go_baselines', {}):
        lines.append(('go_baselines', 'compiler_runner::test_local', None, None,
                      f'{LAYOUT}: TestLocal runs every case, in the 4 shards (go_baselines_local_shards)'))
    for path in sorted(b.get('go_baselines_reference', {})):
        if path.endswith('.diff') or path.startswith(SUBMODULE_COPIES):
            lines.append(('go_baselines_reference', path, None, None,
                          f'{LAYOUT}: no .diff baselines and no submoduleAccepted/submoduleTriaged dirs'))
            continue
        if not path.startswith('submodule/'):
            continue
        rest = path[len('submodule/'):]
        d, _, file = rest.rpartition('/')
        new_file, why = renamer.reference(d.split('/', 1)[0], file) if d else (file, None)
        if new_file is None:
            lines.append(('go_baselines_reference', path, None, None,
                          f'promotedTestCollisions.txt identical: merged into {rest}'))
            continue
        ev = f'{LAYOUT}: reference/submodule merged into reference'
        if why:
            ev += f'; promotedTestCollisions.txt {why}: {file} -> {new_file}'
        lines.append(('go_baselines_reference', path, 'go_baselines_reference', f'{d}/{new_file}' if d else new_file,
                      ev))
    # The rules must give an explicit one-to-one map (compare-tests.py rejects anything else).
    seen = {}
    for old_suite, old, suite, name, _ in lines:
        if suite is None:
            continue
        if (suite, name) in seen:
            die(f'{old_suite} {old} and {seen[(suite, name)]} both map to {suite} {name}')
        seen[(suite, name)] = f'{old_suite} {old}'
        if name in b.get(suite, {}):
            die(f'{old_suite} {old} maps to {suite} {name}, which is a base name')
    return lines


def case_files(go_checkout):
    """{(suite, file name): relative path} of the case files at a typescript-layout pin."""
    out = {}
    root = Path(go_checkout) / 'testdata' / 'tests' / 'cases'
    for d, _, names in os.walk(root):  # nothing when the checkout is not there
        for f in names:
            rel = os.path.relpath(os.path.join(d, f), root)
            out.setdefault((rel.split(os.sep, 1)[0], f), rel)
    return out


def absent_reason(suite, name, new, cases, pin):
    """Why a mapped name is missing from the new results."""
    n = new['suites']
    if suite == 'go_baselines_reference':
        return f'no reference file {name} at {pin}'
    kind, _, key = name.partition(' ')
    where, _, rest = key.partition('/')
    case_suite, _, cname = rest.partition('/')
    stem, ext = split_ext(cname)
    file = (stem.split('(', 1)[0] + ext) if cname.endswith(')' + ext) else cname
    if case_suite == 'transpile' or (case_suite, file) in cases:
        if any(k.partition(' ')[2] == key for k in n.get(suite, {})):
            return f'the {kind} subtest of {key} does not run at {pin}'
        where_file = cases.get((case_suite, file), f'transpile/{file}')
        return f'case {where_file} is at {pin}, but not the configuration {cname}'
    return f'no case file {case_suite}/**/{file} at {pin}'


def main():
    ap = argparse.ArgumentParser(description='Old-name map from a typescript-go layout run to a tsc/ layout run.')
    ap.add_argument('base')
    ap.add_argument('new')
    ap.add_argument('--out', required=True)
    ap.add_argument('--absent')
    ap.add_argument('--collisions')
    ap.add_argument('--remove-absent', action='store_true')
    a = ap.parse_args()
    base, base_sha = load(a.base)
    new, new_sha = load(a.new)
    base_rec, new_rec = pin_record(base['pin']), pin_record(new['pin'])
    if base_rec.get('layout') != 'typescript-go' or new_rec.get('layout') != 'typescript':
        die(f'base pin {base["pin"]} has layout {base_rec.get("layout")!r} and new pin {new["pin"]} '
            f'{new_rec.get("layout")!r}; want typescript-go and typescript')
    collisions = a.collisions or os.path.join(new_rec['goCheckout'], 'testdata', 'promotedTestCollisions.txt')
    col_sha = hashlib.sha256(open(collisions, 'rb').read()).hexdigest()
    lines = build(base, new, Renamer(load_collisions(collisions)))

    cases = case_files(new_rec['goCheckout'])
    incomplete = set(new.get('incomplete', []))
    absent = []
    for i, (old_suite, old, suite, name, ev) in enumerate(lines):
        if suite is None or suite in incomplete or name in new['suites'].get(suite, {}):
            continue
        reason = absent_reason(suite, name, new, cases, new['pin'])
        absent.append((old_suite, old, base['suites'][old_suite][old], suite, name, reason))
        if a.remove_absent:
            lines[i] = (old_suite, old, None, None, f'{ev}; removed upstream: {reason}')

    with open(a.out, 'w', encoding='utf-8') as f:
        f.write(f'# layout-name-map.py: base {a.base} (sha256 {base_sha}, pin {base["pin"]}), new {a.new} '
                f'(sha256 {new_sha}, pin {new["pin"]}), collisions {collisions} (sha256 {col_sha})'
                f'{", absent names removed" if a.remove_absent else ""}\n')
        f.write('oldSuite\toldName\tnewSuite\tnewName\tevidence\n')
        for old_suite, old, suite, name, ev in lines:
            f.write(f'{old_suite}\t{old}\t{suite or "-"}\t{name or "-"}\t{ev}\n')
    if a.absent:
        with open(a.absent, 'w', encoding='utf-8') as f:
            f.write('oldSuite\toldName\tbaseStatus\tnewSuite\tnewName\treason\n')
            for row in absent:
                f.write('\t'.join(row) + '\n')
    removed = sum(1 for line in lines if line[2] is None)
    print(f'{len(lines)} map lines ({removed} removed), {len(absent)} mapped names absent in new '
          f'({sum(1 for r in absent if r[2] == "ok")} of them ok in base); map {a.out}')


if __name__ == '__main__':
    main()
