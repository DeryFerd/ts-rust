#!/usr/bin/env python3
"""Upstream pin selector for the goport tooling.

UPSTREAM.json (repo root) records the typescript-go pins. The default paths hold the
current pin: the oracle ~/.local/bin/tsgo-oracle, the Go checkout
~/.explore/repos/microsoft__typescript-go and the oracle caches listed in "caches".

GOPORT_PIN=<key> selects another pin for one run. The key is the first 12 hex digits of
the commit (a unique prefix of 7 or more also works). `pin.py exec -- <command>` then
starts the command in a private mount namespace (bubblewrap, same uid, no root) where
each default path shows the pin's file or dir:
  oracle      <- pins.<key>.oracle.path   (read-only)
  goCheckout  <- pins.<key>.goCheckout    (read-only)
  each cache  <- <pinRoot>/<key>/<repo-relative path>  (a path outside the repo is under
                 <pinRoot>/<key>/_abs/<path>)
A cache dir that the pin root lacks is made empty, so a recorder that fills a missing
cache writes the pin's output there. A cache file that the pin root lacks reads as a
one-line "not recorded" marker, so a comparison fails and never uses another pin's data.
Nothing outside the namespace changes. With GOPORT_PIN unset, or set to the current
pin, the command runs unchanged (no namespace). Inside a pin run GOPORT_PIN_ACTIVE=<key>
and GOPORT_PIN_ORACLE_SHA256=<the pin oracle sha256> are set.

usage:
  pin.py show [KEY]               the pin record as JSON (default: GOPORT_PIN, else current)
  pin.py path FIELD [KEY]         oracle | goCheckout | root | commit | dumper | cache:<entry>
  pin.py exec -- COMMAND...       run COMMAND under GOPORT_PIN
  pin.py binds [KEY]              the binds that exec makes ("src -> dest [ro]")
  pin.py add COMMIT [--go GO] [--checkout DIR]
                                  old-layout commit: clone a checkout next to the default one
                                  (or use DIR), build tsgo-oracle-<key> with GOTOOLCHAIN=GO
                                  unless it exists, add the pin
  pin.py sync HOST [KEY]          copy the pin's oracle, checkout (no .git), caches and
                                  UPSTREAM.json to a remote host (same absolute paths)
"""
import glob
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CONFIG = REPO / 'UPSTREAM.json'
MARKER = '.not-recorded'


def die(msg):
    sys.exit(f'pin.py: {msg}')


def load():
    return json.loads(CONFIG.read_text())


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def resolve(cfg, value=None):
    """Pin key for value (default GOPORT_PIN, else current). Accepts a unique prefix."""
    value = (value or os.environ.get('GOPORT_PIN') or cfg['current']).strip().lower()
    if value in cfg['pins']:
        return value
    hits = [k for k, p in cfg['pins'].items() if len(value) >= 7 and p['commit'].startswith(value)]
    if len(hits) != 1:
        die(f'unknown pin {value!r}; known: {", ".join(cfg["pins"])}')
    return hits[0]


def cache_src(cfg, key, dest):
    """Pin-keyed location of a cache path."""
    dest = Path(dest)
    root = Path(cfg['pinRoot']) / key
    return root / dest.relative_to(REPO) if dest.is_relative_to(REPO) else root / '_abs' / dest.relative_to('/')


def cache_entries(cfg):
    """(dest path, is dir) for every cache entry; globs expand against the real tree."""
    for pattern in cfg['caches']:
        is_dir = pattern.endswith('/')
        path = pattern.rstrip('/')
        path = path if path.startswith('/') else str(REPO / path)
        if glob.has_magic(path):
            for hit in sorted(glob.glob(path)):
                if os.path.isdir(hit) == is_dir:
                    yield Path(hit), is_dir
        else:
            yield Path(path), is_dir


def binds(cfg, key):
    """(src, dest, read-only) for a pin run, and the cache files the pin has not recorded."""
    rec = cfg['pins'][key]
    out = [(Path(rec['oracle']['path']), Path(cfg['defaults']['oracle']), True),
           (Path(rec['goCheckout']), Path(cfg['defaults']['goCheckout']), True)]
    missing, marker = [], Path(cfg['pinRoot']) / key / MARKER
    for dest, is_dir in cache_entries(cfg):
        src = cache_src(cfg, key, dest)
        if is_dir:
            if not dest.exists():
                if not dest.parent.is_dir():
                    continue
                dest.mkdir()
            src.mkdir(parents=True, exist_ok=True)
            out.append((src, dest, False))
        elif dest.exists():
            if src.exists():
                out.append((src, dest, False))
            else:
                marker.parent.mkdir(parents=True, exist_ok=True)
                if not marker.exists():
                    marker.write_text(f'not recorded for upstream pin {key}\n')
                out.append((marker, dest, True))
                missing.append(dest)
    return out, missing


def cmd_exec(argv):
    if argv[:1] == ['--']:
        argv = argv[1:]
    if not argv:
        die('exec needs a command')
    want, active = os.environ.get('GOPORT_PIN', '').strip(), os.environ.get('GOPORT_PIN_ACTIVE', '')
    if not want:
        os.execvp(argv[0], argv)
    cfg = load()
    key = resolve(cfg, want)
    if active:
        if active != key:
            die(f'GOPORT_PIN={want} inside a run of pin {active}; pins do not nest')
        os.execvp(argv[0], argv)
    rec = cfg['pins'][key]
    env = dict(os.environ, GOPORT_PIN_ACTIVE=key, GOPORT_PIN_ORACLE_SHA256=rec['oracle']['sha256'])
    if key == cfg['current']:
        os.execvpe(argv[0], argv, env)
    for need in (rec['oracle']['path'], rec['goCheckout']):
        if not os.path.exists(need):
            die(f'pin {key}: missing {need} (pin.py sync <host> {key} copies it to a remote host)')
    if sha256(rec['oracle']['path']) != rec['oracle']['sha256']:
        die(f'pin {key}: {rec["oracle"]["path"]} does not match the recorded sha256')
    todo, missing = binds(cfg, key)
    args = ['bwrap', '--dev-bind', '/', '/']
    for src, dest, ro in todo:
        args += ['--ro-bind' if ro else '--bind', str(src), str(dest)]
    note = f'; {len(missing)} cache files not recorded, e.g. {missing[0]}' if missing else ''
    print(f'goport pin {key} ({rec["commit"][:9]}): {len(todo)} binds{note}', file=sys.stderr)
    os.execvpe('bwrap', args + ['--chdir', os.getcwd(), '--', *argv], env)


def cmd_path(field, key=None):
    cfg = load()
    key = resolve(cfg, key)
    rec = cfg['pins'][key]
    if field.startswith('cache:'):
        entry = field[6:].rstrip('/')
        print(cache_src(cfg, key, entry if entry.startswith('/') else REPO / entry))
        return
    value = {'oracle': rec['oracle']['path'], 'goCheckout': rec['goCheckout'], 'commit': rec['commit'],
             'root': str(Path(cfg['pinRoot']) / key), 'dumper': rec.get('typesymDumper', {}).get('path')}
    if field not in value:
        die(f'unknown field {field}')
    if value[field] is None:
        die(f'pin {key} has no {field}')
    print(value[field])


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], check=True, capture_output=True, text=True).stdout.strip()


def cmd_add(commit, go='go1.26.4', checkout=None):
    """Adds an old-layout (microsoft/typescript-go) commit: checkout, TypeScript submodule, oracle."""
    cfg = load()
    base = Path(cfg['defaults']['goCheckout'])
    full = git(base, 'rev-parse', '--verify', f'{commit}^{{commit}}')
    key = full[:12]
    if key in cfg['pins']:
        die(f'pin {key} exists')
    dest = Path(checkout or f'{base}@{key}')
    sub = git(base, 'rev-parse', f'{full}:_submodules/TypeScript')
    if not dest.exists():
        # Local clones hardlink the objects. The default checkout is only read. --no-checkout
        # leaves an empty index, so the checkouts need --force to write every file.
        subprocess.run(['git', 'clone', '--quiet', '--local', '--no-checkout', str(base), str(dest)], check=True)
        git(dest, 'checkout', '--quiet', '--force', '--detach', full)
        subprocess.run(['git', 'clone', '--quiet', '--local', '--no-checkout',
                        str(base / '.git/modules/_submodules/TypeScript'), str(dest / '_submodules/TypeScript')], check=True)
        git(dest / '_submodules/TypeScript', 'checkout', '--quiet', '--force', '--detach', sub)
    if (git(dest, 'rev-parse', 'HEAD') != full or git(dest, 'status', '--porcelain')
            or git(dest / '_submodules/TypeScript', 'rev-parse', 'HEAD') != sub):
        die(f'{dest} is not a clean checkout of {full} with submodule {sub}')
    oracle = Path(cfg['defaults']['oracle']).with_name(f'tsgo-oracle-{key}')
    if not oracle.exists():
        env = dict(os.environ, GOTOOLCHAIN=go, CGO_ENABLED='0', GOAMD64='v1')
        subprocess.run(['go', 'build', '-o', str(oracle), './cmd/tsgo'], cwd=dest, env=env, check=True)
    version = subprocess.run([str(oracle), '--version'], capture_output=True, text=True).stdout.strip()
    cfg['pins'][key] = {
        'repo': 'microsoft/typescript-go', 'commit': full,
        'date': git(dest, 'log', '-1', '--format=%cs', full), 'layout': 'typescript-go',
        'typescriptSubmodule': sub, 'goCheckout': str(dest),
        'oracle': {'path': str(oracle), 'sha256': sha256(oracle), 'go': go, 'version': version,
                   'build': 'CGO_ENABLED=0 GOAMD64=v1 go build ./cmd/tsgo'},
    }
    save(cfg)
    print(json.dumps(cfg['pins'][key], indent=2))


def save(cfg):
    CONFIG.write_text(json.dumps(cfg, indent=2) + '\n')


def cmd_sync(host, key=None):
    cfg = load()
    key = resolve(cfg, key)
    rec = cfg['pins'][key]
    rs = ['rsync', '-aH', '--mkpath', '--compress', '--compress-choice=zstd', '--info=progress2']
    root = Path(cfg['pinRoot']) / key
    steps = [[rec['oracle']['path'], f'{host}:{rec["oracle"]["path"]}'],
             ['--exclude=.git', f'{rec["goCheckout"]}/', f'{host}:{rec["goCheckout"]}/'],
             [str(CONFIG), f'{host}:{CONFIG}']]
    if root.exists():
        steps.append([f'{root}/', f'{host}:{root}/'])
    for step in steps:
        subprocess.run(rs + step, check=True)


def main():
    args = sys.argv[1:]
    if not args or args[0] in ('-h', '--help'):
        print(__doc__.strip())
        sys.exit(0 if args else 2)
    cmd, rest = args[0], args[1:]
    if cmd == 'exec':
        cmd_exec(rest)
    elif cmd == 'show':
        cfg = load()
        print(json.dumps({'key': resolve(cfg, *rest[:1]), **cfg['pins'][resolve(cfg, *rest[:1])]}, indent=2))
    elif cmd == 'binds':
        cfg = load()
        key = resolve(cfg, *rest[:1])
        todo, _ = binds(cfg, key) if key != cfg['current'] else ([], [])
        for src, dest, ro in todo:
            print(f'{src} -> {dest}' + (' [ro]' if ro else ''))
    elif cmd == 'path' and rest:
        cmd_path(*rest[:2])
    elif cmd == 'add' and rest:
        opt = lambda name, default=None: rest[rest.index(name) + 1] if name in rest else default
        cmd_add(rest[0], opt('--go', 'go1.26.4'), opt('--checkout'))
    elif cmd == 'sync' and rest:
        cmd_sync(*rest[:2])
    else:
        die(f'bad arguments; see pin.py --help')


if __name__ == '__main__':
    main()
