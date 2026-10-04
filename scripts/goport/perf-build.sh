#!/bin/bash
# usage: perf-build.sh <label> [options] <side>=<bin>...
#   options: --cores 4,16  --rounds query-chain:10,hono-b:5,effect-b:4,wide:4  --steps cold,noop,body,api
#            --args=<extra tsgo args, commas for spaces, for example --args=--builders,1>
#   example: perf-build.sh bB-base go=$HOME/.local/bin/tsgo-oracle-16c25522e123 base=<bins>/tsgo new=<bins>/tsgo
# `tsgo -b` timing (the gap-audit timing/incr method, gap-audit-perf/tools/extra.py). Per scenario, core count,
# round and side, on a fresh copy of the project at one path for every side (so build info paths agree):
#   cold  first build          noop  rebuild with no change
#   body  'void 0;' appended to an upstream file          api  an export appended to the upstream API file
# Scenarios: query-chain (-b packages/query-sync-storage-persister/tsconfig.json), hono-b (-b tsconfig.json),
# effect-b (-b packages/effect/tsconfig.json, no api step), wide (-b tsconfig.json on a generated monorepo of 12
# independent composite packages of 300 files, the feataudit gen-wide.py shape). Sides run in a seeded shuffle each round; round -1
# is a warm-up. The first side is the reference: the table gives each side's median wall ms, the ratio
# <first side> / <side>, and how many runs had an output tree (with and without .tsbuildinfo) or stdout that
# differs from the first side's run of the same step and round.
# Timing on a loaded host is noise: the tool refuses to start above load PERF_MAX_LOAD (1.5), or waits up to 30
# minutes with PERF_WAIT=1. Run it on a quiet host through remote.sh (mini-743d). GOPORT_* and
# allocator variables are removed and GOPORT_LAUNCH=0 is set, as in perf.sh (PERF_LAUNCH=1 keeps the launcher).
# Output: target/continuation-r97-goport/perf-build/<label>/ (runs.jsonl, host.json, table.txt).
set -uo pipefail
[[ $# -ge 2 ]] || { sed -n '2,18p' "$0"; exit 2; }
exec 8> /tmp/goport-perf.lock
flock -n 8 || { echo "another perf run holds /tmp/goport-perf.lock; waiting"; flock 8; }
exec python3 - "$@" << 'PY'
import argparse, hashlib, json, os, platform, random, shutil, statistics, subprocess, sys, time

REPO = '/home/theo/Code/sandbox/ts-rust'
P = REPO + '/target/project-inputs'
# name: (source, argv after the bin, body-edit file, api-edit file)
SCEN = {
    'query-chain': (P + '/query/source', ['-b', 'packages/query-sync-storage-persister/tsconfig.json'],
                    'packages/query-core/src/utils.ts', 'packages/query-core/src/index.ts'),
    'hono-b': (P + '/hono/source', ['-b', 'tsconfig.json'], 'src/hono.ts', 'src/index.ts'),
    'effect-b': (P + '/effect/source', ['-b', 'packages/effect/tsconfig.json'], 'packages/effect/src/Chunk.ts', None),
    'wide': (None, ['-b', 'tsconfig.json'], 'pkg0/src/m150.ts', 'pkg0/src/m299.ts'),
}
OUT_EXT = ('.js', '.mjs', '.cjs', '.d.ts', '.d.mts', '.d.cts', '.map', '.tsbuildinfo')
DROP = ('GLIBC_TUNABLES', '_RJEM_MALLOC_CONF', 'MALLOC_CONF', 'GOMAXPROCS', 'GOGC', 'GOMEMLIMIT', 'GODEBUG')
ENV = {k: v for k, v in os.environ.items() if k not in DROP and not k.startswith('GOPORT_')}
if os.environ.get('PERF_LAUNCH') != '1':
    ENV['GOPORT_LAUNCH'] = '0'

ap = argparse.ArgumentParser()
ap.add_argument('label')
ap.add_argument('sides', nargs='+')
ap.add_argument('--cores', default='4,16')
ap.add_argument('--rounds', default='query-chain:10,hono-b:5,effect-b:4,wide:4')
ap.add_argument('--steps', default='cold,noop,body,api')
ap.add_argument('--args', default='')
a = ap.parse_args()
sides = dict(s.split('=', 1) for s in a.sides)
names = list(sides)
for n, b in sides.items():
    if not os.access(b, os.X_OK):
        sys.exit(f'not executable: {n}={b}')
cores = [int(c) for c in a.cores.split(',')]
rounds = {k: int(v) for k, v in (x.split(':') for x in a.rounds.split(','))}
want = a.steps.split(',')
extra = a.args.replace(',', ' ').split()
out = f'{REPO}/target/continuation-r97-goport/perf-build/{a.label}'
if os.path.exists(out):
    sys.exit(f'{out} exists')

load = lambda: float(open('/proc/loadavg').read().split()[0])
mx = float(os.environ.get('PERF_MAX_LOAD', '1.5'))
if load() > mx:
    if os.environ.get('PERF_WAIT') != '1':
        sys.exit(f'load {load()} > {mx} on {platform.node()}: timing would be noise. Use a quiet host or PERF_WAIT=1.')
    for _ in range(180):
        if load() <= mx:
            break
        time.sleep(10)
    else:
        sys.exit(f'load still {load()} after 30 minutes')
os.makedirs(out)
scratch = f'/dev/shm/perf-build-{os.getpid()}'
os.makedirs(scratch)


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def trees(root):
    """(hash of the output files, hash without .tsbuildinfo, file count); node_modules is skipped."""
    h, hn, n = hashlib.sha256(), hashlib.sha256(), 0
    for dp, dns, fns in os.walk(root):
        dns[:] = sorted(d for d in dns if d != 'node_modules')
        for fn in sorted(fns):
            if fn.endswith(OUT_EXT):
                p = os.path.join(dp, fn)
                line = os.path.relpath(p, root).encode() + b'\0' + sha(p).encode() + b'\n'
                h.update(line)
                if not fn.endswith('.tsbuildinfo'):
                    hn.update(line)
                n += 1
    return h.hexdigest(), hn.hexdigest(), n


def gen_wide(root, packages=12, files=300):
    """feataudit/gen-wide.py: independent composite packages whose modules import each other."""
    refs = []
    for p in range(packages):
        d = f'{root}/pkg{p}'
        os.makedirs(d + '/src')
        open(d + '/tsconfig.json', 'w').write(
            '{"compilerOptions":{"composite":true,"strict":true,"target":"es2022","module":"esnext","moduleResolution":'
            '"bundler","outDir":"dist","rootDir":"src","declarationMap":true,"skipLibCheck":true},"include":["src"]}\n')
        for f in range(files):
            prev = f"Shape{f - 1}" if f else "unknown"
            imp = f"import {{ Box{f-1}, make{f-1}, type Shape{f-1} }} from './m{f-1}';\n" if f else ""
            body = f"""{imp}export interface Shape{f} {{ kind: 'k{f}'; id: number; tags: readonly string[]; meta?: Record<string, {prev}> }}
export type Pick{f}<T extends Shape{f}> = {{ [K in keyof T as K extends 'kind' ? never : `get_${{K & string}}`]: () => T[K] }};
export class Box{f}<T> {{ constructor(public readonly value: T, private n = {f}) {{}} map<U>(fn: (v: T) => U): Box{f}<U> {{ return new Box{f}(fn(this.value), this.n); }} get size(): number {{ return this.n; }} }}
export function make{f}<T extends object>(v: T): Box{f}<T & {{ at: {f} }}> {{ return new Box{f}({{ ...v, at: {f} as const }}); }}
export const table{f} = {{ a: 1, b: 'x', d: {{ e: true }} }} satisfies Record<string, unknown>;
export function reduce{f}(xs: Shape{f}[]): Map<string, Shape{f}[]> {{ const m = new Map<string, Shape{f}[]>(); for (const x of xs) {{ const k = x.tags[0] ?? ''; m.set(k, [...(m.get(k) ?? []), x]); }} return m; }}
export type Deep{f}<T> = T extends readonly (infer U)[] ? Deep{f}<U>[] : T extends object ? {{ readonly [K in keyof T]: Deep{f}<T[K]> }} : T;
export const deep{f}: Deep{f}<typeof table{f}> = table{f};
"""
            if f:
                body += f"export const chained{f} = make{f-1}({{ q: {f} }}).map(v => v.at + {f});\nexport const s{f}: Shape{f-1} | undefined = undefined;\n"
            open(f'{d}/src/m{f}.ts', 'w').write(body)
        refs.append(f'{{"path":"./pkg{p}"}}')
    open(root + '/tsconfig.json', 'w').write('{"files":[],"references":[' + ','.join(refs) + ']}\n')


def template(src, dst):
    """cp -a of src with its top-level node_modules as a symlink, writable, without *.tsbuildinfo."""
    if src is None:
        return gen_wide(dst)
    os.makedirs(dst)
    for name in os.listdir(src):
        s = os.path.join(src, name)
        if name == 'node_modules' and os.path.isdir(s) and not os.path.islink(s):
            os.symlink(s, os.path.join(dst, name))
        else:
            subprocess.run(['cp', '-a', s, dst + '/'], check=True)
    subprocess.run(['chmod', '-R', 'u+w', dst], check=True)
    for dp, dns, fns in os.walk(dst):
        dns[:] = [d for d in dns if d != 'node_modules']
        for fn in fns:
            if fn.endswith('.tsbuildinfo'):
                os.remove(os.path.join(dp, fn))


def run(side, argv, cwd, cpus):
    txt = f'{scratch}/o.txt'
    with open(txt, 'wb') as f:
        t0 = time.perf_counter_ns()
        proc = subprocess.Popen(['taskset', '-c', cpus, sides[side], *argv, *extra, '--pretty', 'false'],
                                stdout=f, stderr=subprocess.STDOUT, env=ENV, cwd=cwd)
        _, status, ru = os.wait4(proc.pid, 0)
        t1 = time.perf_counter_ns()
    r = dict(wall_ms=(t1 - t0) / 1e6, maxrss_kb=ru.ru_maxrss, utime=ru.ru_utime, stime=ru.ru_stime,
             exit=os.waitstatus_to_exitcode(status), out_sha=sha(txt))
    os.remove(txt)
    return r


host = dict(hostname=platform.node(), nproc=os.cpu_count(), kernel=platform.release(),
            thp=open('/sys/kernel/mm/transparent_hugepage/enabled').read().strip(), start=time.strftime('%FT%TZ', time.gmtime()),
            load_start=open('/proc/loadavg').read().strip(), cores=cores, rounds=a.rounds, steps=want, args=extra,
            launch=ENV.get('GOPORT_LAUNCH', 'default'), bins={n: dict(path=b, sha256=sha(b)) for n, b in sides.items()})
json.dump(host, open(out + '/host.json', 'w'), indent=1)
rows = open(out + '/runs.jsonl', 'a', buffering=1)
res = []
for scen, nr in rounds.items():
    src, argv, up, api = SCEN[scen]
    tmpl, copy = f'{scratch}/tmpl-{scen}', f'{scratch}/w/{scen}'
    template(src, tmpl)
    steps = [s for s in want if s != 'api' or api]
    for c in cores:
        cpus = f'0-{c - 1}'
        for rnd in range(-1, nr):
            order = list(names)
            if rnd >= 0:
                random.Random(rnd).shuffle(order)
            for s in order:
                shutil.rmtree(copy, ignore_errors=True)
                os.makedirs(os.path.dirname(copy), exist_ok=True)
                subprocess.run(['cp', '-a', tmpl, copy], check=True)
                # Every step runs so the build state is the same; only the wanted steps are kept.
                for step, edit in (('cold', None), ('noop', None), ('body', (up, '\nvoid 0;\n')),
                                   ('api', (api, '\nexport const goportApi = 1;\n') if api else None)):
                    if step == 'api' and not api:
                        continue
                    if edit:
                        with open(os.path.join(copy, edit[0]), 'a') as f:
                            f.write(edit[1])
                        time.sleep(0.05)  # the edit's mtime moves past the build info write
                    r = run(s, argv, copy, cpus)
                    tree, tree_nobi, files = trees(copy)
                    row = dict(scen=scen, cores=c, round=rnd, side=s, step=step, tree=tree, tree_nobi=tree_nobi,
                               files=files, **r)
                    rows.write(json.dumps(row) + '\n')
                    if rnd >= 0 and step in steps:
                        res.append(row)
            print(f'{time.strftime("%H:%M:%S")} {scen} c{c} round {rnd} done, load {load()}', flush=True)
    shutil.rmtree(scratch + '/w', ignore_errors=True)
    shutil.rmtree(tmpl, ignore_errors=True)

ref = names[0]
by = {}
for r in res:
    by.setdefault((r['scen'], r['cores'], r['step']), {}).setdefault(r['side'], []).append(r)
lines = [f'host {platform.node()} load end {load()}; ratio = {ref} ms / side ms; diff = runs whose '
         f'tree / tree without tsbuildinfo / stdout differ from {ref}', '']
lines.append(f'{"cell":<24}' + ''.join(f'{n + " ms":>12}' for n in names) + ''.join(f'{n + " x":>10}' for n in names[1:])
             + '  diff ' + ' '.join(names[1:]))
for key in sorted(by):
    d = by[key]
    med = {n: statistics.median(x['wall_ms'] for x in d.get(n, [])) if d.get(n) else float('nan') for n in names}
    refrun = {x['round']: x for x in d.get(ref, [])}
    diffs = []
    for n in names[1:]:
        t = b = o = 0
        for x in d.get(n, []):
            y = refrun.get(x['round'])
            t += y is not None and x['tree'] != y['tree']
            b += y is not None and x['tree_nobi'] != y['tree_nobi']
            o += y is not None and (x['out_sha'] != y['out_sha'] or x['exit'] != y['exit'])
        diffs.append(f'{t}/{b}/{o}')
    lines.append(f'{" ".join(map(str, key)):<24}' + ''.join(f'{med[n]:>12.1f}' for n in names)
                 + ''.join(f'{med[ref] / med[n]:>10.2f}' for n in names[1:]) + '  ' + ' '.join(diffs))
open(out + '/table.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
host.update(end=time.strftime('%FT%TZ', time.gmtime()), load_end=open('/proc/loadavg').read().strip())
json.dump(host, open(out + '/host.json', 'w'), indent=1)
shutil.rmtree(scratch, ignore_errors=True)
PY
