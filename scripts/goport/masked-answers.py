#!/usr/bin/env python3
"""Writes a masked API answer set for oracle-compare.py --answers (bump C reviewer ruling 1 item 3, request 2 item 1).

usage: masked-answers.py --keys TSV --mask ids|strict --pin PIN --golden DIR... --out FILE.json.gz [--note TEXT]

--keys: lines "api TAB <battery>/<trace>#<event> ..." (for example upstream/bumpC/rebaseN/answers-excluded.tsv; #
comments). --golden: the Go golden roots of the pin's oracle, each .../golden/<oracle sha256 prefix> (the pin's
golden and every re-record). For each key, every golden root gives the Go answer of that event, normalized as the
tools do (apply_multisets with the key's multiset patterns from the flaky file of the first golden root), then
masked with oracle-compare.py mask_answer() and the API tool loaded at the pin. All runs must give one masked
answer, or the key fails and nothing is written. The entry is {method, multiset, mask, answers: [{answer, sha256,
sources}]} with every Go golden as a source (relative to the repo root, sorted). The header is goport-oracle-answers/1
with kind api, pin, oracleSha256 (every golden's oracleSha), goldenSha12, mask, maskTool (oracle-compare.py
mask_tool()) and note. Prints per key the method, the run count and the masked sha256, then the file sha256.
"""
import argparse, gzip, hashlib, importlib.util, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('oracle_compare', os.path.join(HERE, 'oracle-compare.py'))
OC = importlib.util.module_from_spec(spec)
spec.loader.exec_module(OC)


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--keys', required=True)
    p.add_argument('--mask', required=True, choices=OC.MASKS)
    p.add_argument('--pin', required=True)
    p.add_argument('--golden', nargs='+', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('--note', default='')
    a = p.parse_args()
    api = OC.tool_at('api', a.pin)
    keys = [line.split('\t')[1].strip() for line in open(a.keys, encoding='utf-8')
            if line.strip() and not line.startswith('#') and line.split('\t')[0] == 'api']
    if not keys or len(keys) != len(set(keys)) or not all(OC.parse_key(k) for k in keys):
        sys.exit(f'masked-answers.py: {a.keys} needs distinct api keys <battery>/<trace>#<event>')
    roots = [os.path.realpath(g) for g in a.golden]
    sha12 = {os.path.basename(r) for r in roots}
    if len(sha12) != 1 or len(roots) != len(set(roots)):
        sys.exit(f'masked-answers.py: the golden roots must be distinct dirs of one oracle, not {sorted(sha12)}')
    sha12, oracles, out, bad = sha12.pop(), set(), {}, []
    for key in keys:
        battery, trace, event = OC.parse_key(key)
        flaky_file = os.path.join(roots[0], battery, trace + '.flaky.json')
        flaky = (json.load(open(flaky_file)).get('events') or {}).get(event) or {} if os.path.isfile(flaky_file) else {}
        patterns, masked, method = flaky.get('multiset') or [], {}, None
        for root in roots:
            path = os.path.join(root, battery, trace + '.golden.jsonl.gz')
            if not os.path.isfile(path):
                bad.append(f'{key}: no golden {path}')
                continue
            with gzip.open(path, 'rt', encoding='utf-8') as f:
                lines = [json.loads(line) for line in f if line.strip()]
            oracles.add(lines[0].get('oracleSha'))
            rec = {str(k): r for k, r in api.records_by_event(lines[1:]).items()}.get(event) or {}
            if rec.get('status') != 'ok' or 'result' not in (rec.get('response') or {}):
                bad.append(f'{key}: {path} has no ok answer')
                continue
            method = method or rec.get('method')
            v = OC.mask_answer(api, a.mask, method, api.apply_multisets(rec['response']['result'], patterns))
            text = api.canon(v)
            masked.setdefault(hashlib.sha256(text.encode('utf-8')).hexdigest(), (v, []))[1].append(os.path.relpath(path, api.REPO))
        if len(masked) != 1:
            bad.append(f'{key}: {len(masked)} masked answers in {len(roots)} Go runs')
            continue
        (sha, (answer, sources)), = masked.items()
        out[key] = {'method': method, 'multiset': patterns, 'mask': a.mask,
                    'answers': [{'answer': answer, 'sha256': sha, 'sources': sorted(sources)}]}
        print(f'{key}\t{method}\t{len(sources)} Go runs\tmasked {sha[:16]}')
    if len(oracles) != 1 or not str(next(iter(oracles))).startswith(sha12):
        bad.append(f'the goldens name the oracles {sorted(map(str, oracles))}, not one oracle {sha12}...')
    if bad:
        sys.exit('\n'.join(bad))
    doc = {'format': OC.ANSWERS_FORMAT, 'kind': 'api', 'pin': a.pin, 'oracleSha256': oracles.pop(), 'goldenSha12': sha12,
           'mask': a.mask, 'maskTool': OC.mask_tool(), 'note': a.note, 'requests': dict(sorted(out.items()))}
    data = gzip.compress(json.dumps(doc, sort_keys=True).encode('utf-8'), mtime=0)
    with open(a.out, 'wb') as f:
        f.write(data)
    print(f'{len(out)} masked keys, mask {a.mask}; {a.out} sha256 {hashlib.sha256(data).hexdigest()}')


if __name__ == '__main__':
    main()
