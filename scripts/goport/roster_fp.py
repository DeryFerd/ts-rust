#!/usr/bin/env python3
"""Roster fingerprint: fp.py's method over every file except crates/ts_goport/.

No roster crate (ts_checker, ts_compiler, ts_fixture and their dependencies) depends on
ts_goport. So two sources with the same roster fingerprint give the protected cargo roster
and the current-source corpus byte-identical inputs. The goport-only roster carry-forward
rule (docs/typechecker-accountability.md) compares these hashes.

usage: roster_fp.py <checkout>   prints "<sha256> <file count>", like fp.py
"""
import hashlib, os, subprocess, sys

EXCLUDED = b'crates/ts_goport/'

root = sys.argv[1]
out = subprocess.run(['git', '-C', root, 'ls-files', '--cached', '--others', '--exclude-standard', '-z'],
                     capture_output=True, check=True).stdout
h, n = hashlib.sha256(), 0
for f in sorted(f for f in out.split(b'\0') if f and not f.startswith(EXCLUDED)):
    p = os.path.join(root.encode(), f)
    if not os.path.isfile(p):
        continue
    h.update(f + b'\0' + open(p, 'rb').read() + b'\0')
    n += 1
print(h.hexdigest(), n)
