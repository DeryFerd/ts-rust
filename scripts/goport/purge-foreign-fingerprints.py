#!/usr/bin/env python3
"""Removes the cargo fingerprints in a target dir that were built from another checkout.

usage: scripts/goport/purge-foreign-fingerprints.py <target dir> <checkout>

Cargo names a path crate's artifacts by its path relative to the workspace root, so the same crate built
from two worktrees into one target dir lands on the same files. Its dep-info then lists the other
worktree's sources, and a later build from this checkout sees it as fresh and links stale code (R132 side
try 1: goport_util built from goport-legacy1). A fingerprint dir whose dep-info names a file under the
repository (the main checkout or any worktree) but outside <checkout> is removed, so cargo builds that unit
again. Registry and git sources do not count. Prints one line per removed dir and a count.
"""
import os, re, shutil, sys

ROOT = '/home/theo/Code/sandbox/ts-rust/'
PATH = re.compile(rb'/[\x21-\x7e]+')


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    target, checkout = sys.argv[1], os.path.realpath(sys.argv[2]) + '/'
    removed = 0
    for profile in ('release', 'debug'):
        fp = os.path.join(target, profile, '.fingerprint')
        if not os.path.isdir(fp):
            continue
        for name in sorted(os.listdir(fp)):
            d = os.path.join(fp, name)
            foreign = None
            for f in os.listdir(d) if os.path.isdir(d) else []:
                if not f.startswith('dep-'):
                    continue
                with open(os.path.join(d, f), 'rb') as h:
                    for m in PATH.finditer(h.read()):
                        p = m.group().decode('ascii', 'replace')
                        if p.startswith(ROOT) and not p.startswith(checkout) and '/registry/' not in p and '/git/checkouts/' not in p:
                            foreign = p
                            break
                if foreign:
                    break
            if foreign:
                shutil.rmtree(d)
                removed += 1
                print(f'removed {profile}/.fingerprint/{name} (built from {foreign})')
    print(f'{removed} foreign fingerprint dir(s) removed')


if __name__ == '__main__':
    main()
