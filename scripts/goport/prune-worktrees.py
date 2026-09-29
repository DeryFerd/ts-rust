#!/usr/bin/env python3
"""Lists stale git worktrees and merged branches. Changes nothing unless --apply.

usage: prune-worktrees.py [--days N] [--apply]

A worktree is stale when all of these hold:
  - it is not the main checkout and not target/worktrees/checker-port,
  - its HEAD is already in main (git merge-base --is-ancestor HEAD main),
  - nothing in it changed for N days (default 3): newest of its index, HEAD and branch commit time,
  - git status --porcelain is empty (no dirty or untracked files).
A branch is stale when it is merged into main, has no worktree and is not main or july-ultra.
--apply runs `git worktree remove` (refuses dirty trees) and `git branch -d` (refuses unmerged
branches), then `git worktree prune`. Every removed commit stays reachable from main.
"""
import os, subprocess, sys, time

REPO = '/home/theo/Code/sandbox/ts-rust'
KEEP_PATHS = {REPO, f'{REPO}/target/worktrees/checker-port'}
KEEP_BRANCHES = {'main', 'july-ultra'}


def git(*args, cwd=REPO, check=True):
    return subprocess.run(['git', '-C', cwd, *args], capture_output=True, text=True, check=check).stdout


def worktrees():
    """(path, head, branch or None) for each worktree in `git worktree list --porcelain`."""
    out, cur = [], {}
    for line in git('worktree', 'list', '--porcelain').splitlines() + ['']:
        if not line:
            if cur:
                out.append((cur['worktree'], cur.get('HEAD'), cur.get('branch', '').removeprefix('refs/heads/') or None))
            cur = {}
        else:
            k, _, v = line.partition(' ')
            cur[k] = v
    return out


def last_change(path, head):
    """Newest of the worktree's index mtime, its HEAD file mtime and its commit time."""
    gitdir = git('rev-parse', '--absolute-git-dir', cwd=path).strip()
    times = [os.path.getmtime(f'{gitdir}/{f}') for f in ('index', 'HEAD') if os.path.exists(f'{gitdir}/{f}')]
    times.append(int(git('log', '-1', '--format=%ct', head)))
    return max(times)


def main():
    args = sys.argv[1:]
    if '-h' in args or '--help' in args:
        print(__doc__.strip())
        return
    apply = '--apply' in args
    days = float(args[args.index('--days') + 1]) if '--days' in args else 3.0
    cutoff = time.time() - days * 86400
    stale, kept, in_use = [], 0, set()
    for path, head, branch in worktrees():
        if branch:
            in_use.add(branch)
        if path in KEEP_PATHS or not head or not os.path.isdir(path):
            kept += 1
            continue
        ok = (subprocess.run(['git', '-C', REPO, 'merge-base', '--is-ancestor', head, 'main']).returncode == 0
              and last_change(path, head) < cutoff
              and not git('status', '--porcelain', cwd=path, check=False).strip())
        if ok:
            stale.append((path, branch))
        else:
            kept += 1
    merged = [b.strip().lstrip('*+ ').strip() for b in git('branch', '--merged', 'main').splitlines()]
    stale_branches = [b for b in merged if b and b not in KEEP_BRANCHES and b not in in_use]
    stale_branches += [b for _, b in stale if b and b not in KEEP_BRANCHES]
    print(f'{len(stale)} stale worktrees, {kept} kept; {len(stale_branches)} merged branches to delete')
    for path, branch in stale:
        print(f'  worktree {path} [{branch}]')
    for b in stale_branches[:50]:
        print(f'  branch {b}')
    if len(stale_branches) > 50:
        print(f'  ... and {len(stale_branches) - 50} more branches')
    if not apply:
        print('dry run: nothing changed. Run with --apply to remove them.')
        return
    for path, _ in stale:
        subprocess.run(['git', '-C', REPO, 'worktree', 'remove', path])
    for i in range(0, len(stale_branches), 200):
        subprocess.run(['git', '-C', REPO, 'branch', '-d', *stale_branches[i:i + 200]], capture_output=True)
    git('worktree', 'prune')
    print('done; run again to see what is left')


if __name__ == '__main__':
    main()
