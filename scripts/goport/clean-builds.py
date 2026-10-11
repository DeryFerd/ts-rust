#!/usr/bin/env python3
"""Frees disk: removes Cargo and Go build output from idle worktrees and caps the Go build cache.
Changes nothing unless --apply.

usage: clean-builds.py [--days N] [--go-cap-gb G] [--apply]
       clean-builds.py timer      install and start the daily systemd user timer (runs --apply)
       clean-builds.py help       this text

Build output: each dir directly under <worktree>/target/ that Cargo made, that is a dir with a
.fingerprint/ dir 1 to 3 levels down (debug/, release/, <triple>/, and CARGO_TARGET_DIR dirs such as
goport-tests/ and candidate-side/), and each private Go build cache (a GOCACHE dir with trim.txt and Go's
README) at most 5 levels under target/. Logs, reports and evidence under target/ stay.
A worktree is idle when all of these hold:
  - it is not the main checkout and not target/worktrees/checker-port,
  - no file or dir in its build output (4 levels down), its index or HEAD changed for N days (default 3),
  - no process has its cwd in it,
  - its target/ is not a symlink.
The Go build cache (`go env GOCACHE`) has no size limit of its own. When it is over G GB (default 40)
and no go process runs, `go clean -cache` empties it.
Exits 1 when a removal fails.
"""
import argparse, os, re, shutil, subprocess, sys, time

TIMER_NAME = 'ts-rust-clean-builds'


def git(*args):
    return subprocess.run(['git', *args], capture_output=True, text=True, check=True).stdout


def worktrees():
    """Path of every worktree; the first one is the main checkout."""
    listing = git('-C', os.path.dirname(os.path.abspath(__file__)), 'worktree', 'list', '--porcelain')
    return [line[len('worktree '):] for line in listing.splitlines() if line.startswith('worktree ')]


def subdirs(path):
    try:
        return [e.path for e in os.scandir(path) if e.is_dir(follow_symlinks=False)]
    except OSError:
        return []


def build_dirs(wt):
    """Cargo-made dirs directly under <wt>/target."""
    found = []
    for d in subdirs(os.path.join(wt, 'target')):
        level1 = subdirs(d)
        level2 = [g for c in level1 for g in subdirs(c)]
        if any(os.path.basename(p) == '.fingerprint' for p in level1 + level2) or any(
                os.path.isdir(os.path.join(p, '.fingerprint')) for p in level2):
            found.append(d)
    return found


def is_go_cache(path):
    """True when Go's README says path is a GOCACHE dir. An unreadable README means no."""
    try:
        with open(os.path.join(path, 'README'), errors='replace') as f:
            return 'cached build artifacts from the Go build system' in f.read(200)
    except OSError:
        return False


def go_cache_dirs(wt, max_depth=5):
    """Private Go build caches (a GOCACHE dir: trim.txt and Go's README) at most max_depth under <wt>/target."""
    found, root = [], os.path.join(wt, 'target')
    for dirpath, dirnames, filenames in os.walk(root):
        if 'trim.txt' in filenames and 'README' in filenames and is_go_cache(dirpath):
            found.append(dirpath)
            dirnames[:] = []
            continue
        if dirpath[len(root):].count(os.sep) >= max_depth:
            dirnames[:] = []
        else:
            dirnames[:] = [d for d in dirnames if d not in ('node_modules', '.fingerprint', 'deps', 'incremental')]
    return found


def changed_since(paths, cutoff, max_depth=4):
    """True when one of paths, or a file or dir at most max_depth levels under it, has an mtime after cutoff.
    A rebuilt binary, a rewritten fingerprint or log and a Go cache entry that Go marked as used all count.
    The walk only stats (it reads no file), stops at the first hit and stays max_depth deep, so a multi-GB
    target dir takes milliseconds. A path it cannot read counts as changed, so its dir stays."""
    def walk(path, depth):
        with os.scandir(path) as entries:
            for e in entries:
                if e.stat(follow_symlinks=False).st_mtime > cutoff:
                    return True
                if depth < max_depth and e.is_dir(follow_symlinks=False) and walk(e.path, depth + 1):
                    return True
        return False

    try:
        return any(os.lstat(p).st_mtime > cutoff or walk(p, 1) for p in paths)
    except OSError:
        return True


def git_files_mtime(wt):
    """Newest mtime of the worktree's index and HEAD. A worktree that git cannot read counts as just used."""
    try:
        gitdir = git('-C', wt, 'rev-parse', '--absolute-git-dir').strip()
        files = [os.path.join(gitdir, f) for f in ('index', 'HEAD')]
        return max((os.stat(f).st_mtime for f in files if os.path.exists(f)), default=0.0)
    except (subprocess.CalledProcessError, OSError):
        return float('inf')


def busy_paths():
    """cwd of every process we can see."""
    cwds = set()
    for pid in filter(str.isdigit, os.listdir('/proc')):
        try:
            cwds.add(os.readlink(f'/proc/{pid}/cwd'))
        except OSError:
            pass
    return cwds


def go_running():
    for pid in filter(str.isdigit, os.listdir('/proc')):
        try:
            with open(f'/proc/{pid}/comm') as f:
                if f.read().strip() == 'go':
                    return True
        except OSError:
            pass
    return False


def dir_bytes(path):
    out = subprocess.run(['du', '-sb', path], capture_output=True, text=True).stdout.split()
    return int(out[0]) if out else 0


def free_gb():
    st = os.statvfs(os.path.expanduser('~'))
    return st.f_bavail * st.f_frsize / 1e9


def install_timer():
    script = os.path.abspath(__file__)
    if not re.fullmatch(r'[\w./+@-]+', script):
        sys.exit(f'{script}: systemd would split or expand this path. Install the timer from a plainer path.')
    unit_dir = os.path.expanduser('~/.config/systemd/user')
    os.makedirs(unit_dir, exist_ok=True)
    with open(f'{unit_dir}/{TIMER_NAME}.service', 'w') as f:
        f.write(f"""[Unit]
Description=ts-rust: remove build output of idle worktrees, cap the Go build cache
ConditionPathExists={script}

[Service]
Type=oneshot
Nice=19
IOSchedulingClass=idle
ExecStart=/usr/bin/env python3 {script} --apply
""")
    with open(f'{unit_dir}/{TIMER_NAME}.timer', 'w') as f:
        f.write(f"""[Unit]
Description=Daily ts-rust build cleanup

[Timer]
OnCalendar=daily
RandomizedDelaySec=1h
Persistent=true

[Install]
WantedBy=timers.target
""")
    subprocess.run(['systemctl', '--user', 'daemon-reload'], check=True)
    subprocess.run(['systemctl', '--user', 'enable', '--now', f'{TIMER_NAME}.timer'], check=True)
    print(f'installed {TIMER_NAME}.timer (logs: journalctl --user -u {TIMER_NAME})')


def main(argv):
    p = argparse.ArgumentParser(prog='clean-builds.py', add_help=False, allow_abbrev=False)
    p.add_argument('command', nargs='?', choices=('help', 'timer'))
    p.add_argument('-h', '--help', action='store_true')
    p.add_argument('--days', type=float, default=3.0)
    p.add_argument('--go-cap-gb', type=float, default=40.0)
    p.add_argument('--apply', action='store_true')
    args = p.parse_args(argv)
    if args.help or args.command == 'help':
        print(__doc__.strip())
        return 0
    if args.command == 'timer':
        install_timer()
        return 0
    go_cap_gb, apply = args.go_cap_gb, args.apply

    all_wts = worktrees()
    keep = {all_wts[0], os.path.join(all_wts[0], 'target/worktrees/checker-port')}
    cutoff = time.time() - args.days * 86400
    busy = busy_paths()
    before = free_gb()
    removed = failed = 0
    for wt in all_wts:
        # A symlinked target/ can be build output that another checkout uses.
        if wt in keep or not os.path.isdir(wt) or os.path.islink(os.path.join(wt, 'target')):
            continue
        if any(c == wt or c.startswith(wt + '/') for c in busy):
            continue
        dirs = build_dirs(wt) + go_cache_dirs(wt)
        if not dirs or git_files_mtime(wt) > cutoff or changed_since(dirs, cutoff):
            continue
        # A Go cache inside a Cargo dir goes with it: remove only the outer dirs.
        for d in [d for d in dirs if not any(d.startswith(o + os.sep) for o in dirs)]:
            print(('remove ' if apply else 'would remove ') + d, flush=True)
            if apply:
                try:
                    shutil.rmtree(d)
                except OSError as e:
                    print(f'failed to remove {d}: {e}', file=sys.stderr, flush=True)
                    failed += 1
                    continue
            removed += 1

    gocache = ''
    if shutil.which('go'):
        gocache = subprocess.run(['go', 'env', 'GOCACHE'], capture_output=True, text=True).stdout.strip()
    if gocache and os.path.isdir(gocache):
        size_gb = dir_bytes(gocache) / 1e9
        if size_gb > go_cap_gb:
            if go_running():
                print(f'Go cache {size_gb:.0f} GB is over {go_cap_gb:.0f} GB; a go process runs, so it stays')
            elif apply:
                subprocess.run(['go', 'clean', '-cache'], check=True)
                print(f'emptied the Go cache ({size_gb:.0f} GB)')
            else:
                print(f'would empty the Go cache ({size_gb:.0f} GB)')

    if apply:
        print(f'{removed} dirs removed, {failed} failed; free {before:.0f} GB -> {free_gb():.0f} GB')
    else:
        print(f'dry run: {removed} dirs. Run with --apply to remove them.')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
