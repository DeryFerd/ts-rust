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
  - nothing in its build output (2 levels down), its index or HEAD changed for N days (default 3),
  - no process has its cwd in it.
The Go build cache (`go env GOCACHE`) has no size limit of its own. When it is over G GB (default 40)
and no go process runs, `go clean -cache` empties it.
"""
import os, shutil, subprocess, sys, time

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


def go_cache_dirs(wt, max_depth=5):
    """Private Go build caches (a GOCACHE dir: trim.txt and Go's README) at most max_depth under <wt>/target."""
    found, root = [], os.path.join(wt, 'target')
    for dirpath, dirnames, filenames in os.walk(root):
        if 'trim.txt' in filenames and 'README' in filenames:
            with open(os.path.join(dirpath, 'README'), errors='replace') as f:
                if 'cached build artifacts from the Go build system' in f.read(200):
                    found.append(dirpath)
                    dirnames[:] = []
                    continue
        if dirpath[len(root):].count(os.sep) >= max_depth:
            dirnames[:] = []
        else:
            dirnames[:] = [d for d in dirnames if d not in ('node_modules', '.fingerprint', 'deps', 'incremental')]
    return found


def newest_mtime(paths):
    newest = 0.0
    for p in paths:
        for q in [p, *subdirs(p), *(g for c in subdirs(p) for g in subdirs(c))]:
            try:
                newest = max(newest, os.stat(q, follow_symlinks=False).st_mtime)
            except OSError:
                pass
    return newest


def git_files_mtime(wt):
    gitdir = git('-C', wt, 'rev-parse', '--absolute-git-dir').strip()
    times = [os.stat(os.path.join(gitdir, f)).st_mtime for f in ('index', 'HEAD') if os.path.exists(os.path.join(gitdir, f))]
    return max(times, default=0.0)


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
    if argv[:1] in (['help'], ['-h'], ['--help']):
        print(__doc__.strip())
        return 0
    if argv[:1] == ['timer']:
        install_timer()
        return 0
    days, go_cap_gb, apply = 3.0, 40.0, '--apply' in argv
    if '--days' in argv:
        days = float(argv[argv.index('--days') + 1])
    if '--go-cap-gb' in argv:
        go_cap_gb = float(argv[argv.index('--go-cap-gb') + 1])

    all_wts = worktrees()
    keep = {all_wts[0], os.path.join(all_wts[0], 'target/worktrees/checker-port')}
    cutoff = time.time() - days * 86400
    busy = busy_paths()
    before = free_gb()
    removed = 0
    for wt in all_wts:
        if wt in keep or not os.path.isdir(wt):
            continue
        if any(c == wt or c.startswith(wt + '/') for c in busy):
            continue
        dirs = build_dirs(wt) + go_cache_dirs(wt)
        if not dirs or max(newest_mtime(dirs), git_files_mtime(wt)) > cutoff:
            continue
        for d in dirs:
            print(('remove ' if apply else 'would remove ') + d, flush=True)
            if apply:
                shutil.rmtree(d, ignore_errors=True)
            removed += 1

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
        print(f'{removed} dirs removed; free {before:.0f} GB -> {free_gb():.0f} GB')
    else:
        print(f'dry run: {removed} dirs. Run with --apply to remove them.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
