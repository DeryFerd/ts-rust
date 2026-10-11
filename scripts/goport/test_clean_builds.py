#!/usr/bin/env python3
"""Unit tests for clean-builds.py on temp dir trees. Nothing outside the temp dir is removed: worktrees() is
replaced and every --apply case replaces shutil.rmtree with a stub that fails.

  python3 scripts/goport/test_clean_builds.py
"""
import contextlib
import importlib.util
import io
import os
import shutil
import tempfile
import time
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("clean_builds", os.path.join(HERE, "clean-builds.py"))
cb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cb)

OLD = time.time() - 10 * 86400
GO_README = "This directory holds cached build artifacts from the Go build system.\n"


def make_tree(root, files):
    """Writes files (relative path -> text) under root, then sets every file and dir under root to OLD."""
    for rel, text in files.items():
        path = os.path.join(root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(text)
    for dirpath, dirnames, filenames in os.walk(root, topdown=False):
        for n in filenames + dirnames:
            os.utime(os.path.join(dirpath, n), (OLD, OLD), follow_symlinks=False)
        os.utime(dirpath, (OLD, OLD))


def rewrite(path):
    """Changes a file in place, as a rebuilt binary or an appended log does: no dir mtime changes."""
    with open(path, "r+") as f:
        f.write("new")


class Tree(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.main_wt = os.path.join(self.tmp, "main")
        self.wt = os.path.join(self.tmp, "wt")
        self.release = os.path.join(self.wt, "target/release")
        self.gocache = os.path.join(self.wt, "target/gocache")
        os.makedirs(self.main_wt)
        make_tree(self.wt, {
            "target/release/tsgo": "bin",
            "target/release/deps/a.rlib": "x",
            "target/release/.fingerprint/unit/dep-lib": "x",
            "target/release/build/pkg/out/gen.rs": "x",
            "target/release/incremental/c/s/q/deep": "x",
            "target/gocache/trim.txt": "x",
            "target/gocache/README": GO_README,
            "target/gocache/0a/entry-d": "x",
            "target/gate.log": "x",
        })
        self.empty_path = os.path.join(self.tmp, "nobin")
        os.makedirs(self.empty_path)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def run_main(self, *argv):
        """main() on the fake worktrees, with no go on PATH. Returns (exit code, stdout, stderr)."""
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(cb, "worktrees", return_value=[self.main_wt, self.wt]), \
                mock.patch.object(cb, "busy_paths", return_value=set()), \
                mock.patch.object(cb, "git_files_mtime", return_value=OLD), \
                mock.patch.dict(os.environ, {"PATH": self.empty_path}), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = cb.main(list(argv))
        return rc, out.getvalue(), err.getvalue()

    def test_file_rewrite_counts_as_use(self):
        self.assertFalse(cb.changed_since([self.release], time.time() - 86400))
        rewrite(os.path.join(self.release, "tsgo"))
        self.assertEqual(os.lstat(self.release).st_mtime, OLD)
        self.assertTrue(cb.changed_since([self.release], time.time() - 86400))

    def test_fingerprint_rewrite_counts_as_use(self):
        rewrite(os.path.join(self.release, ".fingerprint/unit/dep-lib"))
        self.assertTrue(cb.changed_since([self.release], time.time() - 86400))

    def test_walk_stops_at_max_depth(self):
        rewrite(os.path.join(self.release, "incremental/c/s/q/deep"))
        self.assertFalse(cb.changed_since([self.release], time.time() - 86400))

    def test_dry_run_lists_idle_dirs_without_go(self):
        rc, out, _ = self.run_main()
        self.assertEqual(rc, 0)
        self.assertIn(f"would remove {self.release}\n", out)
        self.assertIn(f"would remove {self.gocache}\n", out)
        self.assertIn("dry run: 2 dirs.", out)
        self.assertTrue(os.path.exists(os.path.join(self.release, "tsgo")))

    def test_go_cache_inside_cargo_dir(self):
        # Listed once, with its Cargo dir, but its own entries (7 levels under release/) still count as use.
        cache = os.path.join(self.release, "build/pkg/out/gocache")
        make_tree(cache, {"trim.txt": "x", "README": GO_README, "0a/entry-d": "x"})
        os.utime(os.path.dirname(cache), (OLD, OLD))
        rc, out, _ = self.run_main()
        self.assertEqual(rc, 0)
        self.assertNotIn(cache, out)
        self.assertIn("dry run: 2 dirs.", out)
        rewrite(os.path.join(cache, "0a/entry-d"))
        self.assertIn("dry run: 0 dirs.", self.run_main()[1])

    def test_failed_remove_is_counted_and_exits_1(self):
        with mock.patch.object(cb.shutil, "rmtree", side_effect=OSError("denied")) as rmtree:
            rc, out, err = self.run_main("--apply")
        self.assertEqual(rmtree.call_count, 2)
        self.assertEqual(rc, 1)
        self.assertIn(f"failed to remove {self.release}: denied", err)
        self.assertIn("0 dirs removed, 2 failed", out)

    def test_symlinked_target_is_skipped(self):
        real = os.path.join(self.tmp, "shared-target")
        os.rename(os.path.join(self.wt, "target"), real)
        os.symlink(real, os.path.join(self.wt, "target"))
        rc, out, _ = self.run_main()
        self.assertEqual(rc, 0)
        self.assertIn("dry run: 0 dirs.", out)

    def test_unreadable_go_readme_is_not_a_cache(self):
        readme = os.path.join(self.gocache, "README")
        os.remove(readme)
        os.symlink(os.path.join(self.tmp, "missing"), readme)
        self.assertEqual(cb.go_cache_dirs(self.wt), [])

    def test_git_failure_counts_as_used(self):
        with mock.patch.dict(os.environ, {"GIT_CEILING_DIRECTORIES": self.tmp}):
            self.assertEqual(cb.git_files_mtime(self.wt), float("inf"))

    def test_bad_arguments_exit_2(self):
        for argv in (["--aply"], ["--days"], ["--days", "x"], ["--app"]):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as e:
                cb.main(argv)
            self.assertEqual(e.exception.code, 2)

    def test_timer_refuses_path_systemd_would_split(self):
        home = os.path.join(self.tmp, "home")
        with mock.patch.object(cb, "__file__", os.path.join(self.tmp, "a b%h/clean-builds.py")), \
                mock.patch.dict(os.environ, {"HOME": home}), \
                mock.patch.object(cb.subprocess, "run", side_effect=AssertionError("systemctl ran")), \
                self.assertRaises(SystemExit):
            cb.install_timer()
        self.assertFalse(os.path.exists(home))


if __name__ == "__main__":
    unittest.main()
