#!/usr/bin/env python3
"""Check module-cache rejection before the oracle helper can invoke Go."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class CachePathTests(unittest.TestCase):
    helper: Path
    upstream: Path
    config: Path
    output_parent: Path
    project_root: Path

    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory(dir=self.output_parent)
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.output = self.directory / "output"

    def run_helper(self, cache: str | None) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment.pop("GOMODCACHE", None)
        environment["TS_GO_ORACLE_DOWNLOAD_PINNED"] = "0"
        if cache is not None:
            environment["GOMODCACHE"] = cache
        return subprocess.run(
            [
                "bash", str(self.helper), "/go-must-not-run", str(self.upstream),
                str(self.config), str(self.output), "prepare",
            ],
            env=environment, text=True, capture_output=True, check=False,
        )

    def assert_rejected(self, cache: str, message: str) -> None:
        result = self.run_helper(cache)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn(message, result.stderr)
        self.assertFalse(self.output.exists())

    def test_inherited_upstream_cache_is_rejected(self) -> None:
        self.assert_rejected(
            str(self.upstream / "oracle-cache-must-not-be-created"),
            "Module cache must be outside upstream and project sources",
        )

    def test_inherited_project_cache_is_rejected(self) -> None:
        self.assert_rejected(
            str(self.project_root / "oracle-cache-must-not-be-created"),
            "Module cache must be outside upstream and project sources",
        )

    def test_symlink_into_sources_is_rejected(self) -> None:
        link = self.directory / "cache-link"
        link.symlink_to(self.upstream, target_is_directory=True)
        self.assert_rejected(
            str(link / "oracle-cache-must-not-be-created"),
            "Module cache must be outside upstream and project sources",
        )

    def test_relative_cache_is_rejected(self) -> None:
        self.assert_rejected("relative-cache", "Module cache must be an absolute path")

    def test_cache_outside_output_parent_is_rejected(self) -> None:
        self.assert_rejected(
            str(self.directory.parent / "outside-this-run-cache"),
            "Module cache must stay under the output parent",
        )

    def test_accepted_cache_uses_canonical_path(self) -> None:
        cache = self.directory / "cache"
        cache.mkdir()
        link = self.directory / "cache-link"
        link.symlink_to(cache, target_is_directory=True)
        result = self.run_helper(str(link))
        self.assertEqual(result.returncode, 0, result.stderr)
        manifest = json.loads((self.output / "build.json").read_text())
        self.assertIn(f"GOMODCACHE={cache.resolve()}", manifest["build"]["environment"])
        self.assertEqual(manifest["state"], "prepared")
        self.assertIsNone(manifest["go"]["version"])

    def test_default_cache_is_isolated(self) -> None:
        result = self.run_helper(None)
        self.assertEqual(result.returncode, 0, result.stderr)
        manifest = json.loads((self.output / "build.json").read_text())
        self.assertIn(
            f"GOMODCACHE={self.output / 'go-mod-cache'}",
            manifest["build"]["environment"],
        )
        self.assertIsNone(manifest["executable"])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("upstream", type=Path)
    parser.add_argument("config", type=Path)
    parser.add_argument("output_parent", type=Path)
    arguments = parser.parse_args()
    CachePathTests.helper = Path(__file__).resolve().parents[3] / "scripts/run-go-project-oracle.sh"
    CachePathTests.upstream = arguments.upstream.resolve()
    CachePathTests.config = arguments.config.resolve()
    CachePathTests.output_parent = arguments.output_parent.resolve()
    CachePathTests.output_parent.mkdir(parents=True, exist_ok=True)
    project = subprocess.run(
        ["git", "-C", str(CachePathTests.config.parent), "rev-parse", "--show-toplevel"],
        text=True, capture_output=True, check=True,
    )
    CachePathTests.project_root = Path(project.stdout.strip()).resolve()
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(CachePathTests)
    )
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
