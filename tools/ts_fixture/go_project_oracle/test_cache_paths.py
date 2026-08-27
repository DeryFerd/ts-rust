#!/usr/bin/env python3
"""Check output and module-cache paths before the oracle helper can invoke Go."""

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

    def run_helper(
        self, cache: str | None, *, config: Path | None = None, output: Path | None = None,
    ) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment.pop("GOMODCACHE", None)
        environment["TS_GO_ORACLE_DOWNLOAD_PINNED"] = "0"
        if cache is not None:
            environment["GOMODCACHE"] = cache
        return subprocess.run(
            [
                "bash", str(self.helper), "/go-must-not-run", str(self.upstream),
                str(config or self.config), str(output or self.output), "prepare",
            ],
            env=environment, text=True, capture_output=True, check=False,
        )

    def assert_rejected(
        self, cache: str | None, message: str, *,
        config: Path | None = None, output: Path | None = None,
    ) -> None:
        result = self.run_helper(cache, config=config, output=output)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn(message, result.stderr)
        self.assertFalse((output or self.output).exists())

    def config_link(
        self, *, requested_git: bool = False, physical_git: bool = False,
    ) -> tuple[Path, Path, Path, Path]:
        requested_root = self.directory / "requested-project"
        physical_root = self.directory / "physical-project"
        link = requested_root / "configs" / "tsconfig.json"
        target = physical_root / "configs" / "tsconfig.json"
        link.parent.mkdir(parents=True)
        target.parent.mkdir(parents=True)
        target.write_text('{"compilerOptions":{"noEmit":true},"files":[]}\n', encoding="utf-8")
        link.symlink_to(os.path.relpath(target, link.parent))
        for root, enabled in [(requested_root, requested_git), (physical_root, physical_git)]:
            if enabled:
                subprocess.run(["git", "-C", str(root), "init", "-q"], check=True, capture_output=True)
                subprocess.run(
                    [
                        "git", "-C", str(root), "-c", "user.name=Path control",
                        "-c", "user.email=path-control@example.invalid",
                        "commit", "-q", "--allow-empty", "-m", "Initialize path control",
                    ],
                    check=True, capture_output=True,
                )
        return link, target, requested_root, physical_root

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

    def test_config_symlink_protects_both_config_directories_from_output(self) -> None:
        link, target, _, _ = self.config_link()
        for directory in [link.parent, target.parent]:
            with self.subTest(directory=directory):
                self.assert_rejected(
                    None, "Output must be outside the upstream and config directories",
                    config=link, output=directory / "oracle-output",
                )

    def test_config_symlink_protects_both_git_roots_from_output(self) -> None:
        link, _, requested_root, physical_root = self.config_link(requested_git=True, physical_git=True)
        for root in [requested_root, physical_root]:
            with self.subTest(root=root):
                self.assert_rejected(
                    None, "Output must be outside the project checkout",
                    config=link, output=root / "oracle-output",
                )

    def test_config_symlink_protects_both_config_directories_from_cache(self) -> None:
        link, target, _, _ = self.config_link()
        for directory in [link.parent, target.parent]:
            with self.subTest(directory=directory):
                self.assert_rejected(
                    str(directory / "module-cache"),
                    "Module cache must be outside upstream and project sources", config=link,
                )

    def test_config_symlink_protects_both_git_roots_from_cache(self) -> None:
        link, _, requested_root, physical_root = self.config_link(requested_git=True, physical_git=True)
        for root in [requested_root, physical_root]:
            with self.subTest(root=root):
                self.assert_rejected(
                    str(root / "module-cache"),
                    "Module cache must be outside upstream and project sources", config=link,
                )

    def test_cache_must_not_contain_the_physical_config_directory(self) -> None:
        link, _, _, physical_root = self.config_link()
        self.assert_rejected(
            str(physical_root), "Module cache must not contain upstream or project sources",
            config=link,
        )

    def test_safe_config_symlink_keeps_requested_config_and_project(self) -> None:
        link, target, requested_root, _ = self.config_link(requested_git=True, physical_git=True)
        original = target.read_bytes()
        result = self.run_helper(None, config=link)
        self.assertEqual(result.returncode, 0, result.stderr)
        manifest = json.loads((self.output / "build.json").read_text())
        self.assertEqual(manifest["project"]["config_path"], str(link))
        self.assertEqual(manifest["project"]["root"], str(requested_root))
        self.assertEqual(manifest["state"], "prepared")
        self.assertEqual(manifest["go"]["executable"], "/go-must-not-run")
        self.assertIsNone(manifest["go"]["version"])
        self.assertIsNone(manifest["executable"])
        self.assertEqual(target.read_bytes(), original)
        self.assertEqual(link.resolve(), target)

    def test_safe_config_symlink_does_not_replace_an_unset_requested_project(self) -> None:
        link, _, _, _ = self.config_link(physical_git=True)
        result = self.run_helper(None, config=link)
        self.assertEqual(result.returncode, 0, result.stderr)
        manifest = json.loads((self.output / "build.json").read_text())
        self.assertEqual(manifest["project"]["config_path"], str(link))
        self.assertIsNone(manifest["project"]["root"])
        self.assertIsNone(manifest["go"]["version"])
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
