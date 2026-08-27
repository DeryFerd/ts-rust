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
        self, cache: str | None, *, config: Path | None = None, output: Path | str | None = None,
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

    def assert_canonical_output(self, output: Path, config: Path) -> None:
        manifest = json.loads((output / "build.json").read_text())
        self.assertEqual(manifest["state"], "prepared")
        self.assertEqual(manifest["project"]["config_path"], str(config))
        self.assertIsNone(manifest["go"]["version"])
        self.assertIsNone(manifest["executable"])
        for key, directory in [
            ("GOCACHE", "go-cache"), ("GOMODCACHE", "go-mod-cache"),
            ("GOTMPDIR", "go-tmp"), ("TMPDIR", "go-tmp"),
        ]:
            self.assertIn(f"{key}={output / directory}", manifest["build"]["environment"])
        arguments = manifest["build"]["arguments"]
        for flag, name in [
            ("-modfile", "go.mod"), ("-overlay", "overlay.json"),
            ("-o", "project-oracle.test"),
        ]:
            self.assertEqual(arguments[arguments.index(flag) + 1], str(output / name))
        for overlay in manifest["instrumentation"]["overlays"]:
            replacement = Path(overlay["replacement_path"])
            self.assertEqual(replacement, output / "overlay" / replacement.name)
            self.assertTrue(replacement.is_file())

    def config_link(
        self, *, requested_git: bool = False, physical_git: bool = False,
        missing_target_parent: bool = False,
    ) -> tuple[Path, Path, Path, Path]:
        requested_root = self.directory / "requested-project"
        physical_root = self.directory / "physical-project"
        link = requested_root / "configs" / "tsconfig.json"
        target = physical_root / "configs" / "tsconfig.json"
        link.parent.mkdir(parents=True)
        if missing_target_parent:
            physical_root.mkdir()
        else:
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

    def test_output_traversal_does_not_create_protected_intermediates(self) -> None:
        link, target, requested_root, physical_root = self.config_link(
            requested_git=True, physical_git=True,
        )
        config_bytes = target.read_bytes()
        for index, project in enumerate([requested_root, physical_root]):
            with self.subTest(project=project):
                intermediate = project / "missing-output-parent"
                output = intermediate / ".." / ".." / f"oracle-output-{index}"
                destination = self.directory / f"oracle-output-{index}"
                result = self.run_helper(None, config=link, output=output)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertFalse(intermediate.exists())
                self.assert_canonical_output(destination, link)
        self.assertEqual(target.read_bytes(), config_bytes)

    def test_safe_output_aliases_use_canonical_writes(self) -> None:
        link, _, _, _ = self.config_link(requested_git=True, physical_git=True)
        parent = self.directory / "safe-output-parent"
        existing = parent / "existing"
        existing.mkdir(parents=True)
        alias = self.directory / "output-parent-link"
        alias.symlink_to(parent, target_is_directory=True)
        for output, destination in [
            (parent / "nested" / "output", parent / "nested" / "output"),
            (existing / ".." / "dotdot-output", parent / "dotdot-output"),
            (alias / "symlink-output", parent / "symlink-output"),
        ]:
            with self.subTest(output=output):
                result = self.run_helper(None, config=link, output=output)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_canonical_output(destination, link)
        self.assertTrue(alias.is_symlink())
        self.assertEqual(alias.resolve(), parent)

    def test_existing_canonical_output_is_rejected_without_parent_writes(self) -> None:
        destination = self.directory / "existing-output"
        destination.mkdir()
        marker = destination / "keep.txt"
        marker.write_text("unchanged\n", encoding="utf-8")
        intermediate = self.directory / "missing-output-parent"
        output = intermediate / ".." / destination.name
        self.assert_rejected(None, "Output must not already exist", output=output)
        self.assertFalse(intermediate.exists())
        self.assertEqual(marker.read_text(encoding="utf-8"), "unchanged\n")
        self.assertEqual(list(destination.iterdir()), [marker])

    def test_existing_output_symlinks_are_rejected(self) -> None:
        for target_exists in [False, True]:
            with self.subTest(target_exists=target_exists):
                target = self.directory / f"output-target-{target_exists}"
                if target_exists:
                    target.mkdir()
                link = self.directory / f"output-link-{target_exists}"
                link.symlink_to(target, target_is_directory=True)
                result = self.run_helper(None, output=link)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("Output must not already exist", result.stderr)
                self.assertTrue(link.is_symlink())
                self.assertEqual(link.readlink(), target)
                self.assertEqual(target.exists(), target_exists)
                if target_exists:
                    self.assertEqual(list(target.iterdir()), [])

    def test_hidden_final_output_symlinks_are_rejected(self) -> None:
        for index, suffix in enumerate([None, "/", "/.", "//.//./"]):
            with self.subTest(suffix=suffix):
                target = self.directory / f"absent-output-target-{index}"
                link = self.directory / f"final-output-link-{index}"
                link.symlink_to(target.name, target_is_directory=True)
                intermediate = self.directory / f"missing-output-parent-{index}"
                output = (
                    str(intermediate / ".." / link.name)
                    if suffix is None else str(link) + suffix
                )
                result = self.run_helper(None, output=output)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("Output must not already exist", result.stderr)
                self.assertFalse(target.exists())
                self.assertFalse(intermediate.exists())
                self.assertTrue(link.is_symlink())
                self.assertEqual(link.readlink(), Path(target.name))

    def test_new_outputs_allow_trailing_separators_and_dots(self) -> None:
        for index, suffix in enumerate(["/", "/.", "/./", "//.//./"]):
            with self.subTest(suffix=suffix):
                destination = self.directory / f"new-output-{index}"
                result = self.run_helper(None, output=str(destination) + suffix)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_canonical_output(destination, self.config)

    def test_output_final_entry_uses_the_physical_parent(self) -> None:
        physical = self.directory / "physical-output-parent"
        child = physical / "child"
        child.mkdir(parents=True)
        lexical = self.directory / "lexical-output-parent"
        lexical.mkdir()
        parent_link = lexical / "parent-link"
        parent_target = Path(os.path.relpath(child, lexical))
        parent_link.symlink_to(parent_target, target_is_directory=True)

        decoy = lexical / "new-output"
        decoy.symlink_to("unused-decoy-target", target_is_directory=True)
        output = parent_link / ".." / "new-output"
        result = self.run_helper(None, output=output)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_canonical_output(physical / "new-output", self.config)
        self.assertTrue(decoy.is_symlink())
        self.assertFalse((lexical / "unused-decoy-target").exists())

        final_link = physical / "final-output-link"
        final_link.symlink_to("absent-output-target", target_is_directory=True)
        missing = physical / "missing-output-parent"
        output = parent_link / ".." / missing.name / ".." / final_link.name
        result = self.run_helper(None, output=output)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("Output must not already exist", result.stderr)
        self.assertTrue(final_link.is_symlink())
        self.assertEqual(final_link.readlink(), Path("absent-output-target"))
        self.assertFalse((physical / "absent-output-target").exists())
        self.assertFalse(missing.exists())
        self.assertTrue(parent_link.is_symlink())
        self.assertEqual(parent_link.readlink(), parent_target)

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

    def test_missing_config_parent_rejects_output_inside_project(self) -> None:
        link, target, _, physical_root = self.config_link(
            physical_git=True, missing_target_parent=True,
        )
        for index, config in enumerate([target, link]):
            with self.subTest(config=config):
                self.assert_rejected(
                    None, "Config parent directories must exist", config=config,
                    output=physical_root / f"oracle-output-{index}",
                )

    def test_missing_config_parent_rejects_cache_inside_project(self) -> None:
        link, target, _, physical_root = self.config_link(
            physical_git=True, missing_target_parent=True,
        )
        for index, config in enumerate([target, link]):
            with self.subTest(config=config):
                self.assert_rejected(
                    str(physical_root / f"module-cache-{index}"),
                    "Config parent directories must exist", config=config,
                    output=self.directory / f"oracle-output-{index}",
                )

    def test_missing_config_parent_rejects_prepare_with_safe_paths(self) -> None:
        link, target, _, _ = self.config_link(
            physical_git=True, missing_target_parent=True,
        )
        for index, config in enumerate([target, link]):
            with self.subTest(config=config):
                self.assert_rejected(
                    None, "Config parent directories must exist", config=config,
                    output=self.directory / f"oracle-output-{index}",
                )

    def test_missing_intermediate_config_parent_is_not_normalized_away(self) -> None:
        link, target, _, _ = self.config_link()
        missing = target.parent / "missing"
        config = missing / ".." / target.name
        absolute_link = link.parent / "absolute-missing-parent.json"
        absolute_link.symlink_to(config)
        relative_link = link.parent / "relative-missing-parent.json"
        relative_link.symlink_to(
            Path(os.path.relpath(target.parent, link.parent)) / "missing" / ".." / target.name,
        )
        directory_link = link.parent / "missing-parent-directory"
        directory_link.symlink_to(missing / "..", target_is_directory=True)
        for index, config in enumerate([
            config, absolute_link, relative_link, directory_link / target.name,
        ]):
            with self.subTest(config=config):
                self.assert_rejected(
                    None, "Config parent directories must exist", config=config,
                    output=self.directory / f"oracle-output-{index}",
                )
        self.assertFalse(missing.exists())

    def test_existing_intermediate_config_parent_keeps_requested_paths(self) -> None:
        link, target, requested_root, physical_root = self.config_link(
            requested_git=True, physical_git=True,
        )
        existing = target.parent / "existing"
        existing.mkdir()
        for name in [target.name, "absent.json"]:
            config = existing / ".." / name
            config_link = link.parent / f"parent-{name}"
            config_link.symlink_to(
                Path(os.path.relpath(target.parent, link.parent)) / "existing" / ".." / name,
            )
            for index, config in enumerate([config, config_link]):
                with self.subTest(config=config):
                    output = self.directory / f"oracle-output-{name}-{index}"
                    result = self.run_helper(None, config=config, output=output)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    manifest = json.loads((output / "build.json").read_text())
                    self.assertEqual(manifest["project"]["config_path"], str(config))
                    self.assertEqual(
                        manifest["project"]["root"],
                        str(requested_root if config == config_link else physical_root),
                    )
                    self.assertEqual(manifest["state"], "prepared")
                    self.assertIsNone(manifest["go"]["version"])
                    self.assertIsNone(manifest["executable"])
        self.assertFalse((target.parent / "absent.json").exists())

    def test_missing_config_file_with_existing_parent_remains_preparable(self) -> None:
        link, target, _, physical_root = self.config_link(physical_git=True)
        missing = target.parent / "absent.json"
        missing_link = link.parent / "absent.json"
        missing_link.symlink_to(os.path.relpath(missing, missing_link.parent))
        for index, config in enumerate([missing, missing_link]):
            with self.subTest(config=config):
                output = self.directory / f"oracle-output-{index}"
                result = self.run_helper(None, config=config, output=output)
                self.assertEqual(result.returncode, 0, result.stderr)
                manifest = json.loads((output / "build.json").read_text())
                self.assertEqual(manifest["project"]["config_path"], str(config))
                self.assertEqual(
                    manifest["project"]["root"], str(physical_root) if config == missing else None,
                )
                self.assertEqual(manifest["state"], "prepared")
                self.assertIsNone(manifest["go"]["version"])
                self.assertIsNone(manifest["executable"])
                self.assertFalse(missing.exists())


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
