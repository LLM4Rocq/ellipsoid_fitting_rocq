#!/usr/bin/env python3
"""Harmless failure-path tests for the check runner; no Rocq code is run."""

import subprocess
import tempfile
import types
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
runner = types.ModuleType("run_checks")
runner.__file__ = str(ROOT / "scripts/run_checks.py")
exec(compile(Path(runner.__file__).read_bytes(), runner.__file__, "exec"), runner.__dict__)


class RunnerFailures(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.checks = self.root / "build/checks"
        self.root_patch = patch.object(runner, "ROOT", self.root)
        self.checks_patch = patch.object(runner, "CHECKS", self.checks)
        self.root_patch.start()
        self.checks_patch.start()

    def tearDown(self):
        self.checks_patch.stop()
        self.root_patch.stop()
        self.tmp.cleanup()

    def test_redirected_output_is_refused_without_touching_target(self):
        target = self.root / "target"
        target.mkdir()
        sentinel = target / "sentinel"
        sentinel.write_text("preserve")
        self.checks.parent.mkdir()
        self.checks.symlink_to(target, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            runner.prepare_checks_directory()
        self.assertEqual(sentinel.read_text(), "preserve")

    def test_redirected_build_parent_is_refused(self):
        target = self.root / "target"
        target.mkdir()
        (self.root / "build").symlink_to(target, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            runner.prepare_checks_directory()
        self.assertEqual(list(target.iterdir()), [])

    def test_stale_child_link_is_removed_without_touching_target(self):
        runner.prepare_checks_directory()
        target = self.root / "target"
        target.write_text("preserve")
        (self.checks / "old.out").symlink_to(target)
        runner.prepare_checks_directory()
        self.assertEqual(target.read_text(), "preserve")
        self.assertEqual(list(self.checks.iterdir()), [])

    def test_failed_compile_publishes_no_report(self):
        runner.prepare_checks_directory()
        check = types.SimpleNamespace(source="check/Example.v", flags=[], expect=("empty",))
        with patch.object(runner.subprocess, "run", return_value=types.SimpleNamespace(returncode=1)):
            _, status, _ = runner.compile_check(check)
        self.assertNotEqual(status, 0)
        self.assertFalse((self.checks / "Example.out").exists())
        self.assertFalse((self.checks / "Example.tmp").exists())
        self.assertFalse((self.checks / "manifest.json").exists())

    def test_timed_out_compile_publishes_no_report(self):
        runner.prepare_checks_directory()
        check = types.SimpleNamespace(source="check/Example.v", flags=[], expect=("empty",))
        with patch.object(runner.subprocess, "run", side_effect=subprocess.TimeoutExpired("rocq", 1)):
            _, status, lines = runner.compile_check(check)
        self.assertNotEqual(status, 0)
        self.assertIn("exceeded", lines[0])
        self.assertFalse((self.checks / "Example.out").exists())

    def test_kernel_failure_is_retained_only_as_diagnostic(self):
        runner.prepare_checks_directory()
        with patch.object(runner.subprocess, "run", return_value=types.SimpleNamespace(returncode=1)):
            self.assertNotEqual(runner.run_rocqchk(["EllipsoidFitting.Example"]), 0)
        self.assertTrue((self.checks / "rocqchk.failed").exists())
        self.assertFalse((self.checks / "rocqchk.out").exists())

    def test_kernel_timeout_has_a_diagnostic_and_no_published_report(self):
        runner.prepare_checks_directory()
        with patch.object(runner.subprocess, "run", side_effect=subprocess.TimeoutExpired("rocqchk", 1)):
            self.assertNotEqual(runner.run_rocqchk(["EllipsoidFitting.Example"]), 0)
        self.assertIn("exceeded", (self.checks / "rocqchk.failed").read_text())
        self.assertFalse((self.checks / "rocqchk.out").exists())

    def test_theories_are_in_kernel_inventory(self):
        (self.root / "_CoqProject").write_text(
            "-Q theories EllipsoidFitting\nlibrary/a.v\ntheories/b.v\n"
            "extension/c.v\napplications/d.v\n")
        with patch.object(runner, "ROOT", ROOT):
            checker = runner.load_checker()
        checker.ROOT = self.root
        checker.validated_sources = lambda: ["library/a.v", "theories/b.v", "extension/c.v", "applications/d.v"]
        checker.CHECK_FILES = [types.SimpleNamespace(source="check/Example.v")]
        self.assertEqual(runner.kernel_modules(checker), [
            "GaussianAnalysis.a", "EllipsoidFitting.b", "EllipsoidUniversality.c",
            "GaussianApplications.d", "Checks.Example"])


if __name__ == "__main__":
    unittest.main()
