#!/usr/bin/env python3
"""Harmless regression-runner cleanup tests; no git, Rocq or make is run
(the tests of run() run sh, sleep and printf only).

    python3 -I -B scripts/test_regression_cleanup.py
"""

import contextlib
import hashlib
import importlib.util
import io
import json
import signal
from pathlib import Path
import sys
import tempfile
import time
import types
import unittest
from unittest import mock

SOURCE = Path(__file__).with_name("run_regressions.py")
runner = types.ModuleType("regression_runner_under_test")
runner.__file__ = str(SOURCE)
exec(compile(SOURCE.read_text(), str(SOURCE), "exec"), runner.__dict__)
REAL_RUN = runner.run


class CleanupTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="regression-cleanup-test-")
        self.addCleanup(self.tmp.cleanup)
        self.copy = Path(self.tmp.name)
        (self.copy / "build/checks").mkdir(parents=True)
        (self.copy / "scripts").mkdir()
        self.output = self.copy / "build/report.txt"
        self.output.write_bytes(b"Axioms:\n  harmless : True\n")
        self.manifest = self.copy / "build/checks/manifest.json"
        self.manifest.write_text(json.dumps({"run_id": "test-only", "checks": [{
            "output": "build/report.txt", "output_sha256": "original"}]}))
        self.original = self.output.read_bytes(), self.manifest.read_bytes()
        self.patch = self.copy / "absent.diff"
        self.test = {"step": "checker", "repaired": {
            "expect": "fail", "message": "expected refusal"}}
        self.commands = []
        self.run_mock = mock.patch.object(runner, "run", side_effect=self.command).start()
        self.step_mock = mock.patch.object(runner, "step",
                                          return_value=(1, "expected refusal")).start()
        self.addCleanup(mock.patch.stopall)

    def command(self, cmd, cwd, env=None):
        self.commands.append(cmd)
        self.assertEqual(cwd, self.copy)
        if cmd[:2] == ["git", "apply"]:
            self.probe.write_text("original" if "-R" in cmd else "patched")
        return 0, "mock command only"

    def patch_fixture(self):
        self.patch = self.copy / "fixture.diff"
        self.patch.write_text("diff --git a/probe.txt b/probe.txt\n")
        self.probe = self.copy / "probe.txt"
        self.probe.write_text("original")

    def transform(self):
        self.test["transform"] = {"repaired": [{"output": "report.txt",
            "operation": "duplicate", "refresh_manifest": True}]}

    def execute(self):
        return runner.run_fixture(self.copy, "repaired", self.test, self.patch)

    def assert_restored(self):
        self.assertEqual((self.output.read_bytes(), self.manifest.read_bytes()), self.original)

    def test_normal_transform_is_restored(self):
        self.transform()
        def inspect(*args):
            self.assertEqual(self.output.read_bytes(), self.original[0] * 2)
            entry = json.loads(self.manifest.read_text())["checks"][0]
            self.assertEqual(entry["output_sha256"],
                             hashlib.sha256(self.output.read_bytes()).hexdigest())
            return 1, "expected refusal"
        self.step_mock.side_effect = inspect
        self.assertEqual(self.execute(), (1, "expected refusal", None))
        self.assert_restored()

    def test_preparation_failure_restores_mutated_output(self):
        self.transform()
        self.patch_fixture()
        self.manifest.write_text('{"checks": []}')
        self.original = self.output.read_bytes(), self.manifest.read_bytes()
        with self.assertRaisesRegex(ValueError, "exactly one output"):
            self.execute()
        self.assert_restored()
        self.assertEqual(self.probe.read_text(), "original")
        self.step_mock.assert_not_called()

    def test_overwritten_and_deleted_cache_entries_are_restored(self):
        source = self.copy / "scripts/probe.py"
        source.write_text("value = 0\n")
        cached = Path(importlib.util.cache_from_source(str(source)))
        cached.parent.mkdir()
        cached.write_bytes(b"original cached bytes")
        other = cached.parent / "other.pyc"
        other.write_bytes(b"other original bytes")
        link = cached.parent / "alias.pyc"
        link.symlink_to(other.name)
        self.test["pyc"] = {"repaired": {"scripts/probe.py": "value = 1\n"}}
        def inspect(*args):
            self.assertNotEqual(cached.read_bytes(), b"original cached bytes")
            cached.unlink()
            other.unlink()
            link.unlink()
            (cached.parent / "new.pyc").write_bytes(b"new")
            return 1, "expected refusal"
        self.step_mock.side_effect = inspect
        self.execute()
        self.assertEqual(cached.read_bytes(), b"original cached bytes")
        self.assertEqual(other.read_bytes(), b"other original bytes")
        self.assertTrue(link.is_symlink())
        self.assertEqual(link.readlink(), Path(other.name))
        self.assertFalse((cached.parent / "new.pyc").exists())
        self.assertFalse((self.copy / "build/regression-pyc-source.py").exists())

    def test_reverse_patch_failure_is_hard_failure_and_other_cleanup_continues(self):
        self.patch_fixture()
        self.transform()
        def command(cmd, cwd, env=None):
            if cmd[:3] == ["git", "apply", "-R"]:
                return 1, "simulated reverse failure"
            return self.command(cmd, cwd, env)
        self.run_mock.side_effect = command
        with self.assertRaisesRegex(runner.CleanupError, "reverse patch"):
            self.execute()
        self.assert_restored()
        self.assertEqual(self.probe.read_text(), "patched")

    def test_index_cleanup_failure_is_hard_failure(self):
        self.test["track"] = ["fixture.txt"]
        self.transform()
        def command(cmd, cwd, env=None):
            return (1, "simulated index failure") if cmd[:2] == ["git", "rm"] else (0, "ok")
        self.run_mock.side_effect = command
        with self.assertRaisesRegex(runner.CleanupError, "index fixture.txt"):
            self.execute()
        self.assert_restored()

    def test_step_exception_cleans_marker_and_restores_reports(self):
        self.transform()
        self.test["marker"] = "marker"
        marker = self.copy / "build/marker"
        def fail(*args):
            marker.write_text("fixture marker")
            raise RuntimeError("simulated step exception")
        self.step_mock.side_effect = fail
        with self.assertRaisesRegex(RuntimeError, "step exception"):
            self.execute()
        self.assertFalse(marker.exists())
        self.assert_restored()

    def test_missing_copy_restores_patch_and_fixture_tree(self):
        self.patch_fixture()
        self.test["files"] = {"fixture/source.v": "Definition value := 0.\n"}
        self.test["copy"] = {"repaired": [["missing.txt", "report.txt"]]}
        with self.assertRaisesRegex(runner.FixtureError, "does not exist"):
            self.execute()
        self.assertFalse((self.copy / "build/fixture").exists())
        self.assertEqual(self.probe.read_text(), "original")
        self.step_mock.assert_not_called()

    def test_failed_prerequisite_compile_restores_fixture(self):
        self.patch_fixture()
        self.test["files"] = {"fixture/source.v": "Definition value := 0.\n"}
        self.test["compile"] = [["fixture", "Fixture", "fixture/source.v"]]
        def command(cmd, cwd, env=None):
            if cmd[0] == "rocq":
                (self.copy / "build/fixture/partial.vo").write_text("partial fixture")
                return 1, "simulated compiler refusal"
            return self.command(cmd, cwd, env)
        self.run_mock.side_effect = command
        with self.assertRaisesRegex(runner.FixtureError, "does not compile"):
            self.execute()
        self.assertFalse((self.copy / "build/fixture").exists())
        self.assertEqual(self.probe.read_text(), "original")
        self.step_mock.assert_not_called()

    def test_existing_fixture_tree_is_preserved_and_refused(self):
        tree = self.copy / "build/fixture"
        tree.mkdir()
        (tree / "keep.txt").write_text("preserve")
        self.test["files"] = {"fixture/source.v": "Definition value := 0.\n"}
        with self.assertRaisesRegex(runner.FixtureError, "already exists"):
            self.execute()
        self.assertEqual((tree / "keep.txt").read_text(), "preserve")
        self.step_mock.assert_not_called()

    def test_main_stops_campaign_on_cleanup_failure(self):
        tests = self.copy / "metadata"
        for name in ["A", "B"]:
            directory = tests / name
            directory.mkdir(parents=True)
            (directory / "test.json").write_text(json.dumps(self.test))
        output = io.StringIO()
        with mock.patch.object(runner, "TESTS", tests), \
             mock.patch.object(runner, "run_fixture", side_effect=runner.CleanupError("reverse patch")) as execute, \
             mock.patch.object(sys, "argv", ["run_regressions.py", "--copy", str(self.copy),
                                             "--tree", "repaired", "A", "B"]), \
             contextlib.redirect_stdout(output):
            with self.assertRaisesRegex(SystemExit, "STOP A: cleanup failed"):
                runner.main()
        self.assertEqual(execute.call_count, 1)
        self.assertNotIn("agree", output.getvalue())
        self.run_mock.assert_not_called()

    def test_cleanup_oserror_is_hard_failure_and_other_cleanup_continues(self):
        # P1: an exists() test that raises during the cleanup (a parent
        # directory without search permission) must not skip the rest.
        self.patch_fixture()
        self.transform()
        self.test["files"] = {"fixture/source.v": "Definition value := 0.\n"}
        tree = self.copy / "build/fixture"
        original_exists = Path.exists
        blocked = []
        def exists(path, *args, **kwargs):
            if blocked and path == tree:
                raise PermissionError(13, "simulated lost search permission", str(path))
            return original_exists(path, *args, **kwargs)
        def inspect(*args):
            blocked.append(True)
            return 1, "expected refusal"
        self.step_mock.side_effect = inspect
        with mock.patch.object(Path, "exists", exists):
            with self.assertRaisesRegex(runner.CleanupError, "fixture directory"):
                self.execute()
        self.assert_restored()
        self.assertEqual(self.probe.read_text(), "original")

    def test_time_limit_kills_the_process_group(self):
        # P2: a command past the limit must leave no descendant running.
        work = self.copy / "p2"
        work.mkdir()
        with mock.patch.object(runner, "STEP_TIMEOUT", 1):
            with self.assertRaisesRegex(runner.StepTimeout, "process group was killed"):
                REAL_RUN(["sh", "-c", "(sleep 2; echo late > orphan.txt) & exec sleep 30"],
                         work)
        time.sleep(3)
        self.assertFalse((work / "orphan.txt").exists())

    def test_main_stops_campaign_on_step_timeout(self):
        tests = self.copy / "metadata"
        for name in ["A", "B"]:
            directory = tests / name
            directory.mkdir(parents=True)
            (directory / "test.json").write_text(json.dumps(self.test))
        output = io.StringIO()
        timeout = runner.StepTimeout("make check exceeded 7200 seconds")
        with mock.patch.object(runner, "TESTS", tests), \
             mock.patch.object(runner, "run_fixture", side_effect=timeout) as execute, \
             mock.patch.object(sys, "argv", ["run_regressions.py", "--copy", str(self.copy),
                                             "--tree", "repaired", "A", "B"]), \
             contextlib.redirect_stdout(output):
            with self.assertRaisesRegex(SystemExit, "STOP A: make check exceeded"):
                runner.main()
        self.assertEqual(execute.call_count, 1)
        self.assertNotIn("agree", output.getvalue())
        self.run_mock.assert_not_called()

    def test_interrupt_kills_the_process_group(self):
        # P3: an interrupt of run() other than the time limit must not leave
        # the command or its descendants running.
        class Interrupt(BaseException):
            pass
        def interrupt(signum, frame):
            raise Interrupt()
        work = self.copy / "p3"
        work.mkdir()
        previous = signal.signal(signal.SIGALRM, interrupt)
        self.addCleanup(signal.signal, signal.SIGALRM, previous)
        signal.alarm(1)
        try:
            with self.assertRaises(Interrupt):
                REAL_RUN(["sh", "-c", "(sleep 2; echo late > int.txt) & exec sleep 30"], work)
        finally:
            signal.alarm(0)
        time.sleep(3)
        self.assertFalse((work / "int.txt").exists())

    def test_output_cut_at_the_limit_is_a_timeout(self):
        # A UTF-8 sequence cut by the kill must not turn the timeout into a
        # decoding error.
        with mock.patch.object(runner, "STEP_TIMEOUT", 1):
            with self.assertRaises(runner.StepTimeout):
                REAL_RUN(["sh", "-c", "printf '\\303'; exec sleep 30"], self.copy)

    def test_output_that_is_not_utf8_is_replaced(self):
        status, out = REAL_RUN(["sh", "-c", "printf 'a\\303b'"], self.copy)
        self.assertEqual((status, out), (0, "a\ufffdb"))

    def test_detached_process_is_killed_after_a_normal_return(self):
        work = self.copy / "detached"
        work.mkdir()
        status, _ = REAL_RUN(
            ["sh", "-c", "(sleep 2; echo late > detached.txt) >/dev/null 2>&1 &"], work)
        self.assertEqual(status, 0)
        time.sleep(3)
        self.assertFalse((work / "detached.txt").exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
