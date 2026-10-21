#!/usr/bin/env python3
"""Harmless fixture tests of source_inventory.py; no Rocq or project mutation.

Run: python3 -I -B scripts/test_source_inventory.py
The source loader ignores bytecode and does not import from the checkout.
Temporary fixtures contain only a trivial natural-number definition. Real
Git tests use local empty repositories and a fresh local clone.
"""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import types
import unittest


MODULE = Path(__file__).absolute().with_name("source_inventory.py")
inventory = types.ModuleType("source_inventory")
inventory.__file__ = str(MODULE)
exec(compile(MODULE.read_bytes(), str(MODULE), "exec"), inventory.__dict__)
OPTIONS = ("-Q library GaussianAnalysis", "-arg -q")
SOURCE = "Definition inventory_example : nat := 0.\n"


def stage(path, mode="100644", number="0"):
    return (f"{mode} {'1' * 40} {number}\t{path}\0").encode()


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="source-inventory-")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "repo"
        self.root.mkdir()
        self.make_fixture()

    def make_fixture(self):
        for top in inventory.PROTECTED_ROOTS:
            (self.root / top).mkdir()
        self.sources = [f"{top}/part/example.v" for top in inventory.SOURCE_ROOTS]
        for name in self.sources:
            path = self.root / name
            path.parent.mkdir()
            path.write_text(SOURCE)
        (self.root / "Makefile").write_text("all:\n\t@true\n")
        (self.root / "AGENTS.md").write_text("Fixture only.\n")
        (self.root / "CLAUDE.md").symlink_to("AGENTS.md")
        (self.root / "check" / "Probe.v").write_text(SOURCE)
        (self.root / "scripts" / "probe.py").write_text("pass\n")
        self.write_project(self.sources)

    def write_project(self, sources, options=OPTIONS):
        (self.root / "_CoqProject").write_text("\n".join(list(options) + list(sources)) + "\n")

    def inspect(self, tracked=b""):
        return inventory.inspect_sources(self.root, OPTIONS, tracked_entries=tracked)

    def assert_rejected(self, fragment, tracked=b""):
        result = self.inspect(tracked)
        self.assertEqual(result["sources"], [])
        self.assertTrue(any(fragment in message for message in result["failures"]), result)

    def test_clean_and_root_claude(self):
        result = self.inspect(stage("CLAUDE.md", "120000"))
        self.assertEqual(result["failures"], [])
        self.assertEqual(result["sources"], self.sources)
        self.assertEqual(result["discovered"], sorted(self.sources))
        self.assertIn("check/Probe.v", result["files"])
        self.assertNotIn("check/Probe.v", result["sources"])

    def test_new_registered_source_each_root(self):
        for top in inventory.SOURCE_ROOTS:
            with self.subTest(root=top):
                name = f"{top}/new.v"
                (self.root / name).write_text(SOURCE)
                self.write_project(self.sources + [name])
                result = self.inspect()
                self.assertEqual(result["failures"], [])
                self.assertEqual(result["sources"][-1], name)
                (self.root / name).unlink()
        self.write_project(self.sources)

    def test_root_and_component_directory_symlinks_each_root(self):
        for top in inventory.PROTECTED_ROOTS:
            for level in ("root", "component"):
                for outside in (False, True):
                    with self.subTest(root=top, level=level, outside=outside):
                        path = self.root / top
                        if level == "component":
                            path = path / "part"
                            path.mkdir(exist_ok=True)
                        target = (self.base if outside else self.root) / "payload"
                        path.rename(target)
                        path.symlink_to(target, target_is_directory=True)
                        self.assert_rejected("symlink")
                        path.unlink()
                        target.rename(path)

    def test_file_and_broken_symlinks_each_root(self):
        for top in inventory.PROTECTED_ROOTS:
            for outside in (False, True):
                with self.subTest(root=top, outside=outside):
                    target = (self.base if outside else self.root) / "payload.v"
                    target.write_text(SOURCE)
                    path = self.root / top / "linked.v"
                    path.symlink_to(target)
                    self.assert_rejected("symlink")
                    target.unlink()
                    self.assert_rejected("symlink")
                    path.unlink()

    def test_directory_link_cycle_and_broken_root(self):
        path = self.root / "library" / "loop"
        path.symlink_to(self.root / "library", target_is_directory=True)
        self.assert_rejected("symlink")
        path.unlink()
        top = self.root / "library"
        target = self.root / "saved"
        top.rename(target)
        top.symlink_to(self.root / "missing", target_is_directory=True)
        self.assert_rejected("symlink")

    def test_missing_and_unregistered_source_each_root(self):
        for name in self.sources:
            with self.subTest(source=name):
                path = self.root / name
                path.unlink()
                self.assert_rejected("registered source is not")
                path.write_text(SOURCE)
                self.write_project([source for source in self.sources if source != name])
                self.assert_rejected("unregistered source")
                self.write_project(self.sources)

    def test_duplicate_and_unsafe_literal_source_paths(self):
        self.write_project(self.sources + [self.sources[0]])
        self.assert_rejected("duplicate source")
        aliases = ["library/./part/example.v", "library//part/example.v",
                   "library/part/../part/example.v", "library/../example.v",
                   "/library/part/example.v", "library/part/example.v ",
                   " library/part/example.v", "library/part/example.v\t",
                   "library\\part\\example.v", "Library/part/example.v",
                   "library/part/x-y.v", "check/Probe.v", "library/.v",
                   "library/part/example.v\r", "library/part/example.v\u0085"]
        for alias in aliases:
            with self.subTest(alias=alias):
                self.write_project([alias] + self.sources[1:])
                self.assert_rejected("invalid source path or option")

    def test_unsafe_discovered_name_rejected(self):
        (self.root / "library" / "bad-name.v").write_text(SOURCE)
        self.assert_rejected("unregistered source")

    def test_project_and_makefile_symlinks(self):
        for name in ("_CoqProject", "Makefile"):
            with self.subTest(name=name):
                path = self.root / name
                target = self.root / "input_saved"
                path.rename(target)
                path.symlink_to(target)
                self.assert_rejected(f"{name}: protected input is a symlink")
                path.unlink()
                target.rename(path)

    def test_missing_and_nonregular_inputs(self):
        project = self.root / "_CoqProject"
        project.unlink()
        self.assert_rejected("_CoqProject: cannot inspect")
        project.mkdir()
        self.assert_rejected("_CoqProject: protected input must be an ordinary file")
        project.rmdir()
        self.write_project(self.sources)
        shutil.rmtree(self.root / "check")
        self.assert_rejected("check: cannot inspect")
        (self.root / "check").write_text("not a directory\n")
        self.assert_rejected("check: protected input must be an ordinary directory")

    @unittest.skipUnless(hasattr(os, "mkfifo"), "FIFO fixtures need os.mkfifo")
    def test_nonregular_tree_entry(self):
        os.mkfifo(self.root / "library" / "pipe.v")
        self.assert_rejected("not an ordinary file or directory")

    def test_options_exact_order_and_utf8(self):
        for options in (OPTIONS[::-1], OPTIONS[:1], OPTIONS + OPTIONS[:1], OPTIONS + ("-type-in-type",)):
            with self.subTest(options=options):
                self.write_project(self.sources, options)
                self.assert_rejected("option")
        (self.root / "_CoqProject").write_bytes(b"\xff\n")
        self.assert_rejected("cannot read UTF-8 input")

    def test_tracked_symlinks_even_when_working_tree_regular(self):
        for top in inventory.PROTECTED_ROOTS:
            for suffix in ("", "/alias", "/a space\nand\ta tab"):
                with self.subTest(root=top, suffix=suffix):
                    self.assert_rejected("mode 120000", stage(top + suffix, "120000"))
        self.assertEqual(self.inspect(stage("outside/alias", "120000"))["failures"], [])
        self.assertEqual(self.inspect(stage("library_not_protected/alias", "120000"))["failures"], [])

    def test_malformed_git_records_fail_closed(self):
        for records in (b"bad\0", b"100644 nohash 0\tname\0", stage("library/x")[:-1],
                        b"\0", "not bytes", stage("library/x", number="2"),
                        stage("library/x") + stage("library/x")):
            with self.subTest(records=records):
                self.assertTrue(self.inspect(records)["failures"])
                self.assertEqual(self.inspect(records)["sources"], [])

    def test_real_git_tracks_and_clone_preserves_link(self):
        def git(*args, cwd=None):
            return subprocess.run(["git", *args], cwd=cwd or self.root,
                                  check=True, capture_output=True)
        git("init", "-q")
        git("config", "user.name", "Inventory fixture")
        git("config", "user.email", "inventory@example.invalid")
        git("add", ".")
        git("-c", "commit.gpgsign=false", "commit", "-qm", "Harmless fixture")
        result = inventory.inspect_sources(self.root, OPTIONS)
        self.assertEqual(result["failures"], [])
        link = self.root / "library" / "tracked_link"
        link.symlink_to("part", target_is_directory=True)
        git("add", "library/tracked_link")
        git("-c", "commit.gpgsign=false", "commit", "-qm", "Harmless link fixture")
        clone = self.base / "clone"
        git("clone", "-q", "--local", str(self.root), str(clone))
        self.assertTrue((clone / "library" / "tracked_link").is_symlink())
        cloned = inventory.inspect_sources(clone, OPTIONS)
        self.assertTrue(any("mode 120000" in x for x in cloned["failures"]), cloned)
        link.unlink()
        link.mkdir()
        staged = inventory.inspect_sources(self.root, OPTIONS)
        self.assertTrue(any("mode 120000" in x for x in staged["failures"]), staged)

    def test_git_failure_is_a_diagnostic(self):
        result = inventory.inspect_sources(self.root, OPTIONS)
        self.assertTrue(any("git ls-files --stage: failed" in x for x in result["failures"]), result)
        self.assertEqual(result["sources"], [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
