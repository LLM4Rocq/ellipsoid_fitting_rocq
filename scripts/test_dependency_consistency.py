#!/usr/bin/env python3
"""Check Rocq's rejection of a stale dependent .vo with harmless fixtures.

    opam exec --switch=rocq-analysis -- \
        python3 -I -B scripts/test_dependency_consistency.py

Requires Rocq and rocqchk 9.1.1 on PATH. A fresh directory under
build/dependency-tests holds two small modules and a loading probe. After A
changes, stale B must fail both loading and kernel checking with the specific
inconsistent-assumptions diagnostic. Rebuilding B must restore both successes.
No project module, dependency file, Elpi program or unsafe feature is used.
This tests E33's consistency mechanism, not a historical successful bypass or
the separate rocq dep comment-reading discrepancy. It never runs make.
"""
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / "build" / "dependency-tests"
VERSION = "9.1.1"
TIMEOUT = 30
INCONSISTENT = re.compile(r"inconsistent assumptions", re.IGNORECASE)
A_INITIAL = "Definition value : nat := 0.\n"
A_REVISED = "Definition value : nat := 1.\n"
B_SOURCE = ("From DependencyFixture Require Import A.\n"
            "Definition copied : nat := A.value.\n"
            "Lemma copiedE : copied = A.value.\n"
            "Proof. reflexivity. Qed.\n")
LOAD_SOURCE = ("From DependencyFixture Require Import B.\n"
               "Check B.copiedE.\n")


class TestFailure(RuntimeError):
    pass


def executable(name, version_prefix):
    found = shutil.which(name)
    if found is None:
        raise TestFailure(f"{name} is not on PATH; use the pinned Rocq {VERSION} toolchain")
    path = str(Path(found).resolve())
    result = subprocess.run([path, "--version"], capture_output=True, text=True,
                            timeout=TIMEOUT)
    lines = result.stdout.splitlines()
    if result.returncode or not lines or lines[0] != version_prefix + VERSION:
        raise TestFailure(f"unexpected {name} version: " +
                          (result.stdout + result.stderr).strip())
    return path, lines[0]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    rocq, rocq_version = executable("rocq", "The Rocq Prover, version ")
    rocqchk, checker_version = executable("rocqchk", "The Rocq Proof Checker, version ")
    for path in (ROOT / "build", WORK):
        if path.is_symlink():
            raise TestFailure(f"refusing symlinked scratch directory: {path}")
    WORK.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="run-", dir=WORK))
    report = {"test": "E33 dependency consistency", "status": "running",
              "rocq": rocq, "rocq_version": rocq_version,
              "rocqchk": rocqchk, "rocqchk_version": checker_version,
              "work": str(work), "steps": []}
    loadpath = ["-Q", str(work), "DependencyFixture"]

    def run(name, command, stale=False):
        result = subprocess.run(command, cwd=work, capture_output=True, text=True,
                                timeout=TIMEOUT)
        stdout, stderr = name + ".stdout", name + ".stderr"
        (work / stdout).write_text(result.stdout)
        (work / stderr).write_text(result.stderr)
        report["steps"].append({"name": name, "command": command,
                                "returncode": result.returncode,
                                "expected": "inconsistent assumptions" if stale else "success",
                                "stdout": stdout, "stderr": stderr})
        detail = result.stdout + result.stderr
        if stale:
            if result.returncode == 0 or not INCONSISTENT.search(detail):
                raise TestFailure(f"{name}: expected inconsistent assumptions, "
                                  f"got exit {result.returncode}: {detail.strip()}")
        elif result.returncode:
            raise TestFailure(f"{name}: exit {result.returncode}: {detail.strip()}")
        print(f"{name}: {'stale dependency refused' if stale else 'success'}", flush=True)

    def compile_file(name, source, stale=False):
        run(name, [rocq, "compile", "-q", "-noglob", *loadpath, source], stale)

    def kernel_check(name, stale=False):
        run(name, [rocqchk, "-silent", *loadpath, "DependencyFixture.B"], stale)

    try:
        (work / "A.v").write_text(A_INITIAL)
        (work / "B.v").write_text(B_SOURCE)
        (work / "Load.v").write_text(LOAD_SOURCE)
        report["sources"] = {"A_initial": A_INITIAL, "A_revised": A_REVISED,
                             "B": B_SOURCE, "Load": LOAD_SOURCE}
        compile_file("01-initial-A", "A.v")
        compile_file("02-initial-B", "B.v")
        compile_file("03-initial-load", "Load.v")
        kernel_check("04-initial-kernel")
        initial_a, initial_b = digest(work / "A.vo"), digest(work / "B.vo")
        (work / "A.v").write_text(A_REVISED)
        compile_file("05-revised-A-only", "A.v")
        if digest(work / "A.vo") == initial_a:
            raise TestFailure("changing A's definition did not change its compiled object")
        if digest(work / "B.vo") != initial_b:
            raise TestFailure("B changed before the stale-dependency checks")
        compile_file("06-stale-load", "Load.v", stale=True)
        kernel_check("07-stale-kernel", stale=True)
        if digest(work / "B.vo") != initial_b:
            raise TestFailure("a stale-dependency probe changed B.vo")
        compile_file("08-rebuild-B", "B.v")
        if digest(work / "B.vo") == initial_b:
            raise TestFailure("rebuilding B did not record the changed dependency")
        compile_file("09-rebuilt-load", "Load.v")
        kernel_check("10-rebuilt-kernel")
        report["object_hashes"] = {
            "initial_A": initial_a, "revised_A": digest(work / "A.vo"),
            "initial_B": initial_b, "rebuilt_B": digest(work / "B.vo")}
        report["status"] = "pass"
    except (TestFailure, subprocess.TimeoutExpired, OSError) as error:
        report["status"], report["error"] = "fail", str(error)
        raise
    finally:
        (work / "result.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"evidence: {work / 'result.json'}", flush=True)
    print("E33 consistency mechanism: pass (10 checked steps)")


if __name__ == "__main__":
    try:
        main()
    except (TestFailure, subprocess.TimeoutExpired, OSError) as error:
        sys.exit(f"dependency consistency test failed: {error}")
