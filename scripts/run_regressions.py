#!/usr/bin/env python3
"""Run the regression tests of the checker repair on a scratch copy.

    python3 -I -B scripts/run_regressions.py --copy DIR --tree baseline|repaired [ID...]

Run it where make and rocq are the pinned toolchain (in the container on the
VM, or in the opam switch). DIR is a built scratch copy of the repository
(git working tree): at commit 0ec5fcd for --tree baseline, where each test
must reproduce its bypass, and at the repaired commit for --tree repaired,
where each test must fail with its message. The copy must have passed make
check once, unchanged, so that the outputs of that run exist; the tests whose
step reads those outputs run first, and those that run make check last.

Each test is a directory check/regression/<ID>/ of this tree with test.json
and the patch of each tree (<tree>.diff, a diff of the repository, or none
when the test needs no change of a file). test.json gives

- "title": what the exploit does;
- "step": what is run once the patch is applied: "make" (make check on the
  baseline tree, make -f Makefile check on the repaired tree, where it is
  the command that runs the checker whatever files the tree holds; with
  JOBS=3 and CHECK_JOBS=3), "checker" (the checker alone, on the outputs of
  the last make check of the copy: scripts/check_sources.py with the report
  paths on the baseline, --reuse with the run identifier of the manifest on
  the repaired tree), or "environment" (make check, or the checker on the
  repaired tree, with the variables of "environment" set, and the files of
  "files" written under the copy's build/);
- for each tree, "expect": "pass" (exit status 0: the bypass is reproduced)
  or "fail" with "message", a regular expression that the output must match,
  and possibly its own "step";
- possibly, per tree, "write" (files under build/ to overwrite with the
  given text after the patch, such as an output of the last run), "delete"
  (files under build/ to remove), "copy" (pairs of files under build/, the
  first copied over the second), "pyc" (sources of scripts/ with the text
  to compile, by the Python that runs this driver, into an unchecked-hash
  bytecode file at the place where Python caches that source), and "track"
  (paths that git is made to track, with git add -f, during the step);
- possibly "compile", triples (directory, logical root, file) under build/:
  each file is compiled with rocq compile -q -noglob -Q build/<directory>
  <root> before the step, as a library outside the repository;
- possibly "marker", a path under build/ that the exploit creates when it
  runs code during the build: it is deleted before the step, and it must
  exist after the step where the test expects "pass", and must not exist
  where it expects "fail", unless the tree says otherwise ("marker": true
  or false next to "expect").

A tree for which a test has no patch and no step ("skip") is reported as
skipped, with the reason given. The patch is applied with git apply and
removed with git apply -R; files written under build/ are deleted. When the
step compiled nothing of the patched files (the checker alone), the files
that the patch touched get back their modification times, so that the next
make check does not rebuild what depends on them; after make check they keep
their new times, so that make rebuilds what was compiled from the patch. A test
agrees when the outcome is the expected one; the driver prints one line per
test and exits 0 only if every test agrees.

Every command runs in its own session, with a limit of STEP_TIMEOUT seconds.
Its whole process group is killed when it ends, at the limit, on an
interrupt and after a normal return, so that no process it started can
still write to the copy. Its output is decoded as UTF-8 with replacement
characters. A cleanup that fails, for any reason, and a command that
reaches the limit stop the campaign (STOP): the copy may no longer be the
unchanged tree that the next test needs."""

import argparse
import hashlib
import importlib.util
import json
import os
import py_compile
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TESTS = ROOT / "check" / "regression"
UNSAFE_ENVIRONMENT = ("ROCQPATH", "COQPATH", "ROCQLIB", "COQLIB", "OCAMLPATH",
                      "CAML_LD_LIBRARY_PATH", "ROCQRC", "COQRC", "XDG_CONFIG_HOME",
                      "COQFLAGS", "COQEXTRAFLAGS", "OTHERFLAGS", "COQ_SRC_SUBDIRS",
                      "COQCHKEXTRAFLAGS")


# A full make check of a fresh copy took 4,477 s on 15 October 2026, and the
# VM is shared: the limit leaves room for a slower machine.
STEP_TIMEOUT = 14400


def run(cmd, cwd, env=None):
    clean = {name: value for name, value in os.environ.items()
             if name not in UNSAFE_ENVIRONMENT}
    clean.update(env or {})
    # A session of its own: killing the process group also kills the
    # compilers that make started, not only make (P2). The group is killed
    # however run() ends: on the time limit, on an interrupt (P3), and after
    # a normal return, so that no process of the step outlives it.
    process = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, env=clean,
                               start_new_session=True)
    try:
        out, err = process.communicate(timeout=STEP_TIMEOUT)
    except subprocess.TimeoutExpired:
        raise StepTimeout(f"{' '.join(cmd)} exceeded {STEP_TIMEOUT} seconds; "
                          "its process group was killed") from None
    finally:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        if process.returncode is None:
            # Reap the command without reading its pipes: a partial output
            # is neither decoded nor needed.
            process.wait()
            process.stdout.close()
            process.stderr.close()
    # Output cut inside a UTF-8 sequence, or not UTF-8, is decoded with
    # replacement characters rather than refused.
    return process.returncode, (out + err).decode("utf-8", errors="replace")


def case_sensitive(directory):
    """Probe the target filesystem without changing tracked files."""
    directory.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="case-probe-", dir=directory) as tmp:
        path = Path(tmp)
        (path / "CaseProbe").write_text("probe")
        return not (path / "caseprobe").exists()


def report_paths(copy):
    """The report arguments of the checker before the repair: REPORTS of
    the copy's Makefile."""
    text = (copy / "Makefile").read_text()
    block = re.search(r"^REPORTS = (.*?)\n\n", text, re.S | re.M).group(1)
    return block.replace("\\\n", " ").split()


def step(copy, tree, test):
    kind = test["step"]
    env = test.get("environment", {})
    if kind == "make" or (kind == "environment" and tree == "baseline"):
        make = ["make", "check"] if tree == "baseline" else ["make", "-f", "Makefile", "check"]
        return run(make + ["ROCQ_SWITCH=", "JOBS=3", "CHECK_JOBS=3"], copy, env)
    if kind in ("checker", "environment"):
        if tree == "baseline":
            return run(["python3", "scripts/check_sources.py"] + report_paths(copy), copy, env)
        manifest = json.loads((copy / "build" / "checks" / "manifest.json").read_text())
        args = ["--reuse", manifest["run_id"]] if kind == "checker" else ["--jobs", "1"]
        return run(["python3", "-I", "-B", "scripts/check_sources.py"] + args, copy, env)
    raise ValueError(kind)


class FixtureError(RuntimeError):
    """A fixture could not be prepared or run."""


class CleanupError(FixtureError):
    """The scratch copy may still be modified; stop the campaign."""


class StepTimeout(FixtureError):
    """A command reached STEP_TIMEOUT; stop the campaign."""


def run_fixture(copy, tree, test, patch):
    """Prepare, run and restore one fixture, including failed preparation.

    Cleanup attempts every restoration even if one fails. A cleanup failure
    aborts the campaign: an expected checker refusal cannot make it a pass.
    """
    want = test[tree]
    step_used = want.get("step", test["step"])
    compiles = step_used == "make" or (step_used == "environment" and tree == "baseline")
    saved, times, tracked, trees = {}, {}, [], []
    patch_applied = False
    cache_dir = copy / "scripts/__pycache__"
    if cache_dir.is_symlink():
        raise FixtureError("the pre-existing scripts cache must not be a symlink")
    cache_existed = cache_dir.exists()
    marker = copy / "build" / test["marker"] if "marker" in test else None

    def save(path):
        if path not in saved:
            saved[path] = path.read_bytes() if path.exists() else None

    with tempfile.TemporaryDirectory(prefix="regression-cache-") as temp:
        cache_backup = Path(temp) / "cache"
        if cache_existed:
            shutil.copytree(cache_dir, cache_backup, symlinks=True)
        try:
            # Compilers create several artifacts beside a fixture source.
            # Only use fresh fixture subtrees, so removing them loses no input.
            for path in sorted({copy / "build" / rel.split("/")[0]
                                for rel in test.get("files", {}) if "/" in rel}):
                if path.exists() or path.is_symlink():
                    raise FixtureError(f"fixture directory already exists: {path}")
                trees.append(path)
            if patch.exists():
                for name in re.findall(r"^diff --git a/(\S+) b/", patch.read_text(), re.M):
                    path = copy / name
                    if path.exists():
                        st = path.stat()
                        times[path] = (st.st_atime_ns, st.st_mtime_ns)
                status, out = run(["git", "apply", str(patch)], copy)
                if status:
                    raise FixtureError(f"the patch does not apply: {out.strip()[:200]}")
                patch_applied = True
            for rel, text in test.get("files", {}).items():
                path = copy / "build" / rel
                save(path)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            for directory, root, rel in test.get("compile", []):
                status, out = run(["rocq", "compile", "-q", "-noglob", "-Q",
                                   f"build/{directory}", root, f"build/{rel}"], copy)
                if status:
                    raise FixtureError(f"build/{rel} does not compile: {out.strip()[:200]}")
            need = [src for src, _ in test.get("copy", {}).get(tree, [])]
            absent = [r for r in need if not (copy / "build" / r).exists()]
            if absent:
                raise FixtureError(f"required build/{absent[0]} does not exist")
            for rel, text in test.get("write", {}).get(tree, {}).items():
                path = copy / "build" / rel
                save(path)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            for rel in test.get("delete", {}).get(tree, []):
                path = copy / "build" / rel
                save(path)
                path.unlink(missing_ok=True)
            for src, dst in test.get("copy", {}).get(tree, []):
                path = copy / "build" / dst
                save(path)
                path.write_bytes((copy / "build" / src).read_bytes())
            # Parser tests deliberately update the recorded digest after editing
            # an output, so they reach the parser rather than stopping at SHA-256.
            # This is a test-only operation; the authoritative runner never does it.
            for transform in test.get("transform", {}).get(tree, []):
                rel = transform["output"]
                if Path(rel).is_absolute() or ".." in Path(rel).parts:
                    raise ValueError("a report transformation must stay under build/")
                path = copy / "build" / rel
                save(path)
                text = path.read_text()
                operation = transform["operation"]
                if operation == "duplicate":
                    text += text
                elif operation == "cut-inside-final-report-line":
                    text = text.removesuffix("=== ROCQ CHECK OUTPUT COMPLETE ===\n").rstrip("\n")
                    line = text.rsplit("\n", 1)[-1]
                    text = text[:-len(line)] + line[:max(1, len(line) // 2)]
                elif operation == "append-elision":
                    text += "...\n"
                else:
                    raise ValueError(f"unknown report transformation {operation!r}")
                path.write_text(text)
                if transform.get("refresh_manifest"):
                    manifest_path = copy / "build/checks/manifest.json"
                    save(manifest_path)
                    manifest = json.loads(manifest_path.read_text())
                    matches = [entry for entry in manifest["checks"]
                               if entry["output"] == "build/" + rel]
                    if len(matches) != 1:
                        raise ValueError("a parser test must identify exactly one output")
                    matches[0]["output_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
                    manifest_path.write_text(json.dumps(manifest, indent=1) + "\n")
            for rel, text in test.get("pyc", {}).get(tree, {}).items():
                source = copy / rel
                cached = Path(importlib.util.cache_from_source(str(source)))
                fake = copy / "build" / "regression-pyc-source.py"
                save(fake)
                fake.parent.mkdir(parents=True, exist_ok=True)
                fake.write_text(text)
                py_compile.compile(str(fake), cfile=str(cached), dfile=str(source), doraise=True,
                                   invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
                fake.unlink()
            for rel in test.get("track", []):
                # Register first: a failed git add may have changed the index.
                tracked.append(rel)
                status, out = run(["git", "add", "-f", rel], copy)
                if status:
                    raise FixtureError(f"git add failed for {rel}: {out.strip()[:200]}")
            if marker is not None:
                save(marker)
                marker.unlink(missing_ok=True)
            env = {k: v.replace("@BUILD@", str(copy / "build"))
                   for k, v in test.get("environment", {}).items()}
            status, out = step(copy, tree, dict(test, environment=env, step=step_used))
            ran = marker.exists() if marker is not None else None
            return status, out, ran
        finally:
            errors = []

            def restore(label, action):
                try:
                    action()
                except Exception as error:
                    errors.append(f"{label}: {error}")

            def checked_command(cmd):
                status, out = run(cmd, copy)
                if status:
                    raise CleanupError(f"{' '.join(cmd)} failed ({status}): {out.strip()[:200]}")

            def restore_time(path, ns):
                if path.exists():
                    os.utime(path, ns=ns)

            def remove_tree(path):
                if path.exists():
                    shutil.rmtree(path)

            def restore_cache():
                # Restore from the snapshot, not the surviving current entries:
                # the fixture or checker may have removed an original .pyc.
                if cache_dir.is_symlink() or cache_dir.is_file():
                    cache_dir.unlink()
                elif cache_dir.exists():
                    shutil.rmtree(cache_dir)
                if cache_existed:
                    shutil.copytree(cache_backup, cache_dir, symlinks=True)

            # Every file operation of the cleanup runs inside restore(), and
            # anything that still escapes is a cleanup failure (P1).
            try:
                if patch_applied:
                    restore("reverse patch", lambda: checked_command(
                        ["git", "apply", "-R", str(patch)]))
                    if not compiles:
                        for path, ns in times.items():
                            restore(f"mtime {path}", lambda p=path, t=ns: restore_time(p, t))
                for path in trees:
                    restore(f"fixture directory {path}", lambda p=path: remove_tree(p))
                for path, data in saved.items():
                    def restore_file(path=path, data=data):
                        if data is None:
                            path.unlink(missing_ok=True)
                        else:
                            path.parent.mkdir(parents=True, exist_ok=True)
                            path.write_bytes(data)
                    restore(f"file {path}", restore_file)
                for rel in tracked:
                    restore(f"index {rel}", lambda r=rel: checked_command(
                        ["git", "rm", "-q", "--cached", r]))
                restore("scripts cache", restore_cache)
            except Exception as error:
                errors.append(f"cleanup: {error}")
            if errors:
                raise CleanupError("; ".join(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--copy", type=Path, required=True)
    parser.add_argument("--tree", choices=["baseline", "repaired"], required=True)
    parser.add_argument("ids", nargs="*")
    args = parser.parse_args()
    copy = args.copy.resolve()
    ids = args.ids or sorted(p.name for p in TESTS.iterdir() if (p / "test.json").exists())

    def effective_step(test_id):
        test = json.loads((TESTS / test_id / "test.json").read_text())
        kind = test[args.tree].get("step", test["step"])
        return "make" if kind == "environment" and args.tree == "baseline" else kind
    # The tests that read the outputs of the last make check of the copy run
    # first, while those outputs are the ones of the unchanged tree; the
    # tests that run make check themselves, and so leave the outputs of a
    # changed tree, run last.
    ids = sorted(ids, key=lambda t: (effective_step(t) == "make", t))
    # A checker-step test reads the outputs of the copy's last make check; a
    # make-step test rebuilds them. Make sure they exist before the suite, in
    # case a failed test of an earlier run left them deleted.
    if args.tree == "baseline":
        clean = all((copy / "build" / Path(r).name).exists() for r in report_paths(copy))
        cmd = ["make", "check", "ROCQ_SWITCH=", "JOBS=3", "CHECK_JOBS=3"]
    else:
        clean = (copy / "build" / "checks" / "manifest.json").exists()
        cmd = ["make", "-f", "Makefile", "check", "ROCQ_SWITCH=", "JOBS=3", "CHECK_JOBS=3"]
    if not clean:
        print(f"the copy has no clean outputs; running {' '.join(cmd)} once", flush=True)
        try:
            status, out = run(cmd, copy)
        except StepTimeout as error:
            sys.exit(f"STOP: {error}; inspect the scratch copy")
        if status:
            sys.exit(f"the unchanged copy does not pass: {out.strip().splitlines()[-1][:200]}")
    disagreements = 0
    for test_id in ids:
        test = json.loads((TESTS / test_id / "test.json").read_text())
        want = test[args.tree]
        if test.get("requires_case_sensitive") and not case_sensitive(copy / "build"):
            print(f"skipped {test_id}: requires a case-sensitive filesystem "
                  "(Makefile and makefile must coexist)")
            continue
        if want.get("expect") == "skip":
            print(f"skipped {test_id}: {want.get('reason', '')}")
            continue
        patch = TESTS / test_id / f"{args.tree}.diff"
        try:
            status, out, ran = run_fixture(copy, args.tree, test, patch)
        except CleanupError as error:
            sys.exit(f"STOP {test_id}: cleanup failed; inspect the scratch copy: {error}")
        except StepTimeout as error:
            sys.exit(f"STOP {test_id}: {error}; inspect the scratch copy")
        except (FixtureError, OSError, ValueError, subprocess.SubprocessError,
                py_compile.PyCompileError) as error:
            print(f"DIFFER {test_id}: fixture failed: {error}", flush=True)
            disagreements += 1
            continue
        expect_marker = want.get("marker", want["expect"] == "pass")
        if want["expect"] == "pass":
            ok = status == 0 and (ran is None or ran == expect_marker)
            what = ("passes" if status == 0 else
                    f"fails ({out.strip().splitlines()[-1][:160] if out.strip() else ''})")
            if ran is not None:
                what += f"; {test['marker']} {'created' if ran else 'not created'}"
        else:
            found = re.search(want["message"], out, re.M)
            ok = status != 0 and found is not None and (ran is None or ran == expect_marker)
            what = (f"fails: {found.group(0)[:160]}" if status != 0 and found is not None else
                    "passes" if status == 0 else
                    f"fails without the message: {out.strip().splitlines()[-1][:160]}")
            if ran is not None:
                what += f"; {test['marker']} {'created' if ran else 'not created'}"
        disagreements += not ok
        print(f"{'agree' if ok else 'DIFFER'} {test_id} ({want.get('step', test['step'])}, "
              f"{args.tree}): {what}", flush=True)
    print(f"{len(ids)} tests on the {args.tree} tree, {disagreements} disagreements")
    sys.exit(1 if disagreements else 0)


if __name__ == "__main__":
    main()
