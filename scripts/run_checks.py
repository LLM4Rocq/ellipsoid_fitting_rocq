#!/usr/bin/env python3
"""Compile the check files of make check and publish their outputs only
after a successful compilation.

    python3 -I -B scripts/run_checks.py --run-id ID [--jobs N]

scripts/check_sources.py starts this runner with a run identifier that it
has just created, once the rules on the sources hold, then verifies what the
runner wrote. The check files, their flags and their outputs are CHECK_FILES
of scripts/check_sources.py, which the runner compiles from its source (never
from the bytecode cached in scripts/__pycache__/). The runner

1. fails if any variable of BANNED_ENVIRONMENT is set, or any variable whose
   name starts with OCAML or CAML, since each can change what Rocq loads (an
   rc file, a load path, a plugin path, the configuration of findlib) or
   how the OCaml compiler builds the exporter;
2. removes and recreates the directory build/checks/, which it owns;
3. compiles each check file with rocq compile, -q (no rc file), -noglob, the
   warning comment-terminator-in-string as an error, -Q build/checks Checks
   (so that a check file can Require another as Checks.<Name>) and its flags,
   first the files of stage 1, then those of stage 2, which Require files of
   stage 1; a command line with -vos, -vok, -type-in-type or
   -impredicative-set is refused;
4. captures the standard output and the standard error of each compilation
   itself, and renames the output from its temporary name to
   build/checks/<Name>.out only if rocq exits with status 0; non-snapshot
   outputs receive a completion trailer so truncation is independently
   detected by the report parser;
5. runs rocqchk -silent -o on every module of library/, theories/,
   extension/ and applications/ (the .v lines of _CoqProject) and every compiled check file,
   each named with -norec, so that the kernel checks each again and lists
   every assumption, typing flag and theory; its output (standard output
   and standard error, where it prints the summary) is kept as
   build/checks/rocqchk.out only if it exits with status 0;
6. if every step succeeded, writes build/checks/manifest.json: the
   run identifier, the version line of rocq, the versions of the installed
   rocq-core, rocq-mathcomp-ssreflect and rocq-mathcomp-analysis, and for
   each check file of CHECK_FILES, in order, its source, the SHA-256 of the
   source, its flags, its output, the SHA-256 of the output, its standard
   error and the SHA-256 of that; and the SHA-256 of every other file of
   build/checks/ (the compiled .vo files); and the modules given to rocqchk
   with the SHA-256 of its output.

The identity drivers of rule 30 (e) (check/identity/Identity<Name>.v, E42)
load the exporter of check/identity/. Before the check files compile, the
runner builds it from its pinned sources (kernel_universe.ml,
kernel_identity.ml and META, copied into build/checks/plugin/) with fixed
ocamlfind ocamlopt commands, in an environment without any variable whose
name starts with OCAML or CAML. It compiles the drivers, and only them, with
OCAMLPATH set to build/checks/plugin/findlib, which they need for Declare ML
Module "kernel_identity". Their outputs, like the snapshots', get no
trailer: their framing is checked record by record. The manifest records,
under "identity", the version of ocamlopt and of findlib, the directory of
rocq-runtime (which must lie in the switch of rocq), the SHA-256 of the
build recipe and that of the plugin built.

A failed compilation fails the run, and no manifest is written."""

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import types
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECKS = ROOT / "build" / "checks"
BANNED_ENVIRONMENT = ["ROCQPATH", "COQPATH", "ROCQLIB", "COQLIB", "OCAMLPATH",
                      "CAML_LD_LIBRARY_PATH", "ROCQRC", "COQRC", "XDG_CONFIG_HOME",
                      "COQFLAGS", "COQEXTRAFLAGS", "OTHERFLAGS", "COQ_SRC_SUBDIRS",
                      "COQCHKEXTRAFLAGS"]
BANNED_FLAGS = {"-vos", "-vok", "-type-in-type", "-impredicative-set"}
COMMON = ["-q", "-noglob", "-w", "+comment-terminator-in-string",
          "-Q", "build/checks", "Checks"]
PACKAGES = ["rocq-core", "rocq-mathcomp-ssreflect", "rocq-mathcomp-analysis"]
PROCESS_TIMEOUT = 1800
KERNEL_TIMEOUT = 3600
IDENTITY = ROOT / "check" / "identity"
PLUGIN = CHECKS / "plugin"
# The environment of the identity drivers, set once the exporter is built.
IDENTITY_ENVIRONMENT = None


def build_identity_plugin(checker):
    """The exporter of check/identity/, built from its sources into
    build/checks/plugin/ (scripts/identity_sidecars.py): [] or the lines of a
    failure."""
    try:
        checker.identity_sidecars.build_plugin(IDENTITY, PLUGIN, PROCESS_TIMEOUT)
    except ValueError as error:
        return str(error).splitlines()
    return []


def prepare_checks_directory():
    """Refuse redirected output paths before removing an earlier run."""
    for path in (ROOT / "build", CHECKS):
        if path.is_symlink():
            raise ValueError(f"{path.relative_to(ROOT)}: a symlink is not an output directory")
        if path.exists() and not path.is_dir():
            raise ValueError(f"{path.relative_to(ROOT)}: not a directory")
    if CHECKS.exists():
        shutil.rmtree(CHECKS)
    CHECKS.mkdir(parents=True)


def load_checker():
    """scripts/check_sources.py, compiled from its source: never from the
    bytecode cached in scripts/__pycache__/, which python3 -B does not
    prevent and which can stand for another source (E36)."""
    path = ROOT / "scripts" / "check_sources.py"
    module = types.ModuleType("check_sources")
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    return module


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def package_versions():
    """The installed versions of PACKAGES, read from the opam switch that
    holds rocq: {package: version or None}."""
    where = subprocess.run(["rocq", "-where"], capture_output=True, text=True,
                           check=True, timeout=PROCESS_TIMEOUT).stdout.strip()
    packages = Path(where).resolve().parent.parent / ".opam-switch" / "packages"
    found = {}
    for package in PACKAGES:
        names = sorted(p.name for p in packages.glob(package + ".*")) \
            if packages.is_dir() else []
        found[package] = names[0][len(package) + 1:] if len(names) == 1 else None
    return found


def compile_check(check):
    name = Path(check.source).stem
    command = (["rocq", "compile"] + COMMON + list(check.flags)
               + ["-o", f"build/checks/{name}.vo", check.source])
    if BANNED_FLAGS & set(command):
        return check, -1, ["refused flags: " + " ".join(sorted(BANNED_FLAGS & set(command)))]
    tmp = CHECKS / f"{name}.tmp"
    err = CHECKS / f"{name}.err"
    env = None
    if check.expect[0] == "identity":
        # Only the identity drivers load the exporter (rule 30 (e)).
        env = IDENTITY_ENVIRONMENT
    with open(tmp, "wb") as stdout, open(err, "wb") as stderr:
        try:
            status = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr,
                                    env=env, timeout=PROCESS_TIMEOUT).returncode
        except subprocess.TimeoutExpired:
            tmp.unlink(missing_ok=True)
            return check, -1, [f"compilation exceeded {PROCESS_TIMEOUT} seconds"]
        except OSError as error:
            tmp.unlink(missing_ok=True)
            return check, -1, [f"could not start compilation: {error}"]
    if status != 0:
        tail = err.read_text(errors="replace").splitlines()[-12:]
        tmp.unlink()
        return check, status, [" ".join(command)] + tail
    if check.expect[0] not in ("snapshot", "identity"):
        data = tmp.read_bytes()
        if data and not data.endswith(b"\n"):
            tmp.unlink()
            return check, -1, ["Rocq output ends inside a line"]
        with tmp.open("ab") as out:
            out.write(b"=== ROCQ CHECK OUTPUT COMPLETE ===\n")
    os.replace(tmp, CHECKS / f"{name}.out")
    return check, 0, []


def kernel_modules(checker):
    """Every registered project module, including theories/, and every check."""
    modules = checker.kernel_source_modules(checker.validated_sources())
    modules += [f"Checks.{Path(c.source).stem}" for c in checker.CHECK_FILES]
    return modules


def run_rocqchk(modules):
    command = ["rocqchk", "-silent", "-o", "-Q", "library", "GaussianAnalysis",
               "-Q", "theories", "EllipsoidFitting", "-Q", "extension", "EllipsoidUniversality",
               "-Q", "applications", "GaussianApplications", "-Q", "build/checks", "Checks"]
    for module in modules:
        command += ["-norec", module]
    # rocqchk prints its context summary on the standard error: both streams
    # are kept, together, as its output.
    tmp = CHECKS / "rocqchk.tmp"
    with open(tmp, "wb") as out:
        try:
            status = subprocess.run(command, cwd=ROOT, stdout=out,
                                    stderr=subprocess.STDOUT,
                                    timeout=KERNEL_TIMEOUT).returncode
        except subprocess.TimeoutExpired:
            out.write(f"\nrocqchk exceeded {KERNEL_TIMEOUT} seconds\n".encode())
            out.flush()
            os.replace(tmp, CHECKS / "rocqchk.failed")
            return -1
        except OSError as error:
            out.write(f"\ncould not start rocqchk: {error}\n".encode())
            out.flush()
            os.replace(tmp, CHECKS / "rocqchk.failed")
            return -1
    if status != 0:
        os.replace(tmp, CHECKS / "rocqchk.failed")
        return status
    os.replace(tmp, CHECKS / "rocqchk.out")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if not args.run_id.isalnum():
        sys.exit("run_checks.py: the run identifier must be alphanumeric")
    banned = [v for v in BANNED_ENVIRONMENT if v in os.environ]
    banned += sorted(v for v in os.environ
                     if v.startswith(("OCAML", "CAML")) and v not in banned)
    if banned:
        sys.exit("run_checks.py: unset " + ", ".join(banned) + " (each can change what "
                 "Rocq loads); the Makefile runs make check without them")
    checker = load_checker()
    try:
        modules = kernel_modules(checker)
        prepare_checks_directory()
        version = subprocess.run(["rocq", "--version"], capture_output=True, text=True,
                                 check=True, timeout=PROCESS_TIMEOUT).stdout.splitlines()[0]
        packages = package_versions()
        if version != checker.ROCQ_VERSION or packages != checker.PACKAGES:
            sys.exit("run_checks.py: the installed toolchain is not the pinned one")
    except (OSError, ValueError, subprocess.SubprocessError) as err:
        sys.exit(f"run_checks.py: {err}")
    global IDENTITY_ENVIRONMENT
    failure = build_identity_plugin(checker)
    if failure:
        print("run_checks.py: the exporter of check/identity/ does not build")
        for line in failure:
            print("    " + line)
        sys.exit("run_checks.py: no check file is compiled and no manifest is written")
    IDENTITY_ENVIRONMENT = checker.identity_sidecars.driver_environment(PLUGIN / "findlib")
    try:
        identity = checker.identity_sidecars.ocaml_toolchain(PROCESS_TIMEOUT)
    except ValueError as error:
        sys.exit(f"run_checks.py: the OCaml toolchain of the exporter: {error}")
    identity["recipe_sha256"] = checker.identity_sidecars.recipe_sha256()
    identity["plugin"] = "build/checks/plugin/findlib/kernel_identity/kernel_identity.cmxs"
    identity["plugin_sha256"] = sha256(ROOT / identity["plugin"])
    print("run_checks.py: the exporter of check/identity/ built", flush=True)
    failed = []
    for stage in (1, 2):
        batch = [c for c in checker.CHECK_FILES if c.stage == stage]
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            for check, status, lines in pool.map(compile_check, batch):
                if status == 0:
                    print(f"run_checks.py: {check.source}: compiled", flush=True)
                else:
                    failed.append(check.source)
                    print(f"run_checks.py: {check.source}: rocq exited with status {status}")
                    for line in lines:
                        print("    " + line)
        if failed:
            break
    if failed:
        sys.exit(f"run_checks.py: {len(failed)} check file(s) failed; no output of a failed "
                 "compilation is published and no manifest is written")
    status = run_rocqchk(modules)
    if status != 0:
        sys.exit(f"run_checks.py: rocqchk exited with status {status} (see "
                 "build/checks/rocqchk.failed); no manifest is written")
    print(f"run_checks.py: rocqchk checked {len(modules)} modules", flush=True)
    entries, listed = [], set()
    for c in checker.CHECK_FILES:
        name = Path(c.source).stem
        out, err = f"build/checks/{name}.out", f"build/checks/{name}.err"
        listed |= {out, err}
        entries.append({"source": c.source, "source_sha256": sha256(ROOT / c.source),
                        "flags": list(c.flags), "output": out,
                        "output_sha256": sha256(ROOT / out), "stderr": err,
                        "stderr_sha256": sha256(ROOT / err)})
    kernel = {"modules": modules, "output": "build/checks/rocqchk.out",
              "output_sha256": sha256(CHECKS / "rocqchk.out")}
    listed |= {kernel["output"]}
    others = {str(p.relative_to(ROOT)): sha256(p) for p in sorted(CHECKS.rglob("*"))
              if p.is_file() and str(p.relative_to(ROOT)) not in listed}
    manifest = {"run_id": args.run_id, "rocq": version, "packages": packages,
                "identity": identity, "checks": entries, "kernel": kernel,
                "other_files": others}
    tmp = CHECKS / "manifest.tmp"
    tmp.write_text(json.dumps(manifest, indent=1) + "\n")
    os.replace(tmp, CHECKS / "manifest.json")
    print(f"run_checks.py: {len(entries)} check files compiled; manifest written")


if __name__ == "__main__":
    main()
