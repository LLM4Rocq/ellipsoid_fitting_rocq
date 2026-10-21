#!/usr/bin/env python3
"""Validate the source inventory before any Rocq compilation (repair E41).

inspect_sources(root, allowed_options) returns a dictionary with failures,
sources (in _CoqProject order), discovered .v files, and all regular files
under the six protected roots. On failure, sources is empty: callers must
stop, not scan a partial inventory. The checker and runner should share this
inventory, including theories/; check modules retain their separate registry.

No protected symlink is followed, including broken links and links whose
target is inside the checkout. The root CLAUDE.md link is outside these trees
and remains permitted. This check assumes a controlled checkout; it does not
protect against concurrent filesystem replacement between checking and use.
"""

import os
from pathlib import Path
import re
import stat
import subprocess


SOURCE_ROOTS = ("theories", "library", "extension", "applications")
PROTECTED_ROOTS = SOURCE_ROOTS + ("check", "scripts")
SOURCE_PATH = re.compile(
    r"(?:theories|library|extension|applications)/"
    r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*\.v"
)


def _mode(path, label, failures):
    try:
        return path.lstat().st_mode
    except OSError as error:
        failures.append(f"{label}: cannot inspect input: {error.strerror}")
        return None


def _ordinary_file(root, name, failures):
    mode = _mode(root / name, name, failures)
    if mode is None:
        return False
    if stat.S_ISLNK(mode):
        failures.append(f"{name}: protected input is a symlink")
    elif not stat.S_ISREG(mode):
        failures.append(f"{name}: protected input must be an ordinary file")
    else:
        return True
    return False


def _walk_protected(root, failures):
    files = []
    for top in PROTECTED_ROOTS:
        mode = _mode(root / top, top, failures)
        if mode is None:
            continue
        if stat.S_ISLNK(mode):
            failures.append(f"{top}: protected directory is a symlink")
            continue
        if not stat.S_ISDIR(mode):
            failures.append(f"{top}: protected input must be an ordinary directory")
            continue
        stack = [root / top]
        while stack:
            directory = stack.pop()
            try:
                with os.scandir(directory) as scan:
                    entries = sorted(scan, key=lambda entry: entry.name)
            except OSError as error:
                failures.append(
                    f"{directory.relative_to(root).as_posix()}: "
                    f"cannot enumerate input directory: {error.strerror}")
                continue
            for entry in entries:
                path = Path(entry.path)
                name = path.relative_to(root).as_posix()
                mode = _mode(path, name, failures)
                if mode is None:
                    continue
                if stat.S_ISLNK(mode):
                    failures.append(f"{name}: protected input is a symlink")
                elif stat.S_ISDIR(mode):
                    stack.append(path)
                elif stat.S_ISREG(mode):
                    files.append(name)
                else:
                    failures.append(f"{name}: protected input is not an ordinary file or directory")
    return sorted(files)


def _registered(text, allowed_options, failures):
    sources, options, seen = [], [], set()
    for number, line in enumerate(text.split("\n"), 1):
        if not line.strip(" \t"):
            continue
        if SOURCE_PATH.fullmatch(line):
            if line in seen:
                failures.append(f"_CoqProject:{number}: duplicate source {line}")
            seen.add(line)
            sources.append(line)
        elif line in allowed_options:
            options.append(line)
        else:
            failures.append(
                f"_CoqProject:{number}: invalid source path or option: {line!r}")
    if options != list(allowed_options):
        failures.append("_CoqProject: option lines differ from the allowed ordered list")
    return sources


def _tracked_symlinks(root, tracked_entries, failures):
    """Read git's NUL-delimited stage records; never split pathnames on spaces."""
    if tracked_entries is None:
        try:
            result = subprocess.run(
                ["git", "-C", str(root), "ls-files", "--stage", "-z"],
                capture_output=True, check=False, timeout=30)
        except (OSError, subprocess.TimeoutExpired) as error:
            failures.append(f"git ls-files --stage: cannot inspect tracked inputs: {error}")
            return
        if result.returncode:
            failures.append("git ls-files --stage: failed to inspect tracked inputs")
            return
        tracked_entries = result.stdout
    if not isinstance(tracked_entries, bytes):
        failures.append("git ls-files --stage: expected byte records")
        return
    if tracked_entries and not tracked_entries.endswith(b"\0"):
        failures.append("git ls-files --stage: unterminated stage record")
        return
    seen = set()
    for record in tracked_entries.split(b"\0")[:-1]:
        header, sep, raw_path = record.partition(b"\t")
        match = re.fullmatch(rb"([0-7]{6}) ([0-9a-f]{40}|[0-9a-f]{64}) ([0-3])", header)
        if not sep or not raw_path or match is None:
            failures.append("git ls-files --stage: malformed stage record")
            continue
        path = os.fsdecode(raw_path)
        if path in seen:
            failures.append(f"{path!r}: duplicate tracked path or unresolved git stages")
        seen.add(path)
        if match[3] != b"0":
            failures.append(f"{path!r}: unresolved git stage {os.fsdecode(match[3])}")
        if path.split("/", 1)[0] in PROTECTED_ROOTS and match[1] == b"120000":
            failures.append(f"{path!r}: tracked protected input has symlink mode 120000")


def inspect_sources(root, allowed_options, *, tracked_entries=None):
    """Return a validated source inventory, or diagnostics and no usable sources.

    allowed_options is the checker's exact ordered _CoqProject option list.
    tracked_entries is optional git ls-files --stage -z output, for harmless
    fixture tests; production callers omit it so the current index is checked.
    No source file is opened. Only a regular _CoqProject is read, after walking
    the protected trees. Ordinary-file checks also cover the root Makefile.
    """
    root = Path(root).absolute()
    failures = []
    files = _walk_protected(root, failures)
    project_ok = _ordinary_file(root, "_CoqProject", failures)
    _ordinary_file(root, "Makefile", failures)
    sources = []
    if project_ok:
        try:
            text = (root / "_CoqProject").read_bytes().decode("utf-8")
        except (OSError, UnicodeError) as error:
            failures.append(f"_CoqProject: cannot read UTF-8 input: {error}")
        else:
            sources = _registered(text, tuple(allowed_options), failures)
    discovered = [name for name in files
                  if name.split("/", 1)[0] in SOURCE_ROOTS and name.endswith(".v")]
    for name in sorted(set(sources) - set(discovered)):
        failures.append(f"{name}: registered source is not a discovered ordinary file")
    for name in sorted(set(discovered) - set(sources)):
        failures.append(f"{name}: unregistered source under a source root")
    _tracked_symlinks(root, tracked_entries, failures)
    return {"sources": sources if not failures else [],
            "discovered": discovered, "files": files, "failures": failures}
