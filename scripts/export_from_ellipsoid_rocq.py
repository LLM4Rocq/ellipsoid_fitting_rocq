#!/usr/bin/env python3
"""Copy the proof of the main theorems out of LLM4Rocq/ellipsoid_rocq.

The sources are read from a commit of that repository, not from its working
tree. The script computes the dependency closure of PaperMainResults (the
proof of the three main theorems) and PaperMainDefinitions (the definitions
of the statement) from the `From Tablet Require` lines, writes every module
of the closure to theories/, and replaces the logical root Tablet by
EllipsoidFitting. Nothing else in the files changes.

    python3 scripts/export_from_ellipsoid_rocq.py ../ellipsoid_rocq 9556cdd

With --check, the script writes nothing and compares theories/ with what it
would write; it lists the differences and exits 1 when there are any.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

OLD_ROOT = "Tablet"
NEW_ROOT = "EllipsoidFitting"
ROOTS = ["PaperMainResults", "PaperMainDefinitions"]
REQUIRE = re.compile(r"From\s+" + OLD_ROOT + r"\s+Require(?:\s+(?:Import|Export))?\s+([^.]+?)\s*\.", re.S)


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def show(repo, commit, path):
    return subprocess.run(["git", "-C", str(repo), "show", f"{commit}:{path}"],
                          check=True, capture_output=True, text=True).stdout


def closure(repo, commit):
    sources, todo = {}, list(ROOTS)
    while todo:
        name = todo.pop()
        if name in sources:
            continue
        text = show(repo, commit, f"analysis/{name}.v")
        sources[name] = text
        for match in REQUIRE.finditer(strip_comments(text)):
            todo.extend(match.group(1).split())
    return sources


def rename(text):
    return re.sub(r"\b" + OLD_ROOT + r"\b", NEW_ROOT, text)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("repo", type=Path, help="checkout of LLM4Rocq/ellipsoid_rocq")
    parser.add_argument("commit", help="commit to copy from")
    parser.add_argument("--check", action="store_true", help="compare instead of writing")
    args = parser.parse_args()

    commit = subprocess.run(["git", "-C", str(args.repo), "rev-parse", args.commit],
                            check=True, capture_output=True, text=True).stdout.strip()
    sources = closure(args.repo, commit)
    out = Path(__file__).resolve().parent.parent / "theories"

    if args.check:
        bad = [n for n, t in sorted(sources.items())
               if not (out / f"{n}.v").exists() or (out / f"{n}.v").read_text() != rename(t)]
        print(f"{len(sources)} modules from {commit}; {len(bad)} differ")
        for name in bad:
            print("  differs:", name)
        sys.exit(1 if bad else 0)

    out.mkdir(exist_ok=True)
    for name, text in sources.items():
        (out / f"{name}.v").write_text(rename(text))
    print(f"wrote {len(sources)} modules from {commit} to {out}")


if __name__ == "__main__":
    main()
