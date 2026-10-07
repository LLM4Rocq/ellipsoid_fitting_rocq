#!/usr/bin/env python3
"""List the names that comments of theories/, library/ and extension/ cite
but that nothing defines.

A comment that names a lemma, a definition or a module goes stale when the
name is deleted or renamed. This script compares the identifiers that occur
in the comments with the names that exist: the declarations and references
recorded in the .glob files of a build of theories/, library/ and
extension/, the declarations recorded in the .glob files of the installed
libraries (found through `rocq -where` or `coqc -where`; the check is
weaker without them), and the module names of theories/, library/ and
extension/.

An identifier counts as a citation when it looks like a Rocq name rather
than a word of the prose: it contains two underscores or more, or it
contains one underscore and three or more known declarations share the
part before it (such as gpb_ or gaussian_), or it is a CamelCase word of at
least two capitals that is not a current module name. Words of the prose
with an underscore (x_i, sum_i) are ignored, and a short list of accepted
tokens below silences the others.

    python3 scripts/stale_citations.py            report, exit 1 if any
    python3 scripts/stale_citations.py --quiet    exit code only

Run it after a build: it reads the .glob files next to the modules."""

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Words that the heuristic takes for citations but that are prose.
ACCEPTED = {
    "MathComp", "MathComp-Analysis", "Stdlib", "HB", "Rocq", "Coq",
    "Coquelicot", "SsrReflect", "CamelCase", "ListNotations",
    "coq_nat", "ring_scope", "R_scope", "classical_set_scope",
    "ereal_scope", "fun_scope", "nat_scope", "is_left", "ln_exists",
    "auto_derive",
    # names of the prose of some comments, written like identifiers
    "radius_bound", "gordon_width", "goe_loading", "distance_lt",
    "distance_le", "sup_out", "lambda_max", "lambda_min",
}

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
CAMEL = re.compile(r"^[A-Z][a-z0-9]+(?:[A-Z][a-z0-9]*)+$")


def installed_glob_dirs():
    """The directories of the installed libraries, if a Rocq is on PATH."""
    for cmd in (["rocq", "-where"], ["coqc", "-where"]):
        try:
            out = subprocess.run(cmd, capture_output=True, text=True,
                                 check=True).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            continue
        if out:
            return [Path(out) / "user-contrib", Path(out) / "theories"]
    return []


def glob_names(path, defs_only=False):
    """The names declared (and, unless defs_only, referenced) in a .glob."""
    names = set()
    with open(path, errors="replace") as fh:
        for line in fh:
            if line.startswith(("DIGEST", "F")):
                continue
            parts = line.split()
            if line.startswith("R"):
                if not defs_only and len(parts) >= 5:
                    names.add(parts[3])
                    names.update(parts[1].split("."))
                continue
            if len(parts) >= 4 and parts[0] != "binder":
                names.add(parts[3])
    return names


def comments(text):
    """The comments of a .v file, with the line of their first character."""
    i, n, depth, start = 0, len(text), 0, 0
    while i < n:
        if text.startswith("(*", i):
            if depth == 0:
                start = i
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth > 0:
            depth -= 1
            i += 2
            if depth == 0:
                yield text.count("\n", 0, start) + 1, text[start:i]
        elif text[i] == '"' and depth == 0:
            j = text.find('"', i + 1)
            i = n if j < 0 else j + 1
        else:
            i += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--quiet", action="store_true",
                        help="print nothing, exit 1 if a stale citation exists")
    args = parser.parse_args()

    sources = sorted(list((ROOT / "theories").rglob("*.v")) +
                     list((ROOT / "library").rglob("*.v")) +
                     list((ROOT / "extension").rglob("*.v")))
    known = set()
    for v in sources:
        g = v.with_suffix(".glob")
        if g.exists():
            known |= glob_names(g)
    for d in installed_glob_dirs():
        if d.exists():
            for g in d.rglob("*.glob"):
                known |= glob_names(g, defs_only=True)

    modules = set()
    for v in sources:
        parts = v.relative_to(ROOT).with_suffix("").parts[1:]
        modules.update({v.stem, "/".join(parts), ".".join(parts)})

    prefixes = {}
    for name in known:
        if "_" in name:
            head = name.split("_", 1)[0]
            prefixes[head] = prefixes.get(head, 0) + 1

    stale = []
    for v in sources:
        text = v.read_text(errors="replace")
        seen = set()
        for lineno, comment in comments(text):
            for m in IDENT.finditer(comment):
                tok = m.group(0)
                if tok in known or tok in modules or tok in ACCEPTED:
                    continue
                if tok in seen:
                    continue
                if tok.startswith("_") or tok.endswith("_"):
                    continue
                under = tok.count("_")
                suspicious = False
                if under >= 2:
                    suspicious = True
                elif under == 1:
                    head, tail = tok.split("_")
                    if (len(head) >= 3 and len(tail) >= 3 and
                            prefixes.get(head, 0) >= 3):
                        suspicious = True
                elif under == 0 and len(tok) >= 8 and CAMEL.match(tok):
                    suspicious = True
                if suspicious:
                    seen.add(tok)
                    line = lineno + comment.count("\n", 0, m.start())
                    stale.append((str(v.relative_to(ROOT)), line, tok))

    if not args.quiet:
        for rel, line, tok in stale:
            print(f"{rel}:{line}: {tok}")
        print(f"{len(stale)} stale citation(s) in "
              f"{len({s[0] for s in stale})} module(s)", file=sys.stderr)
    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main())
