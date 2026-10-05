#!/usr/bin/env python3
"""Check the rules on sources that the build does not check.

1. The frozen files are unchanged. The code of each file of FROZEN, with
   comments removed and whitespace collapsed, must equal its code at the
   commit named in check/frozen-baseline. Comments may change. The files
   of EXACT must be byte-identical to that commit.
2. No module of theories/ or library/ contains Admitted, Axiom, Parameter
   or Conjecture outside comments.
3. library/ is independent of the paper and of Stdlib's reals: no module
   of library/ requires a module of EllipsoidFitting, Stdlib's real
   analysis (Reals, Lra, Psatz, Rpower and the other R* modules) or
   MathComp's bridge to them (Rstruct, Rstruct_topology).
4. Given the output of check/Assumptions.v as argument, every axiom it
   prints is among those of check/assumptions.expected. Fewer is fine.

`make check` runs this script after the build. It exits 1 on any failure.
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from export_from_ellipsoid_rocq import strip_comments  # noqa: E402

FROZEN = [
    "theories/MainStatement.v",
    "theories/MainTheorem.v",
    "theories/PaperMainResults.v",
    "theories/PaperMainDefinitions.v",
    "theories/GaussianProbabilityProductDefinitions.v",
    "theories/GaussianProbabilityDefinitions.v",
    "theories/GaussianDefinitions.v",
    "theories/AnalysisIntegralDefinitions.v",
]
EXACT = ["check/Assumptions.v", "check/assumptions.expected"]
ASSUMPTION = re.compile(
    r"(?:\A|(?<=\.))\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+)?"
    r"(Admitted\s*\.|Axioms?\b|Parameters?\b|Conjecture\b)")
REQUIRE = re.compile(r"(?:From\s+([\w.]+)\s+)?Require(?:\s+(?:Import|Export))?\s+([^.]+(?:\.[A-Za-z]\w*)*)\s*\.", re.S)
STDLIB_REALS = re.compile(r"^(Reals|Lra|Psatz|Fourier|Ranalysis\w*|R[A-Z]\w*|Rbase|Rfunctions|Rpower|Rtrigo\w*|Rdefinitions|Raxioms|Rbasic_fun|Rsqrt_def|Rlimit|Rseries|Rcomplete|Rderiv|Rprod|Rtopology|SeqProp|SeqSeries|PSeries_reg|Exp_prop|Ratan|Rsigma|Rgeom|Cos_rel|Sqrt_reg|ClassicalDedekindReals|ConstructiveCauchyReals\w*)$")
MATHCOMP_BRIDGE = {"Rstruct", "Rstruct_topology"}


def code(text):
    return " ".join(strip_comments(text).split())


def at_baseline(commit, path):
    return subprocess.run(["git", "-C", str(ROOT), "show", f"{commit}:{path}"],
                          check=True, capture_output=True, text=True).stdout


def library_imports(text):
    """Pairs (root, module) of the Require commands of a source."""
    for match in REQUIRE.finditer(strip_comments(text)):
        root = match.group(1) or ""
        for name in match.group(2).split():
            yield root, name


def axiom_names(text):
    names, header = set(), None
    for line in text.splitlines():
        if not line or line[0].isspace():
            continue
        if line.rstrip().endswith(":") and " " not in line.rstrip()[:-1]:
            header = line.rstrip()
            if header != "Axioms:":
                names.add("unexpected section " + header)
            continue
        if line.startswith("Closed under the global context"):
            continue
        names.add(line.split(" :", 1)[0].strip())
    return names


def main():
    commit = (ROOT / "check" / "frozen-baseline").read_text().split()[0]
    failures = []
    for path in FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(commit, path)):
            failures.append(f"{path}: code differs from {commit[:12]}")
    for path in EXACT:
        if (ROOT / path).read_text() != at_baseline(commit, path):
            failures.append(f"{path}: differs from {commit[:12]}")
    sources = sorted((ROOT / "theories").rglob("*.v")) + sorted((ROOT / "library").rglob("*.v"))
    for path in sources:
        for match in ASSUMPTION.finditer(strip_comments(path.read_text())):
            failures.append(f"{path.relative_to(ROOT)}: {match.group(1).strip()}")
    library = sorted((ROOT / "library").rglob("*.v"))
    for path in library:
        for root, name in library_imports(path.read_text()):
            full = f"{root}.{name}" if root else name
            last = full.split(".")[-1]
            stdlib = root.startswith(("Stdlib", "Coq")) or not root
            if "EllipsoidFitting" in full.split("."):
                failures.append(f"{path.relative_to(ROOT)}: requires {full} of the paper")
            elif stdlib and (STDLIB_REALS.match(last) or "Reals" in full.split(".")):
                failures.append(f"{path.relative_to(ROOT)}: requires Stdlib's {full}")
            elif last in MATHCOMP_BRIDGE:
                failures.append(f"{path.relative_to(ROOT)}: requires {full}")
    if len(sys.argv) > 1:
        printed = axiom_names(Path(sys.argv[1]).read_text())
        allowed = axiom_names((ROOT / "check" / "assumptions.expected").read_text())
        for name in sorted(printed - allowed):
            failures.append(f"main theorem: {name} is not among check/assumptions.expected")
        if not failures and printed != allowed:
            print("main theorem: fewer axioms than check/assumptions.expected:",
                  ", ".join(sorted(printed)) or "none")
    for line in failures:
        print(line)
    if failures:
        sys.exit(1)
    print(f"{len(FROZEN)} frozen files unchanged since {commit[:12]}; "
          f"no Admitted, Axiom, Parameter or Conjecture; "
          f"{len(library)} library modules independent of the paper and of Stdlib's reals"
          + ("; axioms of the main theorem allowed" if len(sys.argv) > 1 else ""))


if __name__ == "__main__":
    main()
