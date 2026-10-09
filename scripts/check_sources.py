#!/usr/bin/env python3
"""Check the rules on sources that the build does not check.

1. The frozen files are unchanged. The code of each file of FROZEN, with
   comments removed and whitespace collapsed, must equal its code at the
   commit named in check/frozen-baseline. Comments may change. The files
   of EXACT must be byte-identical to that commit. The code of each file
   of EXTENSION_FROZEN, the statement of the universality theorem of
   extension/ and its definitions, must equal its code at the commit
   EXTENSION_BASELINE, the merge that brought them to main. The code of
   each file of PHASE6_FROZEN, the statements of the finite-mixture
   theorem and of its corollary for the paired law and their definitions,
   must equal its code at the commit PHASE6_BASELINE, at which the user
   accepted them.
2. No module of theories/, library/ or extension/ contains Admitted,
   Axiom, Parameter or Conjecture outside comments.
3. library/ is independent of the papers and of Stdlib's reals: no module
   of library/ requires a module of EllipsoidFitting or
   EllipsoidUniversality, Stdlib's real analysis (Reals, Lra, Psatz,
   Rpower and the other R* modules) or MathComp's bridge to them (Rstruct,
   Rstruct_topology).
4. Given the output of check/Assumptions.v as first argument, every axiom
   it prints is among those of check/assumptions.expected. Given the output
   of check/UniversalityAssumptions.v as second argument, every axiom it
   prints is among those of check/universality_assumptions.expected. Fewer
   is fine. Every axiom of check/universality_assumptions.expected is among
   those of check/assumptions.expected, whose text is frozen (EXACT).
5. check/UniversalityAssumptions.v has the code UNIVERSALITY_CHECK: it
   checks that universality_theorem proves the frozen statement
   universality_statement, and prints the axioms of universality_theorem.
6. Phase 6. check/MixtureAssumptions.v and check/PairedAssumptions.v have
   the codes MIXTURE_CHECK and PAIRED_CHECK: they check that
   mixture_theorem proves mixture_theorem_statement and paired_theorem
   proves paired_statement, and print their axioms. Given these outputs as
   third and fourth arguments, every axiom they print is among those of
   check/mixture_assumptions.expected and check/paired_assumptions.expected,
   whose axioms are among those of check/assumptions.expected.

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
EXTENSION_FROZEN = [
    "extension/UniversalityDefinitions.v",
    "extension/UniversalityStatement.v",
]
EXTENSION_BASELINE = "3c6afa103ccd56c7d98bc59cb253d5d40d13fda0"
PHASE6_FROZEN = [
    "extension/MixtureDefinitions.v",
    "extension/MixtureStatement.v",
    "extension/PairedDefinitions.v",
    "extension/PairedStatement.v",
]
PHASE6_BASELINE = "eef46941972935dfaaef689a853f94d7e7d4798c"
UNIVERSALITY_CHECK = (
    "From EllipsoidUniversality Require Import UniversalityStatement "
    "UniversalityTheorem. Definition universality_theorem_checked : "
    "universality_statement := universality_theorem. "
    "Print Assumptions universality_theorem.")
MIXTURE_CHECK = (
    "From EllipsoidUniversality Require Import MixtureStatement "
    "MixtureTheorem. Definition mixture_theorem_checked : "
    "mixture_theorem_statement := mixture_theorem. "
    "Print Assumptions mixture_theorem.")
PAIRED_CHECK = (
    "From EllipsoidUniversality Require Import PairedStatement "
    "PairedTheorem. Definition paired_theorem_checked : "
    "paired_statement := paired_theorem. "
    "Print Assumptions paired_theorem.")
# The theorems of phase 6: name, check file, its code, expected axioms.
PHASE6_THEOREMS = [
    ("mixture theorem", "check/MixtureAssumptions.v", MIXTURE_CHECK,
     "check/mixture_assumptions.expected"),
    ("paired theorem", "check/PairedAssumptions.v", PAIRED_CHECK,
     "check/paired_assumptions.expected"),
]
PAPERS = {"EllipsoidFitting", "EllipsoidUniversality"}
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
    for path in EXTENSION_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(EXTENSION_BASELINE, path)):
            failures.append(f"{path}: code differs from {EXTENSION_BASELINE[:12]}")
    for path in PHASE6_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE6_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE6_BASELINE[:12]}")
    sources = [path for top in ("theories", "library", "extension")
               for path in sorted((ROOT / top).rglob("*.v"))]
    for path in sources:
        for match in ASSUMPTION.finditer(strip_comments(path.read_text())):
            failures.append(f"{path.relative_to(ROOT)}: {match.group(1).strip()}")
    library = sorted((ROOT / "library").rglob("*.v"))
    for path in library:
        for root, name in library_imports(path.read_text()):
            full = f"{root}.{name}" if root else name
            last = full.split(".")[-1]
            stdlib = root.startswith(("Stdlib", "Coq")) or not root
            if PAPERS & set(full.split(".")):
                failures.append(f"{path.relative_to(ROOT)}: requires {full} of a paper")
            elif stdlib and (STDLIB_REALS.match(last) or "Reals" in full.split(".")):
                failures.append(f"{path.relative_to(ROOT)}: requires Stdlib's {full}")
            elif last in MATHCOMP_BRIDGE:
                failures.append(f"{path.relative_to(ROOT)}: requires {full}")
    if code((ROOT / "check" / "UniversalityAssumptions.v").read_text()) != UNIVERSALITY_CHECK:
        failures.append("check/UniversalityAssumptions.v: code differs from UNIVERSALITY_CHECK")
    allowed = axiom_names((ROOT / "check" / "assumptions.expected").read_text())
    allowed_universality = axiom_names(
        (ROOT / "check" / "universality_assumptions.expected").read_text())
    for name in sorted(allowed_universality - allowed):
        failures.append(f"check/universality_assumptions.expected: {name} "
                        "is not among check/assumptions.expected")
    if len(sys.argv) > 1:
        printed = axiom_names(Path(sys.argv[1]).read_text())
        for name in sorted(printed - allowed):
            failures.append(f"main theorem: {name} is not among check/assumptions.expected")
        if not failures and printed != allowed:
            print("main theorem: fewer axioms than check/assumptions.expected:",
                  ", ".join(sorted(printed)) or "none")
    if len(sys.argv) > 2:
        printed = axiom_names(Path(sys.argv[2]).read_text())
        for name in sorted(printed - allowed_universality):
            failures.append(f"universality theorem: {name} is not among "
                            "check/universality_assumptions.expected")
        if not failures and printed != allowed_universality:
            print("universality theorem: fewer axioms than "
                  "check/universality_assumptions.expected:",
                  ", ".join(sorted(printed)) or "none")
    for k, (name, check, check_code, expected) in enumerate(PHASE6_THEOREMS):
        if code((ROOT / check).read_text()) != check_code:
            failures.append(f"{check}: code differs from the expected check")
        allowed_k = axiom_names((ROOT / expected).read_text())
        for ax in sorted(allowed_k - allowed):
            failures.append(f"{expected}: {ax} is not among check/assumptions.expected")
        if len(sys.argv) > 3 + k:
            printed = axiom_names(Path(sys.argv[3 + k]).read_text())
            for ax in sorted(printed - allowed_k):
                failures.append(f"{name}: {ax} is not among {expected}")
            if not failures and printed != allowed_k:
                print(f"{name}: fewer axioms than {expected}:",
                      ", ".join(sorted(printed)) or "none")
    for line in failures:
        print(line)
    if failures:
        sys.exit(1)
    print(f"{len(FROZEN)} frozen files unchanged since {commit[:12]}; "
          f"{len(EXTENSION_FROZEN)} frozen files of extension/ unchanged since "
          f"{EXTENSION_BASELINE[:12]}; "
          f"{len(PHASE6_FROZEN)} frozen files of phase 6 unchanged since "
          f"{PHASE6_BASELINE[:12]}; "
          f"no Admitted, Axiom, Parameter or Conjecture; "
          f"{len(library)} library modules independent of the papers and of Stdlib's reals"
          + ("; axioms of the main theorem allowed" if len(sys.argv) > 1 else "")
          + ("; axioms of the universality theorem allowed" if len(sys.argv) > 2 else "")
          + ("; axioms of the mixture theorem allowed" if len(sys.argv) > 3 else "")
          + ("; axioms of the paired theorem allowed" if len(sys.argv) > 4 else ""))


if __name__ == "__main__":
    main()
