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
7. Phase 7. The check files and expected lists of CHECKS_EXACT, those of
   the axiom checks of phases 5 and 6, are byte-identical to the commit
   CHECKS_BASELINE. Every axiom report given as an argument has the line
   "Axioms:" or the line "Closed under the global context"; a report with
   neither, for example an empty one, is an error, not an empty set of
   axioms. The definition of tuple_prod, on which the frozen statements of
   phases 5 and 6 depend, is pinned: the Require commands of TUPLE_PROD
   and the code of its section tuple_prod must equal their code at
   CHECKS_BASELINE.
8. Phase 7. The code of each file of LATENT_FROZEN, the statement of the
   latent-sign corollary and its definitions, must equal its code at the
   commit LATENT_BASELINE, at which the user accepted them.
   check/LatentSignAssumptions.v has the code LATENT_CHECK: it checks that
   latent_sign_theorem proves latent_sign_statement and prints its axioms.
   Given its output as fifth argument, every axiom it prints is among those
   of check/latent_sign_assumptions.expected, whose axioms are among those
   of check/assumptions.expected.
9. Phase 8. The code of each file of PHASE8_FROZEN, the statements of the
   countable-mixture theorem, of the condition-number theorem and of the
   scope results on the latent-sign law, and their definitions, must equal
   its code at the commit PHASE8_BASELINE, at which the user accepted them.
10. Phase 8. check/CountableAssumptions.v, check/ConditionAssumptions.v
   and check/LatentScopeAssumptions.v have the codes COUNTABLE_CHECK,
   CONDITION_CHECK and LATENT_SCOPE_CHECK: they check that
   countable_theorem proves countable_theorem_statement, condition_theorem
   proves condition_theorem_statement and latent_scope_theorem proves
   latent_scope_statement, and print their axioms. Given their outputs as
   sixth, seventh and eighth arguments, every axiom they print is among
   those of check/countable_assumptions.expected,
   check/condition_assumptions.expected and
   check/latent_scope_assumptions.expected, whose axioms are among those
   of check/assumptions.expected.
11. Phase 9. An axiom report with the line "Axioms:" must list at least
   one axiom after it; a report without axioms is accepted only through
   the line "Closed under the global context". The check files and
   expected lists of CHECKS_EXACT_P8, those of the axiom checks of phases
   7 and 8, are byte-identical to the commit CHECKS_P8_BASELINE, a
   separate baseline; CHECKS_BASELINE and check/frozen-baseline do not
   change.
12. Phase 9. The code of each file of PHASE9_FROZEN, the statements of the
   robustness corollary, of the tensorization bounds of the latent-sign
   law, of the continuous-latent counterexample and of the endpoint
   expansions of the condition-number curve, and their definitions, must
   equal its code at the commit PHASE9_BASELINE, at which the user accepted
   them.
13. Phase 9. check/RobustAssumptions.v, check/LatentTensorAssumptions.v,
   check/ContinuousLatentAssumptions.v and
   check/ConditionEndpointsAssumptions.v have the codes ROBUST_CHECK,
   LATENT_TENSOR_CHECK, CONTINUOUS_LATENT_CHECK and
   CONDITION_ENDPOINTS_CHECK: they check that robust_theorem proves
   robust_theorem_statement, latent_tensor_theorem proves
   latent_tensorization_statement, continuous_latent_theorem proves
   continuous_latent_statement and condition_endpoints_theorem proves
   condition_endpoints_statement, and print their axioms. Given their
   outputs as ninth to twelfth arguments, every axiom they print is among
   those of check/robust_assumptions.expected,
   check/latent_tensor_assumptions.expected,
   check/continuous_latent_assumptions.expected and
   check/condition_endpoints_assumptions.expected, whose axioms are among
   those of check/assumptions.expected.
14. Phase 10. The code of each file of PHASE10_FROZEN, the statements of
   the robustness of the optimal condition number and of the finite
   tensorization constant of the latent-sign law, must equal its code at
   the commit PHASE10_BASELINE, at which the user accepted them.
15. Phase 10. check/ConditionRobustAssumptions.v and
   check/LatentTensorUpperAssumptions.v have the codes
   CONDITION_ROBUST_CHECK and LATENT_TENSOR_UPPER_CHECK: they check that
   robust_condition_theorem proves robust_condition_theorem_statement and
   latent_tensor_upper_theorem proves latent_tensor_upper_statement, and
   print their axioms. Given their outputs as thirteenth and fourteenth
   arguments, every axiom they print is among those of
   check/condition_robust_assumptions.expected and
   check/latent_tensor_upper_assumptions.expected, whose axioms are among
   those of check/assumptions.expected.
16. Phase 10. The check files and expected lists of CHECKS_EXACT_P9, those
   of the axiom checks of phase 9, are byte-identical to the commit
   CHECKS_P9_BASELINE, a separate baseline; CHECKS_BASELINE,
   CHECKS_P8_BASELINE and check/frozen-baseline do not change.
17. Phase 11. The code of each file of PHASE11_FROZEN, the definitions of
   the condition-number curve at every fourth moment and the statements of
   the curve, of the threshold theorem at every fourth moment and of its
   robustness, must equal its code at the commit PHASE11_BASELINE, at which
   the user accepted them.
18. Phase 11. The check files and expected lists of CHECKS_EXACT_P10, those
   of the axiom checks of phase 10, are byte-identical to the commit
   CHECKS_P10_BASELINE, a separate baseline; CHECKS_BASELINE,
   CHECKS_P8_BASELINE, CHECKS_P9_BASELINE and check/frozen-baseline do not
   change.

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
CHECKS_EXACT = [
    "check/UniversalityAssumptions.v",
    "check/universality_assumptions.expected",
    "check/MixtureAssumptions.v",
    "check/mixture_assumptions.expected",
    "check/PairedAssumptions.v",
    "check/paired_assumptions.expected",
]
CHECKS_BASELINE = "c3e555eba4d2d3958d76418c21feebcc241510fc"
CHECKS_EXACT_P8 = [
    "check/LatentSignAssumptions.v",
    "check/latent_sign_assumptions.expected",
    "check/CountableAssumptions.v",
    "check/countable_assumptions.expected",
    "check/ConditionAssumptions.v",
    "check/condition_assumptions.expected",
    "check/LatentScopeAssumptions.v",
    "check/latent_scope_assumptions.expected",
]
CHECKS_P8_BASELINE = "a89ed1e6e29e1041a9a108d82f85bc84620bdd3d"
CHECKS_EXACT_P9 = [
    "check/RobustAssumptions.v",
    "check/robust_assumptions.expected",
    "check/LatentTensorAssumptions.v",
    "check/latent_tensor_assumptions.expected",
    "check/ContinuousLatentAssumptions.v",
    "check/continuous_latent_assumptions.expected",
    "check/ConditionEndpointsAssumptions.v",
    "check/condition_endpoints_assumptions.expected",
]
CHECKS_P9_BASELINE = "e4c46e12d61a28bed6047968565c8424b505319b"
CHECKS_EXACT_P10 = [
    "check/ConditionRobustAssumptions.v",
    "check/condition_robust_assumptions.expected",
    "check/LatentTensorUpperAssumptions.v",
    "check/latent_tensor_upper_assumptions.expected",
]
CHECKS_P10_BASELINE = "eda8a0651798999ec6b9f677532107aae60b0623"
TUPLE_PROD = "library/probability/lindeberg.v"
LATENT_FROZEN = [
    "extension/LatentSignDefinitions.v",
    "extension/LatentSignStatement.v",
]
LATENT_BASELINE = "d4de51d11b12b50afa4c96a7fa90b37f9f6b92ee"
PHASE8_FROZEN = [
    "extension/CountableMixtureDefinitions.v",
    "extension/CountableMixtureStatement.v",
    "extension/ConditionDefinitions.v",
    "extension/ConditionStatement.v",
    "extension/LatentSignScope.v",
]
PHASE8_BASELINE = "5442e84ba6cdc9ad69848040ea4483269e578896"
PHASE9_FROZEN = [
    "extension/RobustDefinitions.v",
    "extension/RobustStatement.v",
    "extension/LatentTensorization.v",
    "extension/ContinuousLatent.v",
    "extension/ConditionEndpoints.v",
]
PHASE9_BASELINE = "1c05ffcbebc81492639e7f9afc7b3dc2b88021e0"
PHASE10_FROZEN = [
    "extension/ConditionRobustStatement.v",
    "extension/LatentTensorUpper.v",
]
PHASE10_BASELINE = "b26eb1e0eff32371248c211ece597fc9bc3463f9"
PHASE11_FROZEN = [
    "extension/ConditionKappaDefinitions.v",
    "extension/ConditionKappaCurveStatement.v",
    "extension/ConditionKappaStatement.v",
    "extension/ConditionKappaRobustStatement.v",
]
PHASE11_BASELINE = "c5f41c44e5bc2622f6dfd940c654553503e9eb1d"
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
LATENT_CHECK = (
    "From EllipsoidUniversality Require Import LatentSignStatement "
    "LatentSignTheorem. Definition latent_sign_theorem_checked : "
    "latent_sign_statement := latent_sign_theorem. "
    "Print Assumptions latent_sign_theorem.")
COUNTABLE_CHECK = (
    "From EllipsoidUniversality Require Import CountableMixtureStatement "
    "CountableTheorem. Definition countable_theorem_checked : "
    "countable_theorem_statement := countable_theorem. "
    "Print Assumptions countable_theorem.")
CONDITION_CHECK = (
    "From EllipsoidUniversality Require Import ConditionStatement "
    "ConditionTheorem. Definition condition_theorem_checked : "
    "condition_theorem_statement := condition_theorem. "
    "Print Assumptions condition_theorem.")
LATENT_SCOPE_CHECK = (
    "From EllipsoidUniversality Require Import LatentSignScope "
    "LatentScopeTheorem. Definition latent_scope_theorem_checked : "
    "latent_scope_statement := latent_scope_theorem. "
    "Print Assumptions latent_scope_theorem.")
ROBUST_CHECK = (
    "From EllipsoidUniversality Require Import RobustStatement "
    "RobustTheorem. Definition robust_theorem_checked : "
    "robust_theorem_statement := robust_theorem. "
    "Print Assumptions robust_theorem.")
LATENT_TENSOR_CHECK = (
    "From EllipsoidUniversality Require Import LatentTensorization "
    "LatentTensorTheorem. Definition latent_tensor_theorem_checked : "
    "latent_tensorization_statement := latent_tensor_theorem. "
    "Print Assumptions latent_tensor_theorem.")
CONTINUOUS_LATENT_CHECK = (
    "From EllipsoidUniversality Require Import ContinuousLatent "
    "ContinuousLatentTheorem. Definition continuous_latent_theorem_checked : "
    "continuous_latent_statement := continuous_latent_theorem. "
    "Print Assumptions continuous_latent_theorem.")
CONDITION_ENDPOINTS_CHECK = (
    "From EllipsoidUniversality Require Import ConditionEndpoints "
    "ConditionEndpointsTheorem. Definition condition_endpoints_theorem_checked "
    ": condition_endpoints_statement := condition_endpoints_theorem. "
    "Print Assumptions condition_endpoints_theorem.")
CONDITION_ROBUST_CHECK = (
    "From EllipsoidUniversality Require Import ConditionRobustStatement "
    "ConditionRobustTheorem. Definition robust_condition_theorem_checked "
    ": robust_condition_theorem_statement := robust_condition_theorem. "
    "Print Assumptions robust_condition_theorem.")
LATENT_TENSOR_UPPER_CHECK = (
    "From EllipsoidUniversality Require Import LatentTensorUpper "
    "LatentTensorUpperTheorem. Definition latent_tensor_upper_theorem_checked "
    ": latent_tensor_upper_statement := latent_tensor_upper_theorem. "
    "Print Assumptions latent_tensor_upper_theorem.")
# The theorems of phases 6 and 7: name, check file, its code, expected
# axioms; their reports are the third, fourth and fifth arguments.
PHASE6_THEOREMS = [
    ("mixture theorem", "check/MixtureAssumptions.v", MIXTURE_CHECK,
     "check/mixture_assumptions.expected"),
    ("paired theorem", "check/PairedAssumptions.v", PAIRED_CHECK,
     "check/paired_assumptions.expected"),
    ("latent-sign theorem", "check/LatentSignAssumptions.v", LATENT_CHECK,
     "check/latent_sign_assumptions.expected"),
]
# The theorems of phase 8; their reports are the sixth, seventh and eighth
# arguments.
PHASE8_THEOREMS = [
    ("countable-mixture theorem", "check/CountableAssumptions.v",
     COUNTABLE_CHECK, "check/countable_assumptions.expected"),
    ("condition-number theorem", "check/ConditionAssumptions.v",
     CONDITION_CHECK, "check/condition_assumptions.expected"),
    ("latent-sign scope theorem", "check/LatentScopeAssumptions.v",
     LATENT_SCOPE_CHECK, "check/latent_scope_assumptions.expected"),
]
# The theorems of phase 9; their reports are the ninth to twelfth
# arguments.
PHASE9_THEOREMS = [
    ("robustness theorem", "check/RobustAssumptions.v", ROBUST_CHECK,
     "check/robust_assumptions.expected"),
    ("tensorization theorem", "check/LatentTensorAssumptions.v",
     LATENT_TENSOR_CHECK, "check/latent_tensor_assumptions.expected"),
    ("continuous-latent theorem", "check/ContinuousLatentAssumptions.v",
     CONTINUOUS_LATENT_CHECK, "check/continuous_latent_assumptions.expected"),
    ("condition-endpoints theorem", "check/ConditionEndpointsAssumptions.v",
     CONDITION_ENDPOINTS_CHECK,
     "check/condition_endpoints_assumptions.expected"),
]
# The theorems of phase 10; their reports are the thirteenth and
# fourteenth arguments.
PHASE10_THEOREMS = [
    ("robust condition-number theorem", "check/ConditionRobustAssumptions.v",
     CONDITION_ROBUST_CHECK, "check/condition_robust_assumptions.expected"),
    ("tensorization upper bound", "check/LatentTensorUpperAssumptions.v",
     LATENT_TENSOR_UPPER_CHECK,
     "check/latent_tensor_upper_assumptions.expected"),
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


def tuple_prod_code(text):
    """The Require commands of TUPLE_PROD and the code of its section
    tuple_prod, comments removed and whitespace collapsed."""
    stripped = strip_comments(text)
    requires = " ".join(m.group(0) for m in REQUIRE.finditer(stripped))
    section = re.search(r"Section tuple_prod\..*?End tuple_prod\.", stripped, re.S)
    return " ".join(requires.split()), " ".join(section.group(0).split()) if section else None


def report_complete(text):
    """An axiom report is complete when it has the line "Closed under the
    global context", or the line "Axioms:" followed by at least one
    axiom. A report with the line "Axioms:" and no axiom is incomplete."""
    lines = text.splitlines()
    if any(line.startswith("Closed under the global context") for line in lines):
        return True
    if any(line.rstrip() == "Axioms:" for line in lines):
        return any(not name.startswith("unexpected section ")
                   for name in axiom_names(text))
    return False


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
    for path in LATENT_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(LATENT_BASELINE, path)):
            failures.append(f"{path}: code differs from {LATENT_BASELINE[:12]}")
    for path in PHASE8_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE8_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE8_BASELINE[:12]}")
    for path in PHASE9_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE9_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE9_BASELINE[:12]}")
    for path in PHASE10_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE10_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE10_BASELINE[:12]}")
    for path in PHASE11_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE11_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE11_BASELINE[:12]}")
    for path in CHECKS_EXACT:
        if (ROOT / path).read_text() != at_baseline(CHECKS_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_BASELINE[:12]}")
    for path in CHECKS_EXACT_P8:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P8_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P8_BASELINE[:12]}")
    for path in CHECKS_EXACT_P9:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P9_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P9_BASELINE[:12]}")
    for path in CHECKS_EXACT_P10:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P10_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P10_BASELINE[:12]}")
    now = tuple_prod_code((ROOT / TUPLE_PROD).read_text())
    if now[1] is None:
        failures.append(f"{TUPLE_PROD}: no section tuple_prod")
    elif now != tuple_prod_code(at_baseline(CHECKS_BASELINE, TUPLE_PROD)):
        failures.append(f"{TUPLE_PROD}: the Require commands or the section "
                        f"tuple_prod differ from {CHECKS_BASELINE[:12]}")
    for arg in sys.argv[1:]:
        if not report_complete(Path(arg).read_text()):
            failures.append(f"{arg}: the axiom report has neither the line "
                            "Axioms: with at least one axiom nor the line "
                            "Closed under the global context")
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
    for k, (name, check, check_code, expected) in enumerate(
            PHASE6_THEOREMS + PHASE8_THEOREMS + PHASE9_THEOREMS
            + PHASE10_THEOREMS):
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
          f"{len(CHECKS_EXACT)} check files and tuple_prod unchanged since "
          f"{CHECKS_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P8)} check files of phases 7 and 8 unchanged since "
          f"{CHECKS_P8_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P9)} check files of phase 9 unchanged since "
          f"{CHECKS_P9_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P10)} check files of phase 10 unchanged since "
          f"{CHECKS_P10_BASELINE[:12]}; "
          f"{len(LATENT_FROZEN)} frozen files of phase 7 unchanged since "
          f"{LATENT_BASELINE[:12]}; "
          f"{len(PHASE8_FROZEN)} frozen files of phase 8 unchanged since "
          f"{PHASE8_BASELINE[:12]}; "
          f"{len(PHASE9_FROZEN)} frozen files of phase 9 unchanged since "
          f"{PHASE9_BASELINE[:12]}; "
          f"{len(PHASE10_FROZEN)} frozen files of phase 10 unchanged since "
          f"{PHASE10_BASELINE[:12]}; "
          f"{len(PHASE11_FROZEN)} frozen files of phase 11 unchanged since "
          f"{PHASE11_BASELINE[:12]}; "
          f"no Admitted, Axiom, Parameter or Conjecture; "
          f"{len(library)} library modules independent of the papers and of Stdlib's reals"
          + ("; axioms of the main theorem allowed" if len(sys.argv) > 1 else "")
          + ("; axioms of the universality theorem allowed" if len(sys.argv) > 2 else "")
          + ("; axioms of the mixture theorem allowed" if len(sys.argv) > 3 else "")
          + ("; axioms of the paired theorem allowed" if len(sys.argv) > 4 else "")
          + ("; axioms of the latent-sign theorem allowed" if len(sys.argv) > 5 else "")
          + ("; axioms of the countable-mixture theorem allowed" if len(sys.argv) > 6 else "")
          + ("; axioms of the condition-number theorem allowed" if len(sys.argv) > 7 else "")
          + ("; axioms of the latent-sign scope theorem allowed" if len(sys.argv) > 8 else "")
          + ("; axioms of the robustness theorem allowed" if len(sys.argv) > 9 else "")
          + ("; axioms of the tensorization theorem allowed" if len(sys.argv) > 10 else "")
          + ("; axioms of the continuous-latent theorem allowed" if len(sys.argv) > 11 else "")
          + ("; axioms of the condition-endpoints theorem allowed" if len(sys.argv) > 12 else "")
          + ("; axioms of the robust condition-number theorem allowed" if len(sys.argv) > 13 else "")
          + ("; axioms of the tensorization upper bound allowed" if len(sys.argv) > 14 else ""))


if __name__ == "__main__":
    main()
