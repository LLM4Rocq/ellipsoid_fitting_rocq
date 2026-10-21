#!/usr/bin/env python3
"""Write the statement snapshots of rule 30 of scripts/check_sources.py and
their references, from builds of the acceptance commits.

    snapshot_baselines.py build [NAME...]       build each baseline
    snapshot_baselines.py files [NAME...]       write check/snapshots/<Name>.v
    snapshot_baselines.py references [NAME...]  write check/snapshots/<Name>.txt
    snapshot_baselines.py verify [NAME...]      compare instead of writing
    snapshot_baselines.py identity-files        write check/identity/inventory.json
                                                and the identity drivers
    snapshot_baselines.py identities [NAME...]  write the identity references
    snapshot_baselines.py identities-verify [NAME...]
                                                compare instead of writing

Run it where rocq and make are those of the pinned toolchain: in the
container of the VM (environment/proof-shell.sh), or in the opam switch
rocq-analysis. --jobs N sets the parallel jobs of the builds (default 3).

Each entry of BASELINES is one acceptance baseline: a commit, the frozen
modules accepted there, the pinned sections whose code is compared with that
commit, and the check files whose lemma statements are snapshotted against
that commit's library. For each:

- build: exports the commit (git archive) into build/baselines/<commit>/
  (the first 12 digits; entries of one commit share it) and
  compiles, with that commit's own Makefile and _CoqProject, the modules
  needed; then compiles the check files of the entry, as they are in
  this tree (their code is fixed and has not changed since their freezes),
  against that build, into build/baselines/<name>/checks/ as Checks.<Name>.
  An existing build directory is refused; choose a new --baselines path.
  The later commands verify tracked source bytes against git and the
  recorded toolchain. Generated artifacts still require a controlled build
  directory from that fresh run; source equality is not a cache signature.
- files: writes the snapshot file check/snapshots/<Name>.v. It only Requires
  the frozen modules and the compiled check files, without Import, sets
  Set Printing All, Set Printing Universes, Set Printing Depth 1000000 and
  Set Printing Width 78, and prints each declaration of each frozen module,
  in the order that Print Module lists them: Print (body and type) for
  definitions and inductive types, Check (statement only) for the lemmas
  that the .glob file of the module marks as proofs (prf); then Print of the
  definitions and Check of the lemmas of each pinned section (from the
  .glob of its module, at the baseline); then Check of each lemma of the
  check files (CHECK_LEMMAS).
- references: compiles each snapshot file against its baseline build, with
  the load paths of that build, and writes its output to
  check/snapshots/<Name>.txt, the reference.
- verify: the same, compared with the reference; exits 1 on a difference.

make check compiles the same snapshot files against the build of the tree,
through scripts/run_checks.py, and scripts/check_sources.py requires each
output to equal its reference, whose SHA-256 it fixes.

The identity layer (rule 30 (e), scripts/identity_sidecars.py):

- identity-files: writes check/identity/inventory.json, the queries that the
  snapshot files print, and for each snapshot that prints a declaration the
  driver check/identity/Identity<Name>.v (the snapshot's Require lines,
  Declare ML Module "kernel_identity", one KernelIdentity line per query);
- identities: builds the exporter of check/identity/ once, into
  <baselines>/identity-plugin/ (an existing directory is refused), compiles
  each driver against the build of its acceptance commit (a verified fresh
  archive), with OCAMLPATH set to that exporter for the driver only, and
  writes the sidecar of its output to check/identity/Identity<Name>.json,
  the reference, with check/identity/REFERENCES.json (commit, toolchain, the
  SHA-256 of the exporter's sources, of its build recipe and of the plugin
  built, the versions of ocamlopt and findlib, and the SHA-256 of each
  reference). A failure or a difference at a baseline stops the command: it
  goes to the user, and no reference is written from another tree;
- identities-verify: the same, compared with the references. A reference is never
regenerated to make an output pass: a difference is examined by a person."""

import argparse
import hashlib
import json
import io
import os
import re
import shutil
import subprocess
import sys
import tarfile
import types
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / "build" / "baselines"   # --baselines overrides it
SNAP = ROOT / "check" / "snapshots"
ROOTS = [("library", "GaussianAnalysis"), ("theories", "EllipsoidFitting"),
         ("extension", "EllipsoidUniversality"), ("applications", "GaussianApplications")]
WARNINGS = ["-w", "-notation-overridden", "-w", "-ambiguous-paths",
            "-w", "-notation-incompatible-prefix", "-w", "-hiding-delimiting-key",
            "-w", "-deprecated-library-file"]
EXPECTED_ROCQ = "The Rocq Prover, version 9.1.1"
EXPECTED_PACKAGES = {"rocq-core": "9.1.1", "rocq-mathcomp-ssreflect": "2.6.0",
                     "rocq-mathcomp-analysis": "1.16.0"}
BANNED_ENVIRONMENT = ("ROCQPATH", "COQPATH", "ROCQLIB", "COQLIB", "OCAMLPATH",
                      "CAML_LD_LIBRARY_PATH", "ROCQRC", "COQRC", "XDG_CONFIG_HOME",
                      "COQFLAGS", "COQEXTRAFLAGS", "OTHERFLAGS", "COQ_SRC_SUBDIRS",
                      "COQCHKEXTRAFLAGS")
EXTRACTED_THIS_RUN = set()
IDENTITY = ROOT / "check" / "identity"


def _load(name, path):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(Path(path).read_bytes(), str(path), "exec"), module.__dict__)
    return module


identity_sidecars = _load("identity_sidecars", ROOT / "scripts" / "identity_sidecars.py")
PROVENANCE_FILE = ".snapshot-archive.json"

# name, commit, frozen modules, pinned sections (module, section), check
# files, extra targets to build at the commit (paths of .vo files).
BASELINES = [
    ("SnapshotPhase1", "29df54e436f05dd3fad60377e2f9a45588c2942b",
     ["EllipsoidFitting.AnalysisIntegralDefinitions", "EllipsoidFitting.GaussianDefinitions",
      "EllipsoidFitting.GaussianProbabilityDefinitions",
      "EllipsoidFitting.GaussianProbabilityProductDefinitions",
      "EllipsoidFitting.PaperMainDefinitions", "EllipsoidFitting.MainStatement"], [], [], []),
    ("SnapshotPhase1Theorems", "29df54e436f05dd3fad60377e2f9a45588c2942b",
     ["EllipsoidFitting.PaperMainResults", "EllipsoidFitting.MainTheorem"], [], [], []),
    ("SnapshotPhase5", "3c6afa103ccd56c7d98bc59cb253d5d40d13fda0",
     ["EllipsoidUniversality.UniversalityDefinitions",
      "EllipsoidUniversality.UniversalityStatement"], [], [], []),
    ("SnapshotPhase6", "eef46941972935dfaaef689a853f94d7e7d4798c",
     ["EllipsoidUniversality.MixtureDefinitions", "EllipsoidUniversality.MixtureStatement",
      "EllipsoidUniversality.PairedDefinitions", "EllipsoidUniversality.PairedStatement"],
     [], [], []),
    ("SnapshotPhase7", "d4de51d11b12b50afa4c96a7fa90b37f9f6b92ee",
     ["EllipsoidUniversality.LatentSignDefinitions",
      "EllipsoidUniversality.LatentSignStatement"], [], [], []),
    ("SnapshotTupleProd", "c3e555eba4d2d3958d76418c21feebcc241510fc",
     [], [("GaussianAnalysis.probability.lindeberg", "tuple_prod")], [], []),
    ("SnapshotPhase8", "5442e84ba6cdc9ad69848040ea4483269e578896",
     ["EllipsoidUniversality.CountableMixtureDefinitions",
      "EllipsoidUniversality.CountableMixtureStatement",
      "EllipsoidUniversality.ConditionDefinitions", "EllipsoidUniversality.ConditionStatement",
      "EllipsoidUniversality.LatentSignScope"], [], [], []),
    ("SnapshotPhase9", "1c05ffcbebc81492639e7f9afc7b3dc2b88021e0",
     ["EllipsoidUniversality.RobustDefinitions", "EllipsoidUniversality.RobustStatement",
      "EllipsoidUniversality.LatentTensorization", "EllipsoidUniversality.ContinuousLatent",
      "EllipsoidUniversality.ConditionEndpoints"], [], [], []),
    ("SnapshotPhase10", "b26eb1e0eff32371248c211ece597fc9bc3463f9",
     ["EllipsoidUniversality.ConditionRobustStatement",
      "EllipsoidUniversality.LatentTensorUpper"], [], [], []),
    ("SnapshotPhase11", "c5f41c44e5bc2622f6dfd940c654553503e9eb1d",
     ["EllipsoidUniversality.ConditionKappaDefinitions",
      "EllipsoidUniversality.ConditionKappaCurveStatement",
      "EllipsoidUniversality.ConditionKappaStatement",
      "EllipsoidUniversality.ConditionKappaRobustStatement"], [], [], []),
    ("SnapshotPhase12Batch1", "fc76edfc953cac79f4fa258a3228cb536784cded",
     ["GaussianApplications.MatrixSeriesStatement", "GaussianApplications.GoeEdgeStatement",
      "GaussianApplications.PsdSplittingStatement"],
     [("GaussianAnalysis.matrix.lambda_max", "lambda_max")], [], []),
    ("SnapshotApplicationsDefinitions", "b6173f138f14d97a2587452e99eca14889a78b21",
     [], [], ["check/ApplicationsDefinitions.v"],
     ["library/gaussian/measurable_matrix.vo", "library/gaussian/gauss.vo",
      "library/matrix/euclidean.vo", "library/matrix/opnorm.vo", "library/matrix/psd_part.vo",
      "library/random_matrix/goe.vo"]),
    # The SigmaRing instance of matrices, characterized by check/MatrixSigmaRing.v
    # (the user's decision of 15 October 2026), against the library at the
    # acceptance commit of check/ApplicationsDefinitions.v.
    ("SnapshotMatrixSigmaRing", "b6173f138f14d97a2587452e99eca14889a78b21",
     [], [], ["check/MatrixSigmaRing.v"], ["library/gaussian/measurable_matrix.vo"]),
    ("SnapshotPhase12Batch2", "0d5afbac072113544fd4c46451a7b6397b7344b3",
     ["GaussianApplications.TensorPackingStatement", "GaussianApplications.SKGapDefinitions",
      "GaussianApplications.SKGapStatement", "GaussianApplications.PerceptronSignDefinitions",
      "GaussianApplications.PerceptronSignStatement",
      "GaussianApplications.SatVarianceDefinitions",
      "GaussianApplications.SatVarianceStatement"], [], [], []),
    ("SnapshotPhase13", "46e45c84b99a50663205933ae501da029dd66098",
     ["GaussianApplications.SatThresholdDefinitions", "GaussianApplications.SatThresholdStatement",
      "GaussianApplications.MinSuperadditiveStatement",
      "GaussianApplications.PsdNormalizationStatement",
      "GaussianApplications.ProductSmoothingStatement",
      "GaussianApplications.PsdRankDefinitions", "GaussianApplications.PsdRankStatement"],
     [], ["check/LibraryStatements.v"],
     ["library/probability/finite_mean.vo", "library/probability/binomial_mean.vo",
      "library/probability/commuting_operators.vo", "library/fourier/boolean_fourier.vo",
      "library/fourier/product_smoothing.vo", "library/matrix/psd_part.vo",
      "library/matrix/psd_factorization.vo", "library/matrix/psd_duality.vo",
      "library/combinatorics/binomial_bounds.vo", "library/matrix/euclidean.vo",
      "library/matrix/real_spectral.vo", "library/matrix/psd_splitting.vo",
      "library/convex/logdet_barrier.vo", "library/convex/moreau.vo"]),
    ("SnapshotPhase13Freeze1", "c0d9cf0b0334b5a94243f1d08fbd3708a860d002",
     [], [], ["check/Phase13Definitions.v"], ["library/probability/finite_mean.vo", "library/probability/binomial_mean.vo",
      "library/probability/commuting_operators.vo", "library/fourier/boolean_fourier.vo",
      "library/fourier/product_smoothing.vo", "library/matrix/psd_part.vo",
      "library/matrix/psd_factorization.vo", "library/matrix/psd_duality.vo",
      "library/combinatorics/binomial_bounds.vo", "library/matrix/euclidean.vo",
      "library/matrix/real_spectral.vo", "library/matrix/psd_splitting.vo",
      "library/convex/logdet_barrier.vo", "library/convex/moreau.vo"]),
    ("SnapshotPhase13Freeze2", "c27c61defbca13535206a13d40dbc5da3e66b1e7",
     [], [], ["check/Phase13Definitions.v"], ["library/probability/finite_mean.vo", "library/probability/binomial_mean.vo",
      "library/probability/commuting_operators.vo", "library/fourier/boolean_fourier.vo",
      "library/fourier/product_smoothing.vo", "library/matrix/psd_part.vo",
      "library/matrix/psd_factorization.vo", "library/matrix/psd_duality.vo",
      "library/combinatorics/binomial_bounds.vo", "library/matrix/euclidean.vo",
      "library/matrix/real_spectral.vo", "library/matrix/psd_splitting.vo",
      "library/convex/logdet_barrier.vo", "library/convex/moreau.vo"]),
    ("SnapshotPhase13Freeze3", "0ec5fcde25b97beac60b9a77b36efed4290179c5",
     [], [], ["check/Phase13Definitions.v"], ["library/probability/finite_mean.vo", "library/probability/binomial_mean.vo",
      "library/probability/commuting_operators.vo", "library/fourier/boolean_fourier.vo",
      "library/fourier/product_smoothing.vo", "library/matrix/psd_part.vo",
      "library/matrix/psd_factorization.vo", "library/matrix/psd_duality.vo",
      "library/combinatorics/binomial_bounds.vo", "library/matrix/euclidean.vo",
      "library/matrix/real_spectral.vo", "library/matrix/psd_splitting.vo",
      "library/convex/logdet_barrier.vo", "library/convex/moreau.vo"]),
]
# The reference of the accepted general statements (the specification, R4
# (iii)): the body of each _statement definition of the inventory, printed at
# the acceptance commit; the definitions do not exist at HEAD, so this
# reference is compared by scripts/check_sources.py with the statements of the
# lemmas of check/LibraryStatements.v, not with a print at HEAD.
ACCEPTED = ("SnapshotAcceptedStatements", "46e45c84b99a50663205933ae501da029dd66098")
# The lemmas of the check files whose statements are snapshotted.
CHECK_LEMMAS = {
    "check/ApplicationsDefinitions.v": [
        "mxdot_characterization", "frobenius_characterization", "opnorm_characterization",
        "psdmx_characterization", "goe_mx_characterization",
        "matrix_measurable_characterization", "gauss_characterization", "gauss_determined"],
    "check/MatrixSigmaRing.v": ["matrix_sigma_ring_characterization"],
    "check/Phase13Definitions.v#1": [
        n + "_characterization" for n in (
            "unif_mean", "unif_var", "binomial_mean", "linear_op", "monotone_op", "meet_avg")],
    "check/Phase13Definitions.v#2": [
        n + "_characterization" for n in (
            "unif_mean", "unif_var", "binomial_mean", "linear_op", "monotone_op", "meet_avg",
            "bdot", "bchar", "blk_deg", "blk_dist", "fcoef", "low_blk_deg", "prob_vec",
            "prod_avg", "smoothing_hyps", "weighted_gram", "psd_factorization")],
    "check/Phase13Definitions.v#3": [
        n + "_characterization" for n in (
            "unif_mean", "unif_var", "binomial_mean", "linear_op", "monotone_op", "meet_avg",
            "bdot", "bchar", "blk_deg", "blk_dist", "fcoef", "low_blk_deg", "prob_vec",
            "prod_avg", "smoothing_hyps", "weighted_gram", "psd_factorization",
            "psd_eval", "psd_eval_cone")],
}


def libst_lemmas():
    text = (ROOT / "check" / "LibraryStatements.v").read_text()
    names = []
    for m in re.finditer(r"^Module (accepted_\w+)\.\n(.*?)^End \1\.", text, re.S | re.M):
        names += [f"{m.group(1)}.{n}" for n in
                  re.findall(r"^Lemma (\w+_accepted) :", m.group(2), re.M)]
    return names


def inventory():
    """The entries of INVENTORY of scripts/check_sources.py: (commit, path,
    name, proposition)."""
    path = ROOT / "scripts" / "check_sources.py"
    module = types.ModuleType("check_sources")
    module.__file__ = str(path)
    # Compiled from its source, never from the bytecode cached in
    # scripts/__pycache__/ (E36).
    exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    return module.INVENTORY


def logical(path):
    """The logical name of a source path."""
    for d, lp in ROOTS:
        if path.startswith(d + "/"):
            return lp + "." + path[len(d) + 1:-2].replace("/", ".")
    raise ValueError(path)


def library_lemmas():
    """The full names of the library lemmas of the 70 accepted statements."""
    return [f"{logical(path)}.{name[:-len('_statement')]}"
            for _, path, name, _ in inventory()]


def write_accepted():
    """The reference of the accepted statements: Print of each _statement
    definition of the inventory, at the acceptance commit."""
    name, commit = ACCEPTED
    entries = inventory()
    modules = sorted({logical(path) for _, path, _, _ in entries})
    lines = [f"(* The bodies of the 70 accepted _statement definitions, printed at",
             f"   {commit[:12]} (scripts/check_sources.py, rule 30 (d)). The definitions",
             "   no longer exist at HEAD: this file is compiled only at the",
             "   acceptance commit, and its output is compared with the statements",
             "   of the lemmas of check/LibraryStatements.v. *)", ""]
    lines += [f"Require {m}." for m in modules]
    lines += ["", "Set Printing All.", "Set Printing Universes.",
              "Set Printing Depth 1000000.", "Set Printing Width 78.", ""]
    lines += [f"Print {logical(path)}.{n}." for _, path, n, _ in entries]
    SNAP.mkdir(exist_ok=True)
    (SNAP / f"{name}.v").write_text("\n".join(lines) + "\n")
    print(f"{name}: check/snapshots/{name}.v written")


def leading_fun_to_forall(text):
    """forall B, body for a text fun B => body (the leading binders of the
    section parameters); other texts unchanged."""
    if not text.startswith("fun "):
        return text
    depth = 0
    for i, c in enumerate(text):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and text.startswith("=>", i):
            return "forall " + text[4:i].strip() + ", " + text[i + 2:].strip()
    return text


def write_conversions():
    """check/snapshots/AcceptedConversions.v: for each accepted statement, two
    definitions whose type is the body of its _statement definition printed
    at the acceptance commit (closed over its section parameters, universe
    annotations removed) and whose bodies are the lemma of
    check/LibraryStatements.v and the library lemma. It compiles at the
    acceptance commit only if both lemmas have types convertible with the
    accepted bodies; the definitions do not exist at HEAD, where the
    statements of both lemmas are compared with their prints at that commit
    (SnapshotPhase13)."""
    name, commit = ACCEPTED
    entries = inventory()
    ref = (SNAP / f"{name}.txt").read_text()
    blocks = re.split(r"\n(?=\S+_statement =)", ref.strip())
    if len(blocks) != len(entries):
        sys.exit(f"{name}: {len(blocks)} printed bodies for {len(entries)} entries")
    modules = sorted({logical(path) for _, path, _, _ in entries})
    lines = ["(* Generated by scripts/snapshot_baselines.py from SnapshotAcceptedStatements.txt;",
             "   compiled only at the acceptance commit 46e45c8. *)", ""]
    lines += [f"Require {m}." for m in modules] + ["Require Checks.LibraryStatements.", ""]
    for k, ((_, path, stmt, _), block) in enumerate(zip(entries, blocks)):
        if not block.split(" =", 1)[0].endswith(stmt):
            sys.exit(f"{name}: the printed body {k} is not that of {stmt}")
        body = re.split(r"\n     : ", block.split(" =", 1)[1], 1)[0]
        body = re.sub(r"@\{[^}]*\}", "", " ".join(body.split()))
        prop = leading_fun_to_forall(body)
        base = stmt[:-len("_statement")]
        module = path.split("/")[-1][:-2]
        lines += [f"Definition conversion_{k} :", f"  {prop} :=",
                  f"  Checks.LibraryStatements.accepted_{module}.{base}_accepted.",
                  f"Definition conversion_library_{k} :", f"  {prop} :=",
                  f"  @{logical(path)}.{base}.", ""]
    (SNAP / "AcceptedConversions.v").write_text("\n".join(lines) + "\n")
    return modules


def module_path(logical):
    for d, lp in ROOTS:
        if logical.startswith(lp + "."):
            return d + "/" + logical[len(lp) + 1:].replace(".", "/")
    raise ValueError(logical)


def run(cmd, cwd=ROOT, **kw):
    kw.setdefault("timeout", 3600)
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, **kw)


def load_paths(base):
    flags = []
    for d, lp in ROOTS:
        if (base / d).is_dir():
            flags += ["-Q", str(base / d), lp]
    return flags + ["-Q", str(base / "checks"), "Checks"]


def base_of(entry):
    """The build directory of an entry: one per commit, shared (the
    reference of the accepted statements uses that of 46e45c8)."""
    return BASE / entry[1][:12]


def archive_sources(commit):
    """Expected source bytes come from git, not a manifest inside the extract."""
    archive = subprocess.run(["git", "archive", commit], cwd=ROOT,
                             capture_output=True, check=True, timeout=120).stdout
    members = {}
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as tar:
        for member in tar.getmembers():
            if member.isdir():
                continue
            path = Path(member.name)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError("unsafe path in the acceptance archive")
            if member.issym():
                members[member.name] = ("symlink", member.linkname)
            elif member.isfile():
                members[member.name] = ("file", hashlib.sha256(tar.extractfile(member).read()).hexdigest())
            else:
                raise ValueError("unsupported entry in the acceptance archive")
    return archive, members


def verify_extract(entry):
    """Refuse stale or changed sources even when a build directory already exists."""
    base = base_of(entry)
    marker = base / PROVENANCE_FILE
    if base.is_symlink() or not marker.is_file() or marker.is_symlink():
        raise ValueError(f"{base}: no verified fresh archive; use a new --baselines directory")
    meta = json.loads(marker.read_text())
    if meta != {"commit": entry[1], "rocq": EXPECTED_ROCQ, "packages": EXPECTED_PACKAGES}:
        raise ValueError(f"{base}: stale archive or toolchain provenance")
    _, members = archive_sources(entry[1])
    for name, (kind, value) in members.items():
        path = base / name
        for ancestor in path.parents:
            if ancestor == base:
                break
            if ancestor.is_symlink():
                raise ValueError(f"{path}: symlinked archive parent")
        if kind == "symlink":
            equal = path.is_symlink() and os.readlink(path) == value
        else:
            equal = path.is_file() and not path.is_symlink() and hashlib.sha256(path.read_bytes()).hexdigest() == value
        if not equal:
            raise ValueError(f"{path}: differs from git archive {entry[1][:12]}")
    return base


def build(entry, jobs):
    name, commit, modules, sections, checks, extra = entry
    base = base_of(entry)
    if commit not in EXTRACTED_THIS_RUN:
        if base.exists() or base.is_symlink():
            sys.exit(f"{base}: refusing to reuse a build; use a new --baselines directory")
        base.mkdir(parents=True)
        archive, _ = archive_sources(commit)
        subprocess.run(["tar", "-x", "-C", str(base)], input=archive, check=True, timeout=120)
        (base / PROVENANCE_FILE).write_text(json.dumps(
            {"commit": commit, "rocq": EXPECTED_ROCQ, "packages": EXPECTED_PACKAGES},
            indent=2, sort_keys=True) + "\n")
        EXTRACTED_THIS_RUN.add(commit)
    verify_extract(entry)
    targets = [module_path(m) + ".vo" for m in modules] \
        + [module_path(m) + ".vo" for m, _ in sections] + extra
    for t in targets:
        if not (base / (t[:-3] + ".v")).exists():
            sys.exit(f"{name}: no source for {t} at {commit[:12]}")
    r = run(["make", "Makefile.rocq", "ROCQ_SWITCH="], cwd=base)
    if r.returncode:
        sys.exit(f"{name}: make Makefile.rocq failed\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    r = run(["make", "-f", "Makefile.rocq", "-j", str(jobs)] + targets, cwd=base)
    if r.returncode:
        sys.exit(f"{name}: the build of {commit[:12]} failed\n{r.stdout[-3000:]}{r.stderr[-3000:]}")
    (base / "checks").mkdir(exist_ok=True)
    for check in checks:
        stem = Path(check).stem
        # The version of the check file at the acceptance commit when it has
        # one (Phase13Definitions.v at each freeze, ApplicationsDefinitions.v
        # at b6173f1); otherwise this tree's (LibraryStatements.v, added at
        # commit P, against the library at 46e45c8).
        source = base / check if (base / check).exists() else ROOT / check
        r = run(["rocq", "compile", "-q", "-noglob"] + WARNINGS + load_paths(base)
                + ["-o", str(base / "checks" / f"{stem}.vo"), str(source)])
        if r.returncode:
            sys.exit(f"{name}: {check} does not compile against {commit[:12]}\n{r.stderr[-3000:]}")
    print(f"{name}: built at {commit[:12]}")


FIELD = ("Definition", "Parameter", "Inductive", "CoInductive", "Variant", "Record",
         "Structure", "Class")


def declarations(base, modules):
    """The declarations of the compiled modules, each in the order of Print
    Module: {module: [(Print or Check, full name)]}. Print Module prints the
    fields after ":= Struct", each starting with its keyword after the end of
    the previous one, on one line for a small module or on several for a
    larger one; the output of each module is read as one text. Every name
    that the .glob of a module defines must be among its fields, and a module
    with no declaration is an error."""
    if not modules:
        return {}
    (base / "checks").mkdir(exist_ok=True)
    query = base / "checks" / "SnapshotQuery.v"
    query.write_text("".join(f"Require {m}.\n" for m in modules)
                     + "".join(f"Print Module {m}.\n" for m in modules))
    r = run(["rocq", "compile", "-q", "-noglob"] + WARNINGS + load_paths(base)
            + ["-o", str(base / "checks" / "SnapshotQuery.vo"), str(query)])
    if r.returncode:
        sys.exit(f"Print Module failed at {base}\n{r.stderr[-2000:]}")
    texts = re.split(r"(?=^Module\b)", r.stdout, flags=re.M)
    texts = [" ".join(t.split()) for t in texts if t.strip()]
    if len(texts) != len(modules):
        sys.exit(f"Print Module at {base}: {len(texts)} outputs for {len(modules)} modules")
    found = {}
    for module, text in zip(modules, texts):
        short = module.split(".")[-1]
        body = re.fullmatch(rf"Module {short} := Struct (.*) End", text)
        if not body:
            sys.exit(f"Print Module {module}: not understood: {text[:200]!r}")
        names = re.findall(r"(?:^|\. )(?:%s) ([^\s:]+)" % "|".join(FIELD), body.group(1))
        if not names:
            sys.exit(f"Print Module {module}: no declaration")
        glob = (base / (module_path(module) + ".glob")).read_text()
        entries = [w for w in (line.split() for line in glob.splitlines())
                   if len(w) >= 4 and w[0] in ("def", "prf", "thm", "lem", "ind", "rec")]
        missing = [w[-1] for w in entries if w[-1] not in names]
        if missing:
            sys.exit(f"Print Module {module}: the .glob defines {missing}, which it does not list")
        proofs = {w[-1] for w in entries if w[0] in ("prf", "thm", "lem")}
        found[module] = [("Check" if n in proofs else "Print", f"{module}.{n}") for n in names]
    return found


def section_declarations(base, module, section):
    """The declarations of a pinned section, from the .glob of its module at
    the baseline: those whose position lies between Section and End."""
    source = (base / (module_path(module) + ".v")).read_bytes()
    starts = [m.start() for m in re.finditer(rb"(?m)^Section %s\." % section.encode(), source)]
    ends = [m.end() for m in re.finditer(rb"(?m)^End %s\." % section.encode(), source)]
    if len(starts) != 1 or len(ends) != 1:
        sys.exit(f"{module}: the section {section} is not found exactly once")
    glob = (base / (module_path(module) + ".glob")).read_text()
    found = []
    for w in (line.split() for line in glob.splitlines()):
        if len(w) >= 4 and w[0] in ("def", "prf", "thm", "lem", "ind", "rec"):
            begin = int(w[1].split(":")[0])
            if starts[0] <= begin < ends[0]:
                found.append(("Check" if w[0] in ("prf", "thm", "lem") else "Print",
                              f"{module}.{w[-1]}"))
    if not found:
        sys.exit(f"{module}: no declaration of the section {section} in its .glob")
    return found


def write_file(entry):
    name, commit, modules, sections, checks, _ = entry
    base = base_of(entry)
    lines = [f"(* The statement snapshot {name} (scripts/check_sources.py, rule 30):",
             f"   the declarations accepted at {commit[:12]}, printed in full. Written",
             "   by scripts/snapshot_baselines.py; its reference, the output at that",
             "   commit, is check/snapshots/" + name + ".txt. *)", ""]
    if name == "SnapshotMatrixSigmaRing":
        lines = [f"(* The statement snapshot {name} (scripts/check_sources.py, rule 30):",
                 "   the characterization of check/MatrixSigmaRing.v, accepted on 15",
                 f"   October 2026, printed in full against the library at {commit[:12]}.",
                 "   Written by scripts/snapshot_baselines.py; its reference, the output",
                 "   at that commit, is check/snapshots/" + name + ".txt. *)", ""]
    for m in modules + [m for m, _ in sections]:
        lines.append(f"Require {m}.")
    for c in checks:
        lines.append(f"Require Checks.{Path(c).stem}.")
    lines += ["", "Set Printing All.", "Set Printing Universes.",
              "Set Printing Depth 1000000.", "Set Printing Width 78.", ""]
    found = declarations(base, modules)
    for m in modules:
        lines.append(f"Print Module {m}.")
        for kind, full in found[m]:
            lines.append(f"{kind} {full}.")
    for m, s in sections:
        for kind, full in section_declarations(base, m, s):
            lines.append(f"{kind} {full}.")
    for c in checks:
        stem = Path(c).stem
        if stem == "LibraryStatements":
            lemmas = libst_lemmas()
        elif stem == "Phase13Definitions":
            lemmas = CHECK_LEMMAS[f"{c}#{name[-1]}"]
        else:
            lemmas = CHECK_LEMMAS[c]
        for lemma in lemmas:
            lines.append(f"Check Checks.{stem}.{lemma}.")
    if name == "SnapshotPhase13":
        # The statements of the library lemmas that replace the accepted
        # _statement definitions.
        for full in library_lemmas():
            lines.append(f"Check @{full}.")
    SNAP.mkdir(exist_ok=True)
    (SNAP / f"{name}.v").write_text("\n".join(lines) + "\n")
    print(f"{name}: check/snapshots/{name}.v written")


PROJECT_ROOTS = ("GaussianAnalysis.", "EllipsoidFitting.", "EllipsoidUniversality.",
                 "GaussianApplications.", "Checks.")
QUALIFIED = re.compile(r"(?<![\w'.])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+)")


def project_names(entry, output):
    """The project objects that the output names: {printed name: full name},
    resolved by Locate in the environment of the snapshot file at its
    baseline (the printed names are the shortest unambiguous ones, which
    the name of a module alone does not determine)."""
    name = entry[0]
    base = base_of(entry)
    text = re.sub(r"@\{[^}]*\}", "", output)
    printed = sorted(set(QUALIFIED.findall(text)))
    source = (SNAP / f"{name}.v").read_text()
    head = source[:source.index("Set Printing All.")]
    query = base / "checks" / "SnapshotLocate.v"
    # Each Locate is followed by Check I, whose output separates the answers.
    query.write_text(head + "".join(f"Locate {p}.\nCheck I.\n" for p in printed))
    r = run(["rocq", "compile", "-q", "-noglob"] + WARNINGS + load_paths(base)
            + ["-o", str(base / "checks" / "SnapshotLocate.vo"), str(query)])
    if r.returncode:
        sys.exit(f"{name}: Locate failed at its baseline\n{r.stderr[-2000:]}")
    answers = re.split(r"^I\n     : True\n?", r.stdout, flags=re.M)
    if len(answers) != len(printed) + 1:
        sys.exit(f"{name}: {len(answers) - 1} answers of Locate for {len(printed)} names")
    found = {}
    for p, answer in zip(printed, answers):
        lines = answer.strip().split("\n")
        # A long name is printed on the line after its keyword.
        first = " ".join(lines[:2]) if lines and lines[0] in (
            "Constant", "Inductive", "Constructor", "Projection") else lines[0]
        m = re.match(r"(?:Constant|Inductive|Constructor|Projection)\s+(\S+)", first)
        if m and m.group(1).startswith(PROJECT_ROOTS):
            found[p] = m.group(1)
    return found


def toolchain():
    """The version line of rocq and the versions of the installed packages."""
    lines = run(["rocq", "--version"], check=True).stdout.splitlines()
    if not lines:
        raise ValueError("rocq --version produced no version line")
    version = lines[0]
    where = run(["rocq", "-where"], check=True).stdout.strip()
    if not where:
        raise ValueError("rocq -where produced no library path")
    packages = Path(where).resolve().parent.parent / ".opam-switch" / "packages"
    found = {}
    for package in ["rocq-core", "rocq-mathcomp-ssreflect", "rocq-mathcomp-analysis"]:
        names = sorted(p.name for p in packages.glob(package + ".*")) if packages.is_dir() else []
        found[package] = names[0][len(package) + 1:] if len(names) == 1 else None
    return version, found


def output_at_baseline(entry):
    name = entry[0]
    base = base_of(entry)
    (base / "checks").mkdir(exist_ok=True)
    r = run(["rocq", "compile", "-q", "-noglob"] + WARNINGS + load_paths(base)
            + ["-o", str(base / "checks" / f"{name}.vo"), f"check/snapshots/{name}.v"])
    if r.returncode:
        sys.exit(f"{name}: the snapshot does not compile at its baseline\n{r.stderr[-3000:]}")
    return r.stdout


def identity_inventory():
    texts = {p.stem: p.read_text() for p in sorted(SNAP.glob("Snapshot*.v"))}
    return identity_sidecars.inventory(texts)


def write_identity_files():
    inv = identity_inventory()
    IDENTITY.mkdir(exist_ok=True)
    (IDENTITY / "inventory.json").write_text(identity_sidecars.inventory_text(inv))
    for name, entry in inv["snapshots"].items():
        (IDENTITY / f"Identity{name}.v").write_text(identity_sidecars.driver_text(name, entry))
    queries = sum(len(e["queries"]) for e in inv["snapshots"].values())
    print(f"identity-files: {len(inv['snapshots'])} drivers, {queries} queries")


def identity_at_baseline(entry, findlib, queries):
    """The sidecar of the identity driver of entry, compiled against the
    build of its acceptance commit."""
    name = entry[0]
    base = base_of(entry)
    (base / "checks").mkdir(exist_ok=True)
    r = run(["rocq", "compile", "-q", "-noglob"] + WARNINGS + load_paths(base)
            + ["-o", str(base / "checks" / f"Identity{name}.vo"),
               str(IDENTITY / f"Identity{name}.v")],
            env=identity_sidecars.driver_environment(findlib))
    if r.returncode or r.stderr:
        sys.exit(f"{name}: the identity driver does not compile cleanly at its "
                 f"baseline\n{r.stderr[-3000:]}")
    try:
        return identity_sidecars.sidecar_bytes(name, r.stdout, queries)
    except ValueError as error:
        sys.exit(f"{name}: the identity export at its baseline is not framed: {error}")


def identities(names, write):
    inv = json.loads((IDENTITY / "inventory.json").read_text())
    if inv != identity_inventory():
        sys.exit("check/identity/inventory.json differs from the snapshot files; run "
                 "identity-files")
    plugin = BASE / "identity-plugin"
    if plugin.exists() or plugin.is_symlink():
        sys.exit(f"{plugin}: refusing to reuse an exporter build")
    try:
        findlib = identity_sidecars.build_plugin(IDENTITY, plugin, 3600)
        ocaml = identity_sidecars.ocaml_toolchain(3600)
    except ValueError as error:
        sys.exit(f"the exporter of check/identity/ does not build: {error}")
    exporter = {name: hashlib.sha256((IDENTITY / name).read_bytes()).hexdigest()
                for name in identity_sidecars.PLUGIN_SOURCES + ("META",)}
    exporter["recipe_sha256"] = identity_sidecars.recipe_sha256()
    exporter["plugin_sha256"] = hashlib.sha256(
        (findlib / "kernel_identity" / "kernel_identity.cmxs").read_bytes()).hexdigest()
    exporter.update(ocaml)
    meta_path = IDENTITY / "REFERENCES.json"
    meta = json.loads(meta_path.read_text()) if meta_path.exists() else {}
    bad = 0
    for entry in BASELINES:
        name = entry[0]
        if name not in inv["snapshots"] or (names and name not in names):
            continue
        verify_extract(entry)
        out = identity_at_baseline(entry, findlib, inv["snapshots"][name]["queries"])
        ref = IDENTITY / f"Identity{name}.json"
        if write:
            ref.write_bytes(out)
            version, packages = toolchain()
            meta[name] = {"commit": entry[1], "rocq": version, "packages": packages,
                          "exporter": exporter,
                          "sha256": hashlib.sha256(out).hexdigest()}
            print(f"{name}: identity reference written, {len(out)} bytes")
        elif not ref.exists() or ref.read_bytes() != out:
            bad += 1
            print(f"{name}: the identities at the baseline differ from {ref}")
            if ref.exists():
                for line in identity_sidecars.first_differences(ref.read_bytes(), out):
                    print("    " + line)
        else:
            print(f"{name}: identities equal to their reference")
    if write:
        meta_path.write_text(json.dumps(meta, indent=1, sort_keys=True) + "\n")
    return bad


def main():
    global BASE
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", choices=["build", "files", "references", "verify",
                                            "conversions", "identity-files", "identities",
                                            "identities-verify"])
    parser.add_argument("names", nargs="*")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--baselines", type=Path, default=BASE)
    args = parser.parse_intermixed_args()
    BASE = args.baselines.resolve()
    banned = [name for name in BANNED_ENVIRONMENT if name in os.environ]
    banned += sorted(v for v in os.environ
                     if v.startswith(("OCAML", "CAML")) and v not in banned)
    if banned:
        sys.exit("snapshot_baselines.py: unset " + ", ".join(banned))
    try:
        version, packages = toolchain()
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        sys.exit(f"snapshot_baselines.py: cannot verify toolchain: {error}")
    if version != EXPECTED_ROCQ or packages != EXPECTED_PACKAGES:
        sys.exit("snapshot_baselines.py: the installed toolchain is not the pinned one")
    accepted = (ACCEPTED[0], ACCEPTED[1], [], [], [], [])
    if args.command == "identity-files":
        write_identity_files()
        return
    if args.command in ("identities", "identities-verify"):
        sys.exit(1 if identities(args.names, args.command == "identities") else 0)
    if args.command == "conversions":
        verify_extract(accepted)
        write_conversions()
        base = base_of(accepted)
        r = run(["rocq", "compile", "-q", "-noglob"] + WARNINGS + load_paths(base)
                + ["-o", str(base / "checks" / "AcceptedConversions.vo"),
                   str(SNAP / "AcceptedConversions.v")])
        print("AcceptedConversions.v:", "compiled at " + ACCEPTED[1][:12] if r.returncode == 0
              else "FAILED\n" + r.stderr[-3000:])
        sys.exit(r.returncode)
    entries = [e for e in BASELINES + [accepted] if not args.names or e[0] in args.names]
    bad, meta = 0, {}
    meta_path = SNAP / "REFERENCES.json"
    if meta_path.exists():
        meta = json.loads(meta_path.read_text())
    for entry in entries:
        if args.command != "build":
            verify_extract(entry)
        if args.command == "build":
            if entry[0] == ACCEPTED[0]:
                continue
            build(entry, args.jobs)
        elif args.command == "files":
            if entry[0] == ACCEPTED[0]:
                write_accepted()
            else:
                write_file(entry)
        else:
            out = output_at_baseline(entry)
            ref = SNAP / f"{entry[0]}.txt"
            if args.command == "references":
                ref.write_text(out)
                version, packages = toolchain()
                meta[entry[0]] = {"commit": entry[1], "rocq": version, "packages": packages,
                                  "sha256": hashlib.sha256(out.encode()).hexdigest(),
                                  "project_names": project_names(entry, out)}
                print(f"{entry[0]}: reference written, {len(out)} bytes")
            elif not ref.exists() or ref.read_text() != out:
                bad += 1
                print(f"{entry[0]}: the output at the baseline differs from {ref}")
            else:
                print(f"{entry[0]}: equal to its reference")
    if args.command == "references":
        meta_path.write_text(json.dumps(meta, indent=1, sort_keys=True) + "\n")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
