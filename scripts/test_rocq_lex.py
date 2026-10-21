#!/usr/bin/env python3
"""Differential tests of scripts/rocq_lex.py against Rocq.

    python3 -I -B scripts/test_rocq_lex.py [--jobs N] [--random N] [--seed S]

Run it where rocq is the pinned toolchain (in the container on the VM, or in
the opam switch). It requires Rocq 9.1.1 and checks every unmodified source
base and its probes before running mutations. Scratch files, including
tactic caches, stay under build/lexer-tests/. It prints one line per case,
then a summary; it exits 0 only if every case agrees.

The property tested is the one the checker relies on: two texts that the
lexer gives the same code are read alike by Rocq. For a text A that the
lexer reads, the test first compiles A and code(A), the lexer's normalized
text, alone. Separate probes load each compiled file: short module printing
enumerates its kernel fields recursively, including Unicode identifiers and
definitions introduced by Include. Rich Print Module and Print commands then
observe every module and declaration, with Printing All and Universes enabled.
Probe names come from both texts. The source compilations must both fail, or
both succeed with the same inventories and observations. A failed probe or
an unsupported module form is an error, never an agreement. Every expected
reading comes from the lexer and Rocq; none is written by hand.

The lexer raises LexError on an unterminated comment or string, on three
forms that Rocq reads by the keywords in scope (a (* or a double quote glued
to the token before it, and the quotations :{{ and lp:), which it refuses
rather than guess, and on a *) in a string inside a comment, on which Rocq
warns (comment-terminator-in-string, a warning the build makes an error). For an unterminated comment or string, Rocq must fail too.
Any other refused form is outside the lexer's domain: the checker fails on
any text that holds one, so Rocq's reading of it does not matter; the test
records what Rocq does, for information.

The cases come from a fixed corpus (CORPUS: nested comments, strings in code
and in comments, doubled quotes in both directions, (*), the delimiters
inside strings, *) in code, a comment inside a token and after a symbol,
strings next to identifiers, U+00A0 and the other characters that Python
treats as blanks, form feed, carriage returns, unterminated comments and
strings, modules and an interior U+FEFF, and the exploits E1 to E6, each also
shown to fool its corresponding old pin or scan)
and from random insertions (--random, default 1000): comments built from
strings, doubled quotes, nested comments and comment delimiters inside
strings, inserted at blanks of small synthetic files and of copies of frozen
and code-fixed files."""

import argparse
import random
import re
import shutil
import subprocess
import sys
import types
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def load(name, path):
    """A module of scripts/, compiled from its source, never from the
    bytecode cached in scripts/__pycache__/ (E32)."""
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(Path(path).read_bytes(), str(path), "exec"), module.__dict__)
    return module


lex = load("rocq_lex", ROOT / "scripts" / "rocq_lex.py")
old = load("export_from_ellipsoid_rocq", ROOT / "scripts" / "export_from_ellipsoid_rocq.py")
WORK = ROOT / "build" / "lexer-tests"
PINNED_VERSION = "9.1.1"
ROCQ = "rocq"
LOADPATHS = [arg for directory, logical in
             [("library", "GaussianAnalysis"), ("theories", "EllipsoidFitting"),
              ("extension", "EllipsoidUniversality"), ("applications", "GaussianApplications")]
             for arg in ("-Q", str(ROOT / directory), logical)]
COMPILE_FLAGS = ["-q", "-noglob", "-w", "-notation-overridden", "-w", "-ambiguous-paths",
                 "-w", "-notation-incompatible-prefix", "-w", "-hiding-delimiting-key",
                 "-w", "+comment-terminator-in-string"]
PROBE_HEAD = ("\nSet Printing All.\nSet Printing Universes.\nSet Printing Depth 1000000.\n"
              "Set Printing Width 78.\nPrint All.\n")


class ProbeError(RuntimeError):
    """Test infrastructure failed; this is never a both-fail agreement."""


def check_toolchain():
    """Use exactly the executable whose version was checked for every probe."""
    global ROCQ
    executable = shutil.which("rocq")
    if executable is None:
        raise ProbeError("rocq is not on PATH; use the pinned Rocq 9.1.1 toolchain")
    executable = str(Path(executable).resolve())
    result = subprocess.run([executable, "--version"], capture_output=True,
                            text=True, timeout=30)
    lines = result.stdout.splitlines()
    version = re.fullmatch(r"The Rocq Prover, version ([^ ]+)", lines[0]) if lines else None
    if result.returncode or version is None or version.group(1) != PINNED_VERSION:
        detail = (result.stdout + result.stderr).strip()
        raise ProbeError(f"expected Rocq {PINNED_VERSION}, got {executable}: {detail}")
    ROCQ = executable
    print(f"toolchain: {ROCQ}: {lines[0]}", flush=True)


def old_code(text):
    return " ".join(old.strip_comments(text).split())


# The scans of the checker before the repair (scripts/check_sources.py at
# commit P, verbatim), for the exploits E3 and E4.
OLD_ASSUMPTION = re.compile(
    r"(?:\A|(?<=\.))\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+)?"
    r"(Admitted\s*\.|Axioms?\b|Parameters?\b|Conjecture\b)")
OLD_REQUIRE = re.compile(r"(?:From\s+([\w.]+)\s+)?Require(?:\s+(?:Import|Export))?\s+"
                         r"([^.]+(?:\.[A-Za-z]\w*)*)\s*\.", re.S)


def old_section_code(text, name):
    stripped = old.strip_comments(text)
    requires = " ".join(m.group(0) for m in OLD_REQUIRE.finditer(stripped))
    section = re.search(rf"Section {name}\..*?End {name}\.", stripped, re.S)
    return " ".join(requires.split()), " ".join(section.group(0).split()) if section else None


def old_scan(text):
    stripped = old.strip_comments(text)
    return ([m.group(1).strip() for m in OLD_ASSUMPTION.finditer(stripped)],
            [m.group(2) for m in OLD_REQUIRE.finditer(stripped)])


def rocq(directory, text, timeout=600, module="LexCase"):
    """Compile a fixture or its separate probe; (status, stdout)."""
    directory.mkdir(parents=True, exist_ok=True)
    source = directory / f"{module}.v"
    with open(source, "w", encoding="utf-8", newline="") as out:
        out.write(text)
    r = subprocess.run([ROCQ, "compile"] + COMPILE_FLAGS + LOADPATHS
                       + ["-Q", str(directory), "", "-o", str(directory / f"{module}.vo"), str(source)],
                       cwd=directory, capture_output=True, timeout=timeout)
    (directory / f"{module}.stdout").write_bytes(r.stdout)
    (directory / f"{module}.stderr").write_bytes(r.stderr)
    if r.returncode < 0:
        raise ProbeError(f"Rocq terminated by signal {-r.returncode}: {source}")
    return r.returncode, r.stdout.decode("utf-8")


def checked_probe(directory, commands, module="LexProbe"):
    """A probe failure after successful source compilation invalidates the test."""
    status, output = rocq(directory, "Require LexCase.\n" + PROBE_HEAD + commands,
                          module=module)
    if status:
        diagnostic = lex.read_source(directory / f"{module}.stderr").strip()
        raise ProbeError(f"probe failed after source compiled: {directory}: {diagnostic}")
    return output


def module_fields(output, name):
    """Read Rocq's short module listing, not source text or the tested lexer.

    Short listings enumerate kernel fields without their types or bodies.
    Only ASCII blanks separate names: U+00A0 may occur inside an identifier.
    Functors, abstract signatures and unknown listing forms fail closed;
    their members cannot in general be addressed by qualified Print commands.
    """
    words = re.findall(r"[^ \t\r\n]+", output)
    if words[:2] != ["Module", name]:
        raise ProbeError(f"unrecognized module listing for {name}: {output}")
    if words[2:4] in ([":=", "Functor"], [":", "Functor"]):
        raise ProbeError(f"cannot probe unapplied functor members: {name}")
    if words[2:4] == [":=", "Struct"] or words[2:4] == [":", "Sig"]:
        start = 4
    else:
        raise ProbeError(f"cannot enumerate abstract module signature: {name}: {output}")
    constants, modules = [], []
    i = start
    while i < len(words) and words[i] != "End":
        kind = words[i]
        if i + 1 >= len(words):
            raise ProbeError(f"truncated module listing for {name}")
        child = words[i + 1]
        if kind == "Module" and child == "Type":
            raise ProbeError(f"cannot probe module-type members: {name}")
        if kind == "Module":
            modules.append(f"{name}.{child}")
        elif kind in {"Definition", "Parameter", "Theorem", "Inductive", "CoInductive", "Variant"}:
            constants.append(f"{name}.{child}")
        else:
            raise ProbeError(f"unknown module field {kind!r} in {name}")
        i += 2
    if i >= len(words):
        raise ProbeError(f"unterminated module listing for {name}")
    # A concrete alias can follow the signature. Its target is also printed
    # by the rich comparison probe; there are no more fields after End.
    if words[i + 1:] and not (len(words[i + 1:]) == 2 and words[i + 1] == ":="):
        raise ProbeError(f"unknown module suffix for {name}: {words[i + 1:]}")
    return constants, modules


def declarations(directory):
    """Discover all concrete module fields, including Include-generated ones."""
    pending, modules, constants = ["LexCase"], [], []
    while pending:
        name = pending.pop(0)
        if name in modules:
            raise ProbeError(f"repeated module in probe discovery: {name}")
        output = checked_probe(directory, f"Set Short Module Printing.\nPrint Module {name}.\n",
                               module=f"LexDiscover{len(modules)}")
        # Print All in the probe's own empty module produces no declarations.
        found, children = module_fields(output, name)
        modules.append(name)
        constants.extend(found)
        pending.extend(children)
    return tuple(modules), tuple(constants)


def prepare(directory, text):
    status, output = rocq(directory, text)
    inventory = declarations(directory) if status == 0 else ((), ())
    observed = ""
    if status == 0:
        modules, constants = inventory
        probe = "Unset Short Module Printing.\n" \
            + "".join(f"Print Module {n}.\n" for n in sorted(set(modules))) \
            + "".join(f"Print {n}.\n" for n in sorted(set(constants)))
        observed = checked_probe(directory, probe)
    return status, output, inventory, observed


def compare_prepared(a, b):
    """Compare source failures or complete successful observations separately."""
    status_a, out_a, inventory_a, observed_a = a
    status_b, out_b, inventory_b, observed_b = b
    if status_a or status_b:
        same = bool(status_a and status_b)
        return same, "both fail" if same else (
            f"text {'fails' if status_a else 'compiles'}, code {'fails' if status_b else 'compiles'}")
    # Differing inventories already prove a semantic difference; never issue
    # Print for a name absent on one side and misclassify its failure.
    if inventory_a != inventory_b:
        return False, "declaration inventories differ"
    # The equal inventories are the union of names from both sides. prepare
    # already printed each leaf and module, so cached probes stay read-only.
    same = out_a == out_b and observed_a == observed_b
    return same, "same output" if same else "declaration outputs differ"


class Case:
    def __init__(self, name, text, note=""):
        self.name, self.text, self.note = name, text, note


def run_case(case, cache):
    """The outcome of one case: (agrees, line)."""
    base = WORK / re.sub(r"\W", "_", case.name)
    try:
        normalized = lex.code(case.text)
    except lex.LexError as err:
        status, _ = rocq(base / "a", case.text)
        if err.reason in (lex.UNTERMINATED_COMMENT, lex.UNTERMINATED_STRING):
            ok = status != 0
            return ok, (f"{'agree' if ok else 'DIFFER'} {case.name}: lexer {err}; "
                        f"Rocq {'fails' if status else 'compiles'}")
        if err.reason not in {lex.GLUED_COMMENT, lex.GLUED_STRING, lex.QUOTATION,
                              lex.TERMINATOR_IN_STRING, lex.INVALID_UTF8}:
            raise ProbeError(f"unexpected lexer refusal in {case.name}: {err}")
        return True, (f"refused {case.name}: lexer {err}; Rocq "
                      f"{'fails' if status else 'compiles'} (outside the lexer's domain)")
    # Both sources compile before observation probes run. A failed generated
    # probe is an infrastructure failure, never an ordinary both-fail case.
    key = normalized
    if key not in cache:
        cache[key] = prepare(base / "b", normalized)
    same, what = compare_prepared(prepare(base / "a", case.text), cache[key])
    return same, f"{'agree' if same else 'DIFFER'} {case.name}: {what}{case.note}"


NBSP = " "
PY_BLANKS = [chr(c) for c in range(0x110000) if chr(c).isspace()]
OTHER_BLANKS = [c for c in PY_BLANKS if c not in " \t\n\r"]


STRINGS = "From Stdlib Require Import String.\nOpen Scope string_scope.\n"


def corpus():
    c = []
    add = lambda name, text, note="": c.append(Case(name, text, note))  # noqa: E731
    add("plain", "Definition p0 := 1.\nDefinition p1 := p0 + 1.\n")
    add("nested-comments", "Definition p0 := 1.\n(* a (* b (* c *) d *) e *)\nDefinition p1 := 2.\n")
    add("nested-unclosed", "Definition p0 := 1.\n(* a (* b *)\nDefinition p1 := 2.\n")
    add("string-in-code", STRINGS + 'Definition p0 := "a (* b *) c".\nDefinition p1 := 1.\n')
    add("string-open-comment-in-code", STRINGS + 'Definition p0 := "(*".\nDefinition p1 := 1.\nDefinition p2 := "*)".\n')
    add("string-in-comment", 'Definition p0 := 1.\n(* "a *) b" *)\nDefinition p1 := 2.\n')
    add("open-delimiter-in-comment-string", 'Definition p0 := 1.\n(* "(*" *)\nDefinition p1 := 2.\n')
    add("balanced-delimiters-in-comment-string", 'Definition p0 := 1.\n(* "(* *)" *)\nDefinition p1 := 2.\n')
    add("nested-delimiters-in-comment-string", 'Definition p0 := 1.\n(* outer (* "(* *)" *) "(* (* *) *)" *)\nDefinition p1 := 2.\n')
    add("string-in-comment-hides", 'Definition p0 := 1.\n(* " *)\nDefinition p1 := 2.\n(* " *)\nDefinition p2 := 3.\n')
    add("doubled-quote-keeps-open", 'Definition p0 := 1.\n(* "a "" *) b" *)\nDefinition p1 := 2.\n')
    add("doubled-quote-lets-close", 'Definition p0 := 1.\n(* "a""" *)\nDefinition p1 := 2.\n')
    add("doubled-quote-in-code", STRINGS + 'Definition p0 := "a""b".\nDefinition p1 := """".\n')
    add("comment-paren-star-paren", "Definition p0 := 1.\n(*) still a comment *)\nDefinition p1 := 2.\n")
    add("close-in-code", "Notation \"x *) y\" := (x + y) (at level 50).\nDefinition p0 := 1 *) 2.\n")
    add("comment-in-token", "Definition ab := 1.\nDefinition a (n : nat) := n + 100.\nDefinition b := 11.\nDefinition p0 := a(*x*)b.\n")
    add("comment-after-dot-number", "Definition p0 := 1.\nDefinition p1 := (1).(* c *)\n")
    add("comment-after-dot-number-exact", "Definition p0 := 1.(* c *)\n")
    add("comment-after-quote-symbol", "Definition p0 := 1.\nDefinition p1 := p0 '(* c *).\n")
    add("comment-after-period-blank", "Definition p0 := 1. (* c *)\nDefinition p1 := 2.\n")
    add("string-next-to-ident", STRINGS + 'Definition p0 := 1.\nDefinition p1 := p0"x".\n')
    add("string-after-blank", STRINGS + 'Definition p0 := 1.\nDefinition p2 := "x".\nDefinition p1 := 2.\n')
    add("nbsp-in-ident", f"Definition a{NBSP}b := 1.\nDefinition p0 := a{NBSP}b.\n")
    add("nbsp-after-ident", f"Definition psd (n : nat) := n = 0.\nDefinition psd{NBSP} (n : nat) := True.\n"
        f"Definition p0 := forall n, psd{NBSP} (n * 0).\n")
    for k, ch in enumerate(OTHER_BLANKS):
        add(f"python-blank-U+{ord(ch):04X}", f"Definition p0{ch}:= 1.\n")
    add("form-feed", "Definition p0 := 1.\fDefinition p1 := 2.\n")
    add("crlf", "Definition p0 := 1.\r\nDefinition p1 := 2.\r\n")
    add("cr-in-string", STRINGS + 'Definition p0 := "a\r\nb".\nDefinition p1 := "a\nb".\n')
    add("cr-only", "Definition p0 := 1.\rDefinition p1 := 2.\r")
    add("tabs", "Definition\tp0\t:=\t1.\n\tDefinition p1 := p0 + 1.\n")
    add("unterminated-comment", "Definition p0 := 1.\n(* open\nDefinition p1 := 2.\n")
    add("unterminated-string", 'Definition p0 := "open.\nDefinition p1 := 2.\n')
    add("unterminated-string-in-comment", 'Definition p0 := 1.\n(* " *)\nDefinition p1 := 2.\n')
    add("bom-start", "﻿Definition p0 := 1.\n")
    add("bom-after-definition", "Definition p0 := 1.\n\ufeffDefinition p1 := 2.\n")
    add("module", "Module M.\nDefinition q := 1.\nEnd M.\nDefinition p0 := M.q.\n")
    add("nested-module", f"Module M.\nModule N.\nDefinition a{NBSP}b := 1.\n"
        f"End N.\nEnd M.\nDefinition p0 := M.N.a{NBSP}b.\n")
    add("module-include", "Module M. Definition q := 1. End M.\nInclude M.\n")
    add("module-alias", "Module M. Definition q := 1. End M.\nModule N := M.\n")
    add("module-keyword-identifier", "Module M. Definition Functor := 1. End M.\n")
    add("module-comment-string-hides", 'Module M.\n(* " *)\nDefinition q := 1.\n'
        '(* " *)\nEnd M.\nDefinition p0 := 1.\n')
    return c


def exploits():
    """E1 to E6 in their reported placements: (name, original, mutated, the
    text compiled for the differential case, the old function that each
    fooled). The old function gives both the same value; the new lexer
    refuses the mutated text, or reads it as Rocq does."""
    c = []
    sat = lex.read_source(ROOT / "applications" / "SatThresholdStatement.v")
    # Keep the second comment in an existing whitespace gap. This preserves
    # old_code equality while testing comment strings, not the glued-token rule.
    e1 = sat.replace("exists alpha : R, 0 < alpha /\\", 'exists alpha : R, 0 < alpha (* " *) /\\', 1) \
            .replace("--> (0 : R)).", '--> (0 : (* " *) R)).', 1)
    c.append(("E1", sat, e1, e1, "code()", old_code))
    p13 = lex.read_source(ROOT / "check" / "Phase13Definitions.v")
    e2 = p13.replace("(* Freeze 2,", '(* " *)\n(* Freeze 2,', 1) + '(* " *)\n'
    c.append(("E2", p13, e2, e2, "code()", old_code))
    lm = lex.read_source(ROOT / "library" / "matrix" / "lambda_max.v")
    a = lm.index("Section lambda_max.")
    b = lm.index("End lambda_max.") + len("End lambda_max.\n")
    sec = lm[a:b]
    new = sec.replace("mxdot x x = 1", "mxdot x x <= 1")
    e3 = lm[:a] + '(* " *)\n' + sec + '(* " *)\n' + new
    c.append(("E3", lm, e3 + lm[b:], e3, "section_code (the pin of lambda_max)",
              lambda t: old_section_code(t, "lambda_max")))
    inv = lex.read_source(ROOT / "library" / "fourier" / "inversion.v")
    e4 = inv + ('\nFail Check "(*".\nAxiom hidden_axiom : False.\n'
                'Lemma hidden_admitted : False. Admitted.\n'
                'From Stdlib Require Import Reals.\nFail Check "*)".\n')
    c.append(("E4", inv, e4, e4, "the scans of rules 2 and 3", old_scan))
    psd = lex.read_source(ROOT / "applications" / "PsdNormalizationStatement.v")
    e5 = psd.replace("forall i, psdmx (F' i)", f"forall i, psdmx{NBSP} (F' i)", 1)
    c.append(("E5", psd, e5, e5, "code()", old_code))
    sd = lex.read_source(ROOT / "applications" / "SatThresholdDefinitions.v")
    e6 = sd.replace("Definition sat_prob", "Definition sat(*x*)_prob", 1)
    c.append(("E6", sd, e6, e6, "code()", old_code))
    return c


ATOMS = ['"', '""', "(*", "*)", " ", "\n", "a", "x", "'", ".", "(", ")", "*", "{", "}"]


def random_comment(rng):
    body = "".join(rng.choice(ATOMS) for _ in range(rng.randint(0, 12)))
    return "(*" + body + "*)"


SYNTHETIC = [
    "Definition p0 := 1.\nDefinition p1 (n : nat) := n + p0.\nDefinition p2 := p1 2.\n",
    'From Stdlib Require Import String.\nOpen Scope string_scope.\n'
    'Definition p0 := "s".\nDefinition p1 := (1, 2).\nDefinition p2 := fun x : nat => x.\n',
    "Section S.\nVariable x : nat.\nDefinition p0 := x + 1.\nEnd S.\nDefinition p1 := p0 3.\n",
    "Module M.\nDefinition q := 1.\nModule N.\nDefinition r := q + 1.\n"
    "End N.\nEnd M.\nDefinition p0 := M.N.r.\n",
]

FROZEN_BASES = ["applications/MinSuperadditiveStatement.v", "applications/SatThresholdStatement.v",
                "check/Phase13Definitions.v", "theories/MainStatement.v"]


def source_bases():
    return [(f"syn{k}", text) for k, text in enumerate(SYNTHETIC)] + [
        (path.replace("/", "_"), lex.read_source(ROOT / path)) for path in FROZEN_BASES]


def preflight(bases, cache):
    """Every original input and its full probe must work before any mutation."""
    seen = set()
    for name, text in bases:
        if text in seen:
            continue
        seen.add(text)
        directory = WORK / "preflight" / re.sub(r"\W", "_", name)
        normalized = lex.code(text)
        a = prepare(directory / "a", text)
        b = prepare(directory / "b", normalized)
        for label, result in (("a", a), ("b", b)):
            if result[0]:
                diagnostic = lex.read_source(directory / label / "LexCase.stderr").strip()
                raise ProbeError(f"unmodified base/probe does not compile: {name}/{label}: {diagnostic}")
        same, what = compare_prepared(a, b)
        if not same:
            raise ProbeError(f"unmodified base differs from its normalized text: {name}: {what}")
        cache[normalized] = b
        print(f"preflight {name}: source, normalized source and recursive probes compile", flush=True)
    print(f"preflight: {len(seen)} distinct bases passed", flush=True)


def random_cases(n, rng):
    """n insertions: most in the small synthetic files, some in copies of
    frozen and code-fixed files, at blanks."""
    bases = source_bases()
    cases = []
    for k in range(n):
        name, text = bases[k % len(SYNTHETIC)] if k % 10 else bases[len(SYNTHETIC) + (k // 10) % len(FROZEN_BASES)]
        blanks = [m.start() for m in re.finditer(r"[ \t\r\n]", text)]
        i = rng.choice(blanks)
        cases.append(Case(f"random{k:04d}-{name}", text[:i] + " " + random_comment(rng) + " " + text[i:]))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--random", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=20261015)
    args = parser.parse_args()
    if args.jobs < 1 or args.random < 0:
        parser.error("--jobs must be positive and --random nonnegative")
    check_toolchain()
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    exploit_cases = exploits()
    cache = {}
    preflight(source_bases() + [(name, original)
              for name, original, _, _, _, _ in exploit_cases], cache)
    failures = 0
    for name, original, mutated, _, fooled, old_fn in exploit_cases:
        same_old = old_fn(original) == old_fn(mutated)
        try:
            same_new = lex.code(original) == lex.code(mutated)
        except lex.LexError as err:
            same_new = f"refused ({err})"
        ok = same_old and same_new is not True
        failures += not ok
        print(f"{'agree' if ok else 'DIFFER'} {name}: the old {fooled} gives the original "
              f"and the mutated text the same value: {same_old}; new code() equal: {same_new}")
    cases = corpus() + [Case(f"{n}-mutated", t) for n, _, _, t, _, _ in exploit_cases] \
        + random_cases(args.random, random.Random(args.seed))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for ok, line in pool.map(lambda c: run_case(c, cache), cases):
            failures += not ok
            print(line, flush=True)
    print(f"{len(cases)} cases, {failures} disagreements")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    try:
        main()
    except (ProbeError, lex.LexError, OSError, UnicodeError, subprocess.TimeoutExpired) as err:
        print(f"ERROR: {err}", file=sys.stderr, flush=True)
        sys.exit(1)
