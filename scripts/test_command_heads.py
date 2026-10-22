#!/usr/bin/env python3
"""Parser-only regressions for E40; no Rocq or source fixture is executed.

    python3 -I -B scripts/test_command_heads.py

The fixtures are strings fed to the source checker. Some deliberately malformed
prefixes test refusal, not Rocq syntax. The complete control list comes from
Rocq 9.1.1's vernac/g_vernac.mlg. Source-scan failures are checked separately
from normalized command heads, so rejecting every control cannot conceal a
broken Require or scope parser.
"""
import types
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
checker = types.ModuleType("command_head_checker")
checker.__file__ = str(ROOT / "scripts" / "check_sources.py")
exec(compile(Path(checker.__file__).read_bytes(), checker.__file__, "exec"),
     checker.__dict__)

PREFIXES = (
    "Time", "Timeout 100", "Instructions", "Profile", 'Profile "report"',
    'Redirect "report"', "Fail", "Succeed",
)
FORBIDDEN = (
    "Axiom a : True", "Axioms a b : True", "Parameter a : Prop",
    "Parameters a b : Prop", "Conjecture a : True", "Admitted",
    "Admit Obligations", "Declare Instance a : True",
    'Declare ML Module "plugin"', 'Add LoadPath "path"',
    'Add Rec LoadPath "path"', 'Add ML Path "path"', 'Load "source"',
    'Extraction "output" a', "Recursive Extraction a",
    "Separate Extraction a", "Extraction Library A", 'Cd "path"',
    "Elpi Command probe", "From GaussianAnalysis Extra Dependency",
    'HB.graph "graph"', "Set Guard Checking", "Unset Guard Checking",
    "Set Positivity Checking", "Unset Positivity Checking",
    "Set Universe Checking", "Unset Universe Checking",
)
IMPORTS = (
    ("From Stdlib Require Import Reals Rpower Lra Psatz",
     [("Stdlib", s) for s in ("Reals", "Rpower", "Lra", "Psatz")]),
    ("From mathcomp Require Import Rstruct Rstruct_topology",
     [("mathcomp", s) for s in ("Rstruct", "Rstruct_topology")]),
    ("Require EllipsoidFitting.MainTheorem EllipsoidUniversality.MixtureTheorem",
     [("", "EllipsoidFitting.MainTheorem"),
      ("", "EllipsoidUniversality.MixtureTheorem")]),
    ("From GaussianApplications Require Import SKGapStatement",
     [("GaussianApplications", "SKGapStatement")]),
    ("From GaussianAnalysis.matrix Require Import euclidean",
     [("GaussianAnalysis.matrix", "euclidean")]),
    ("Require Export GaussianAnalysis.matrix.euclidean",
     [("", "GaussianAnalysis.matrix.euclidean")]),
)


class CommandHeads(unittest.TestCase):
    def setUp(self):
        checker.LEX_FAILURES.clear()

    def parsed(self, source):
        result = checker.sentences(source, "fixture.v")
        self.assertIsNotNone(result, checker.LEX_FAILURES)
        self.assertEqual(checker.LEX_FAILURES, [])
        return result

    def refused(self, source, scope="all"):
        result = checker.forbidden(source, "fixture.v", scope)
        self.assertTrue(result or checker.LEX_FAILURES, source)
        return result

    def test_every_control_exposes_and_refuses_the_command(self):
        for prefix in PREFIXES:
            with self.subTest(prefix=prefix):
                self.assertEqual(self.parsed(prefix + " Check nat.")[0][2],
                                 "Check nat")
                self.assertTrue(any("control prefix" in x for x in
                                    self.refused(prefix + " Check nat.")))

    def test_forbidden_class_cross_product(self):
        for prefix in PREFIXES:
            for command in FORBIDDEN:
                with self.subTest(prefix=prefix, command=command):
                    text = prefix + " " + command + "."
                    parsed = self.parsed(text)[0][2]
                    self.assertIsNotNone(checker.FORBIDDEN_COMMANDS.match(parsed))
                    failures = self.refused(text)
                    self.assertTrue(any("control prefix" in x for x in failures))
                    self.assertTrue(any("control prefix" not in x for x in failures))

    def test_require_rules_get_the_inner_import(self):
        for prefix in PREFIXES:
            for command, want in IMPORTS:
                with self.subTest(prefix=prefix, command=command):
                    text = prefix + " " + command + "."
                    self.assertEqual(list(checker.requires(text, "fixture.v")), want)
                    self.refused(text, "library")

    def test_attributes_modifiers_and_controls_interleave(self):
        for prefix in (
            "Time #[local]", "#[local] Time", "Local Time #[local]",
            'Time #[deprecated(note = "a ] b", since = "9.1")] #[local]',
            '#[outer(inner(note = "a ] b"))] Time',
            "Time Local #[local] Timeout 1", "#[local] Fail Timeout 1",
            "Profile \"report\" #[local] Instructions",
            "Time #[local] Profile \"report\" #[deprecated(note = \"x\")] Local",
            "Succeed Fail Time Timeout 1 Instructions Profile Redirect \"report\"",
        ):
            with self.subTest(prefix=prefix):
                text = prefix + " Axiom a : True."
                self.assertEqual(self.parsed(text)[0][2], "Axiom a : True")
                self.refused(text)

    def test_attributes_retain_policy_metadata(self):
        fixtures = (
            ("Time #[bypass_check] Definition x := 0.", "all", "bypass_check"),
            ("Time #[global] Set Implicit Arguments.", "library", "global or exported"),
            ("Time Global Set Implicit Arguments.", "library", "global or exported"),
            ("Time #[export] Set Implicit Arguments.", "library", "global or exported"),
            ('Time #[warnings = "-all"] Definition x := 0.', "fixed", "warning"),
            ('Time Set Warnings "-all".', "fixed", "Warnings"),
            ("Time Require Export A.", "library", "exported module"),
            ("Time Export A.", "library", "exported module"),
        )
        for text, scope, expected in fixtures:
            with self.subTest(text=text):
                self.assertTrue(any(expected in x for x in self.refused(text, scope)))

    def test_profile_string_is_one_argument(self):
        for filename in ('"report. fragment"', '"a""b"', '"Timeout 8 Axiom"', '""'):
            with self.subTest(filename=filename):
                text = "Profile " + filename + " #[local] Axiom a : True."
                parsed = self.parsed(text)
                self.assertEqual(len(parsed), 1)
                self.assertEqual(parsed[0][1], "Profile")
                self.assertEqual(parsed[0][2], "Axiom a : True")
                self.refused(text)

    def test_malformed_prefixes_fail_closed(self):
        for text in ("Timeout.", "Timeout x Check nat.", "Timeout -1 Check nat.",
                     "Timeout 1x Check nat.", "Redirect Check nat.",
                     "Time.", "Profile \"name\".", "Time #[local Check nat.",
                     'Profile "unterminated', "Time", "#[local]", "Local"):
            with self.subTest(text=text):
                checker.LEX_FAILURES.clear()
                self.assertIsNone(checker.sentences(text, "fixture.v"))
                self.assertTrue(checker.LEX_FAILURES)

    def test_incomplete_final_command_uses_the_same_parser(self):
        for prefix in PREFIXES:
            with self.subTest(prefix=prefix):
                text = prefix + " #[local] Axiom a : True"
                self.assertEqual(self.parsed(text)[0][2], "Axiom a : True")
                self.refused(text)

    def test_controlled_structural_commands_do_not_create_scope(self):
        for prefix in PREFIXES:
            for command in ("Section S", "Module S"):
                with self.subTest(prefix=prefix, command=command):
                    text = prefix + " " + command + ". Variable x : Prop."
                    self.assertTrue(any("outside a section" in x for x in
                                        self.refused(text)))
        text = "Section S. Time End S. Variable x : Prop. End S."
        self.assertTrue(any("control prefix" in x for x in self.refused(text)))

    def test_ordinary_scope_and_commands_stay_allowed(self):
        text = ("Section S. Variable x : Prop. Context (h : x). "
                "Lemma sample : x. Proof. exact h. Qed. End S. "
                "Module M. Definition y := 0. End M. "
                "Local Open Scope nat_scope. #[local] Set Implicit Arguments. "
                "HB.instance Definition _ := sample. "
                "From mathcomp Require Import all_ssreflect.")
        self.assertEqual(checker.forbidden(text, "fixture.v", "library"), [])
        self.assertEqual(checker.LEX_FAILURES, [])

    def test_comments_strings_and_identifier_suffixes_are_not_controls(self):
        text = ('(* Time Axiom hidden : True. *) '
                'Definition message := "Timeout 1. Axiom hidden : True.". '
                'Definition TimeSuffix := 0. '
                '#[deprecated(note = "Time")] Definition other := 0.')
        self.assertEqual(checker.forbidden(text, "fixture.v", "all"), [])
        self.assertEqual(checker.LEX_FAILURES, [])
        for name in ("TimeoutSuffix", "Time'", "Profile_name"):
            self.assertEqual(self.parsed(name + ".")[0][2], name)

    def test_initial_bom_is_a_blank_for_heads_only_at_file_start(self):
        for prefix in PREFIXES:
            with self.subTest(prefix=prefix):
                text = "\ufeff" + prefix + " Axiom a : True."
                self.assertEqual(self.parsed(text)[0][2], "Axiom a : True")
                self.refused(text)
        self.assertTrue(any("Axiom" in x for x in
                            self.refused("\ufeffAxiom a : True.")))
        self.assertEqual(list(checker.requires(
            "\ufeffFrom Stdlib Require Import Reals.", "fixture.v")),
            [("Stdlib", "Reals")])
        text = "\ufeffDefinition x := 0."
        self.assertEqual(checker.forbidden(text, "fixture.v", "all"), [])
        stripped, masked = checker.views(text, "fixture.v")
        self.assertEqual(len(stripped), len(masked))
        self.assertEqual(stripped, text)
        self.assertEqual(masked[0], " ")
        self.assertEqual(checker.code(text), "Definition x := 0.")
        # An interior BOM belongs to a token, not to Rocq's blanks. These
        # malformed command strings test lexical distinction, not compilation.
        for text in (" \ufeffTime Check nat.",
                     "Definition x := 0.\n\ufeffTime Check nat."):
            with self.subTest(text=text):
                parsed = self.parsed(text)
                self.assertIn("\ufeffTime", parsed[-1][2])
                self.assertNotIn("Time", parsed[-1][1].split())

    def test_module_forms_do_not_change_named_section_scope(self):
        # Alias bodies, functor binders and signature refinements can all
        # contain :=. None is a Section, regardless of its module grammar.
        for module in ("Module Alias := Base", "Module Type Alias := Base",
                       "Module Alias (X : T) := F X",
                       "Module Open : T with Definition t := nat",
                       "Module Open (X : T with Definition t := nat)"):
            with self.subTest(module=module):
                text = module + ". Variable x : Prop."
                self.assertTrue(any("outside a section" in x for x in
                                    self.refused(text)))
        allowed = ("Module Outer. Module Alias := Base. "
                   "Section S. Variable x : Prop. Section T. Variable y : Prop. "
                   "End T. End S. End Outer.")
        self.assertEqual(checker.forbidden(allowed, "fixture.v", "all"), [])
        self.assertEqual(checker.LEX_FAILURES, [])
        self.assertTrue(any("outside a section" in x for x in
                            self.refused(allowed + " Variable z : Prop.")))
        mismatch = "Section S. Section T. End S."
        self.assertTrue(any("does not match" in x for x in self.refused(mismatch)))
        # This is deliberately a parser-only regression. Rocq independently
        # rejects a module inside a Section, so it is not a compiling bypass.
        parser_only = "Section S. Module Alias := Base. End S. Variable z : Prop."
        self.assertTrue(any("outside a section" in x for x in
                            self.refused(parser_only)))

    def test_frozen_sections_retain_original_source(self):
        text = ("From A Require Import B. Section S. "
                "Variable x : Prop. End S.")
        self.assertEqual(checker.section_code(text, "S", "fixture.v"),
                         ("From A Require Import B.",
                          "Section S. Variable x : Prop. End S."))
        changed = "Time " + text
        imports, section = checker.section_code(changed, "S", "fixture.v")
        self.assertEqual(imports, "Time From A Require Import B.")
        self.assertEqual(section, "Section S. Variable x : Prop. End S.")
        self.refused(changed)
        self.assertIsNone(checker.section_code(
            "Time Section S. Variable x : Prop. End S.", "S", "fixture.v")[1])


if __name__ == "__main__":
    unittest.main(verbosity=2)
