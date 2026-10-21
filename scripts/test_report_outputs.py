#!/usr/bin/env python3
"""Harmless tests of the real checker's output parser and completion framing.

Run: python3 -I -B scripts/test_report_outputs.py
No Rocq process is started and no project input/output is changed. The checker
is loaded directly from source, without importing a cached bytecode file.
These tests concern truncation and report structure. The runner's success
status and manifest hashes authenticate the contents; framing alone does not
validate an arbitrary edit to a report with a new completion trailer.
"""

from pathlib import Path
import types
import unittest


ROOT = Path(__file__).resolve().parent.parent
checker = types.ModuleType("check_sources")
checker.__file__ = str(ROOT / "scripts/check_sources.py")
exec(compile(Path(checker.__file__).read_bytes(), checker.__file__, "exec"), checker.__dict__)
TRAILER = checker.OUTPUT_COMPLETE
MARKER = "Checks.Example.accepted_statement"
REPORT = (
    f"Constant {MARKER}\n"
    "Axioms:\n"
    "boolp.propext : forall P Q : Prop, (P <-> Q) -> P = Q\n"
    "boolp.funext :\n"
    "  forall (A B : Type) (f g : A -> B),\n"
    "  (forall x, f x = g x) -> f = g\n"
)
AXIOMS = frozenset(("boolp.propext", "boolp.funext"))
CLOSED = "Closed under the global context\n"


class ReportOutputs(unittest.TestCase):
    def assert_rejected(self, text, diagnostic=None):
        items = checker.parse_output(text)
        errors = [value for kind, value in items if kind == "other"]
        self.assertTrue(errors, (text, items))
        if diagnostic is not None:
            self.assertTrue(any(diagnostic in value for value in errors), errors)

    def test_empty_output_is_framed_and_remains_empty(self):
        self.assertEqual(checker.parse_output(TRAILER), [])
        self.assert_rejected("", "completion trailer")

    def test_complete_representative_report(self):
        self.assertEqual(checker.parse_output(REPORT + TRAILER),
                         [("marker", MARKER), ("report", AXIOMS)])

    def test_closed_report(self):
        self.assertEqual(checker.parse_output(CLOSED + TRAILER),
                         [("report", frozenset())])

    def test_wrapped_marker_and_shorter_name(self):
        text = (f"Constant\n{MARKER}\n"
                "  (shorter name to refer to it in current context is Example.accepted_statement)\n"
                + CLOSED + TRAILER)
        self.assertEqual(checker.parse_output(text),
                         [("marker", MARKER), ("report", frozenset())])

    def test_every_proper_prefix_is_rejected(self):
        # This includes cuts in axiom names, axiom types, continuation lines,
        # complete line boundaries, and every position of the final trailer.
        for label, complete in (("empty", TRAILER), ("report", REPORT + TRAILER),
                                ("closed", CLOSED + TRAILER)):
            for cut in range(len(complete)):
                with self.subTest(output=label, cut=cut):
                    self.assert_rejected(complete[:cut], "completion trailer")

    def test_complete_body_without_trailer_is_rejected(self):
        self.assert_rejected(REPORT, "completion trailer")
        self.assert_rejected(CLOSED, "completion trailer")

    def test_duplicate_complete_outputs_are_rejected(self):
        complete = REPORT + TRAILER
        self.assert_rejected(complete + complete, "completion trailer")
        self.assert_rejected(TRAILER + TRAILER, "completion trailer")

    def test_duplicate_and_misplaced_trailer(self):
        for text in (REPORT + TRAILER + TRAILER, TRAILER + REPORT,
                     TRAILER + REPORT + TRAILER, REPORT + TRAILER + "extra\n",
                     REPORT + TRAILER + "\n"):
            with self.subTest(text=text):
                self.assert_rejected(text, "completion trailer")

    def test_partial_final_line_cannot_be_reframed(self):
        for body in (REPORT.rstrip("\n"), "Axioms:\nboolp.funext : fo",
                     "Closed under the glo", "Constant"):
            with self.subTest(body=body):
                self.assert_rejected(body + TRAILER, "inside a line")

    def test_damaged_trailer(self):
        for trailer in (TRAILER.rstrip("\n"), TRAILER.replace("COMPLETE", "COMPLET"),
                        TRAILER.lower(), TRAILER.replace("\n", "\r\n")):
            with self.subTest(trailer=trailer):
                self.assert_rejected(REPORT + trailer, "completion trailer")

    def test_empty_axioms_section_is_not_a_report(self):
        self.assert_rejected("Axioms:\n" + TRAILER, "Axioms:")

    def test_duplicate_reports_remain_visible_to_exact_count_check(self):
        # One authentic final trailer does not erase duplicated report bodies.
        # The higher-level checker requires the exact number and marker order.
        items = checker.parse_output(REPORT + REPORT + TRAILER)
        self.assertEqual(items, [("marker", MARKER), ("report", AXIOMS)] * 2)
        self.assertEqual(sum(kind == "report" for kind, _ in items), 2)
        self.assertNotEqual(items, [("marker", MARKER), ("report", AXIOMS)])

    def test_ordered_distinct_report_markers_are_preserved(self):
        second = "Constant Checks.Other.statement\n" + CLOSED
        self.assertEqual(checker.parse_output(REPORT + second + TRAILER), [
            ("marker", MARKER), ("report", AXIOMS),
            ("marker", "Checks.Other.statement"), ("report", frozenset())])


if __name__ == "__main__":
    unittest.main(verbosity=2)
