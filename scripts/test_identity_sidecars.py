#!/usr/bin/env python3
"""Tests of scripts/identity_sidecars.py (rule 30 (e), E42): the inventory,
the drivers, the framing, the reference walk, the encoding and the account
of differences. No Rocq, OCaml or git process is run.

    python3 -I -B scripts/test_identity_sidecars.py
"""

import copy
import json
import os
from pathlib import Path
import shutil
import tempfile
import types
import unittest
from unittest import mock

SOURCE = Path(__file__).with_name("identity_sidecars.py")
ids = types.ModuleType("identity_sidecars_under_test")
ids.__file__ = str(SOURCE)
exec(compile(SOURCE.read_bytes(), str(SOURCE), "exec"), ids.__dict__)

SNAPSHOT = """(* A snapshot. *)

Require GaussianApplications.Stmt.
Require Checks.Lib.

Set Printing All.

Print Module GaussianApplications.Stmt.
Print GaussianApplications.Stmt.d.
Check @GaussianApplications.Stmt.l.
Check GaussianApplications.Stmt.m.
Print EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_pair_probability_setT_subproof.
"""


def kname(full):
    parts = full.split(".")
    return {"module": {"tag": "MPfile", "path": parts[:-1]}, "label": parts[-1]}


def const(full):
    return {"tag": "Const", "identity": {"user": kname(full), "canonical": kname(full)},
            "instance": {"qualities": [], "levels": []}}


def record(target, mode, body=True, root=None, schema=None, rocq=None):
    r = {"schema": schema or ids.SCHEMA, "rocq": rocq or ids.ROCQ, "target": target,
         "mode": mode, "identity": {"user": kname(root or target),
                                    "canonical": kname(root or target)},
         "type": {"tag": "App", "function": const("A.f"), "arguments": [const("A.g")]}}
    if body:
        r["body"] = {"tag": "Lambda", "binder": {"relevance": "Relevant"},
                     "domain": const("A.t"), "body": const("A.h")}
    return r


def line(r):
    return ids.PREFIX + json.dumps(r, separators=(",", ":"))


QUERIES = [{"ordinal": 0, "target": "A.x", "mode": "definition", "parts": ["type", "body"]},
           {"ordinal": 1, "target": "A.y", "mode": "type", "parts": ["type"]}]
GOOD = line(record("A.x", "definition")) + "\n" + line(record("A.y", "type", False)) + "\n"


class Inventory(unittest.TestCase):
    def test_snapshot_queries(self):
        requires, queries = ids.parse_snapshot(SNAPSHOT)
        self.assertEqual(requires, ["Require GaussianApplications.Stmt.", "Require Checks.Lib."])
        self.assertEqual([(q["ordinal"], q["target"], q["mode"], q["parts"]) for q in queries], [
            (0, "GaussianApplications.Stmt.d", "definition", ["type", "body"]),
            (1, "GaussianApplications.Stmt.l", "type", ["type"]),
            (2, "GaussianApplications.Stmt.m", "type", ["type"]),
            (3, ids.OPAQUE[0], "opaque-body", ["type", "body"])])

    def test_malformed_lines_are_refused(self):
        for text in ("Print A.b c.", "Check A.b : nat.", "Print A.b"):
            with self.assertRaises(ValueError):
                ids.parse_snapshot(text + "\n")

    def test_inventory_skips_historical_and_empty_snapshots(self):
        inv = ids.inventory({"SnapshotX": SNAPSHOT, "SnapshotAcceptedStatements": SNAPSHOT,
                             "SnapshotEmpty": "Require A.\nPrint Module A.\n"})
        self.assertEqual(list(inv["snapshots"]), ["SnapshotX"])
        self.assertEqual(inv["opaque"], list(ids.OPAQUE))
        self.assertEqual(json.loads(ids.inventory_text(inv)), inv)

    def test_driver_text(self):
        inv = ids.inventory({"SnapshotX": SNAPSHOT})
        text = ids.driver_text("SnapshotX", inv["snapshots"]["SnapshotX"])
        body = text.split("*)\n", 1)[1]
        self.assertEqual(body, "\nRequire GaussianApplications.Stmt.\nRequire Checks.Lib.\n"
                         'Declare ML Module "kernel_identity".\n\n'
                         'KernelIdentity "definition" "GaussianApplications.Stmt.d".\n'
                         'KernelIdentity "type" "GaussianApplications.Stmt.l".\n'
                         'KernelIdentity "type" "GaussianApplications.Stmt.m".\n'
                         f'KernelIdentity "opaque-body" "{ids.OPAQUE[0]}".\n')
        self.assertTrue(text.isascii())


class Framing(unittest.TestCase):
    def test_good_output_is_accepted(self):
        data = json.loads(ids.sidecar_bytes("S", GOOD, QUERIES))
        self.assertEqual(data["count"], 2)
        self.assertEqual([e["target"] for e in data["entries"]], ["A.x", "A.y"])

    def test_bad_outputs_are_refused(self):
        x, y = line(record("A.x", "definition")), line(record("A.y", "type", False))
        bad = {
            "missing": x + "\n",
            "duplicate": GOOD + y + "\n",
            "substituted": x + "\n" + line(record("A.z", "type", False)) + "\n",
            "reordered": y + "\n" + x + "\n",
            "mode changed": line(record("A.x", "type", False)) + "\n" + y + "\n",
            "truncated record": GOOD[:-40] + "\n",
            "cut inside a line": GOOD[:-1],
            "extra line": "noise\n" + GOOD,
            "blank line": x + "\n\n" + y + "\n",
            "part missing": line(record("A.x", "definition", False)) + "\n" + y + "\n",
            "part extra": x + "\n" + line(record("A.y", "type")) + "\n",
            "empty": "",
            "root identity differs": line(record("A.x", "definition", root="A.w")) + "\n"
                                     + y + "\n",
            "extra JSON on a line": x + " {}\n" + y + "\n",
            "old schema": line(record("A.x", "definition",
                                      schema="rocq-kernel-identity-prototype-v2"))
                          + "\n" + y + "\n",
            "other Rocq": line(record("A.x", "definition", rocq="9.1.0")) + "\n" + y + "\n",
            "not a record": ids.PREFIX + "[1, 2]\n" + y + "\n",
        }
        for label, text in bad.items():
            with self.subTest(label), self.assertRaises(ValueError):
                ids.sidecar_bytes("S", text, QUERIES)


class Encoding(unittest.TestCase):
    def test_walk_order_and_kinds(self):
        term = {"tag": "Case", "inductive": {"mutual": {"user": kname("I.i"),
                                                        "canonical": kname("I.i")},
                                             "index": 0},
                "parameters": [const("A.a")],
                "branches": [{"binders": [], "body": {"tag": "Construct", "identity": {
                    "inductive": {"mutual": {"user": kname("I.i"),
                                             "canonical": kname("I.i")}, "index": 0},
                    "index": 1}, "instance": {}}}],
                "scrutinee": {"tag": "Proj", "identity": {
                    "constant": {"user": kname("I.p"), "canonical": kname("I.p")},
                    "inductive": {"mutual": {"user": kname("I.r"),
                                             "canonical": kname("I.r")}, "index": 0},
                    "npars": 0, "arg": 0, "label": "p", "unfolded": False},
                    "relevance": "Relevant", "term": const("A.b")}}
        refs = ids.references(term)
        self.assertEqual([(r[0], r[1]) for r in refs], [
            ([], "Case"), (["parameters", 0], "Const"),
            (["branches", 0, "body"], "Construct"), (["scrutinee"], "Proj"),
            (["scrutinee", "term"], "Const")])
        self.assertEqual(ids.names("Proj", refs[3][2]), {"I.p", "I.r"})
        self.assertEqual(ids.names("Construct", refs[2][2]), {"I.i"})
        self.assertEqual(ids.names("Case", refs[0][2]), {"I.i"})

    def test_deep_term_round_trip(self):
        # Records nest 20,042 levels in a snapshot of the project; the C
        # decoder stops near 1,500: 2,000 term levels nest about 6,000 deep.
        term = const("A.leaf")
        for k in range(2000):
            term = {"tag": "App", "function": const(f"A.f{k % 3}"), "arguments": [term]}
        r = record("A.x", "definition")
        r["body"] = term
        text = line(r) + "\n" + line(record("A.y", "type", False)) + "\n"
        data = json.loads(ids.sidecar_bytes("S", text, QUERIES))
        refs = ids.decode_refs(data["entries"][0]["parts"]["body"], data["identities"])
        self.assertEqual(len(refs), 2001)
        self.assertEqual(refs[-1][2]["user"], kname("A.leaf"))
        self.assertEqual(len(refs[-1][0]), 4000)
        self.assertEqual(len(data["identities"]), 6)

    def test_encoding_is_canonical(self):
        self.assertEqual(ids.sidecar_bytes("S", GOOD, QUERIES),
                         ids.sidecar_bytes("S", GOOD, QUERIES))
        swapped = record("A.x", "definition")
        swapped["type"]["arguments"] = [const("A.f")]
        swapped["type"]["function"] = const("A.g")
        other = line(swapped) + "\n" + line(record("A.y", "type", False)) + "\n"
        self.assertNotEqual(ids.sidecar_bytes("S", GOOD, QUERIES),
                            ids.sidecar_bytes("S", other, QUERIES))


class Differences(unittest.TestCase):
    def setUp(self):
        self.ref = ids.sidecar_bytes("S", GOOD, QUERIES)
        self.base = json.loads(self.ref)

    def mutated(self, mutate):
        d = copy.deepcopy(self.base)
        mutate(d)
        return (ids.canonical(d) + "\n").encode()

    def test_equal_sidecars(self):
        self.assertEqual(ids.first_differences(self.ref, self.ref), [])

    def test_the_four_shapes_and_controls_are_described(self):
        def extra_entry(d):
            d["entries"].append(copy.deepcopy(d["entries"][-1]))

        def extra_part(d):
            d["entries"][1]["parts"]["body"] = copy.deepcopy(d["entries"][1]["parts"]["type"])

        def ordinal(d):
            d["entries"][0]["ordinal"] = 7

        def schema(d):
            d["schema"] = "another"

        def identity(d):
            d["entries"][0]["parts"]["type"][0][3] = 1

        def removed(d):
            d["entries"].pop()
            d["count"] -= 1
        for mutate in (extra_entry, extra_part, ordinal, schema, identity, removed):
            with self.subTest(mutate.__name__):
                other = self.mutated(mutate)
                self.assertNotEqual(other, self.ref)
                self.assertTrue(ids.first_differences(self.ref, other))

    def test_a_changed_reference_names_both_identities(self):
        attacked = GOOD.replace('["A"]},"label":"g"', '["Z"]},"label":"g"')
        self.assertNotEqual(attacked, GOOD)
        got = ids.sidecar_bytes("S", attacked, QUERIES)
        message = " ".join(ids.first_differences(self.ref, got))
        self.assertIn("A.g", message)
        self.assertIn("Z.g", message)


class Environment(unittest.TestCase):
    def test_ocaml_variables_are_removed(self):
        env = {"PATH": "/bin", "OCAMLFIND_CONF": "/x", "OCAMLPARAM": "y", "CAMLLIB": "z",
               "OCAMLPATH": "w", "HOME": "/h"}
        with mock.patch.dict(os.environ, env, clear=True):
            self.assertEqual(ids.ocaml_free_environment(), {"PATH": "/bin", "HOME": "/h"})
            self.assertEqual(ids.driver_environment(Path("/p/findlib")),
                             {"PATH": "/bin", "HOME": "/h", "OCAMLPATH": "/p/findlib"})



class Hardening(unittest.TestCase):
    def test_unknown_tag_is_refused(self):
        r = record("A.x", "definition")
        r["body"] = {"tag": "Meta", "index": 1}
        text = line(r) + "\n" + line(record("A.y", "type", False)) + "\n"
        with self.assertRaisesRegex(ValueError, "unknown node 'Meta'"):
            ids.sidecar_bytes("S", text, QUERIES)

    def test_output_that_is_not_utf8_is_refused(self):
        self.assertEqual(ids.decode_output(GOOD.encode()), GOOD)
        with self.assertRaisesRegex(ValueError, "not UTF-8"):
            ids.decode_output(GOOD.encode()[:-3] + b"\xff\n")

    def test_records_deeper_than_the_limit_fail_closed(self):
        # Beyond the C decoder (it stopped at 20,042 levels in the pilot) and
        # beyond a lowered Python limit; the text is written directly, since
        # json.dumps would recurse as deep.
        sep = (",", ":")
        level = '{"tag":"App","function":' + json.dumps(const("A.f"), separators=sep) \
            + ',"arguments":['
        body = level * 15000 + json.dumps(const("A.leaf"), separators=sep) + "]}" * 15000
        r = record("A.x", "definition")
        r["body"] = "BODY"
        deep = line(r).replace('"body":"BODY"', '"body":' + body)
        text = deep + "\n" + line(record("A.y", "type", False)) + "\n"
        with mock.patch.object(ids, "RECURSION_LIMIT", 2000):
            with self.assertRaisesRegex(ValueError, "RecursionError"):
                ids.sidecar_bytes("S", text, QUERIES)

    def test_recipe_hash(self):
        self.assertEqual(ids.recipe_sha256(), ids.recipe_sha256())
        with mock.patch.object(ids, "PLUGIN_COMMANDS", ids.PLUGIN_COMMANDS + [["true"]]):
            other = ids.recipe_sha256()
        self.assertNotEqual(other, ids.recipe_sha256())


def mutual(user, canonical=None):
    return {"user": kname(user), "canonical": kname(canonical or user)}


def sidecar_with(refs):
    """A sidecar whose one entry, target S.t, has the given references."""
    table, encoded = [], []
    for kind, identity in refs:
        table.append(identity)
        encoded.append([0, [len(encoded)], kind, len(table) - 1])
    return {"schema": ids.SIDECAR_SCHEMA, "snapshot": "S", "count": 1, "identities": table,
            "entries": [{"ordinal": 0, "target": "S.t", "mode": "type",
                         "identity": mutual("S.t"), "parts": {"type": encoded}}]}


class Closure(unittest.TestCase):
    ROOTS = ("GaussianAnalysis", "Checks")

    def closure(self, refs, frozen=(), pinned=(), characterized=(), checks=()):
        found = {"SnapshotX": ids.referenced_names(sidecar_with(refs))}
        if characterized:
            found["SnapshotChar"] = ids.referenced_names(sidecar_with(
                [("Const", mutual(n)) for n in characterized]))
        return ids.unprotected(found, ["SnapshotChar"], {}, set(frozen), set(pinned),
                               set(checks), self.ROOTS)

    def test_every_kind_of_reference_counts(self):
        ind = {"mutual": mutual("GaussianAnalysis.m.i"), "index": 0}
        refs = [("Ind", ind), ("Case", ind), ("Construct", {"inductive": ind, "index": 1}),
                ("Proj", {"constant": mutual("GaussianAnalysis.m.p"), "inductive": ind,
                          "npars": 0, "arg": 0, "label": "p", "unfolded": False})]
        for kind, identity in refs:
            with self.subTest(kind):
                self.assertTrue(self.closure([(kind, identity)]))
                self.assertEqual(self.closure([(kind, identity)], frozen=["GaussianAnalysis.m"]),
                                 [])

    def test_external_names_are_not_project_names(self):
        self.assertEqual(self.closure([("Const", mutual("mathcomp.algebra.ssralg.GRing.add"))]),
                         [])

    def test_canonical_name_must_be_protected_too(self):
        alias = mutual("GaussianAnalysis.f.c", "GaussianAnalysis.g.c")
        got = self.closure([("Const", alias)], frozen=["GaussianAnalysis.f"])
        self.assertEqual([full for _, _, full, _ in got], ["GaussianAnalysis.g.c"])

    def test_frozen_by_file_not_by_prefix(self):
        # A module F inside the file GaussianAnalysis.m is not the file
        # GaussianAnalysis.m.F; a file whose name extends a frozen one is not
        # frozen.
        inner = {"user": {"module": {"tag": "MPdot", "label": "F", "parent": {
            "tag": "MPfile", "path": ["GaussianAnalysis", "m"]}}, "label": "c"}}
        inner["canonical"] = inner["user"]
        self.assertTrue(self.closure([("Const", inner)], frozen=["GaussianAnalysis.m.F"]))
        self.assertEqual(self.closure([("Const", inner)], frozen=["GaussianAnalysis.m"]), [])
        self.assertTrue(self.closure([("Const", mutual("GaussianAnalysis.mx.c"))],
                                     frozen=["GaussianAnalysis.m"]))

    def test_pinned_characterized_and_check_names(self):
        c = ("Const", mutual("GaussianAnalysis.m.c"))
        self.assertEqual(self.closure([c], pinned=["GaussianAnalysis.m.c"]), [])
        self.assertEqual(self.closure([c], characterized=["GaussianAnalysis.m.c"]), [])
        lemma = ("Const", mutual("Checks.Lib.l"))
        self.assertTrue(self.closure([lemma]))
        self.assertEqual(self.closure([lemma], checks=["Checks.Lib"]), [])


class Generator(unittest.TestCase):
    """The identities command refuses a reused exporter build and an
    unverified extract (scripts/snapshot_baselines.py)."""

    def setUp(self):
        path = SOURCE.with_name("snapshot_baselines.py")
        self.gen = types.ModuleType("snapshot_baselines_under_test")
        self.gen.__file__ = str(path)
        exec(compile(path.read_bytes(), str(path), "exec"), self.gen.__dict__)
        self.tmp = Path(tempfile.mkdtemp(prefix="identity-generator-test-"))
        self.addCleanup(shutil.rmtree, self.tmp)

    def test_reused_plugin_directory_is_refused(self):
        (self.tmp / "identity-plugin").mkdir()
        inv = ids.inventory({})
        identity = self.tmp / "identity"
        identity.mkdir()
        (identity / "inventory.json").write_text(ids.inventory_text(inv))
        with mock.patch.object(self.gen, "BASE", self.tmp), \
                mock.patch.object(self.gen, "IDENTITY", identity), \
                mock.patch.object(self.gen, "identity_inventory", return_value=inv):
            with self.assertRaisesRegex(SystemExit, "refusing to reuse an exporter build"):
                self.gen.identities([], False)

    def test_unverified_extract_is_refused(self):
        entry = ("SnapshotX", "0" * 40, [], [], [], [])
        (self.tmp / entry[1][:12]).mkdir()
        with mock.patch.object(self.gen, "BASE", self.tmp):
            with self.assertRaisesRegex(ValueError, "no verified fresh archive"):
                self.gen.verify_extract(entry)

if __name__ == "__main__":
    unittest.main(verbosity=2)
