#!/usr/bin/env python3
"""The identity sidecars of the statement snapshots (rule 30 (e) of
scripts/check_sources.py; the repair E42).

A statement snapshot prints each frozen or accepted declaration, but a
printed name can resolve to another constant than at the acceptance commit
(E42: topology_structure.closed printed alike for MathComp's predicate and
for a new project constant). The identity layer reads, for each declaration
of each snapshot, the global references of its kernel term with the exporter
of check/identity/ (KernelIdentity, a query of a small OCaml plugin), and
compares them with those read at the acceptance commit.

This module holds what scripts/check_sources.py, scripts/run_checks.py and
scripts/snapshot_baselines.py share:

- the inventory: for each snapshot file check/snapshots/<Name>.v that
  prints a declaration, its Require lines and one query per Print or Check
  line, in order: a Print in definition mode (type and body), except the
  roots of OPAQUE, explicitly listed, in opaque-body mode, and a Check (or
  Check @) in type mode (the type only); Print Module makes no query;
- the driver check/identity/Identity<Name>.v of each snapshot: its Require
  lines, Declare ML Module "kernel_identity" and one KernelIdentity line per
  query;
- the framing of a driver's output: exactly one complete record line per
  query, in order, with the expected schema, Rocq version, target, mode and
  parts, and nothing else;
- the sidecar: for each query its target, its mode, the root identity and,
  for each part, the references of the term in a fixed depth-first order:
  the structural path of each reference-bearing node (Const, Ind, Construct,
  Proj, and the inductive of a Case), its kind and its identity (user and
  canonical kernel names, indices). Paths are stored as the length of the
  common prefix with the previous path and the rest, identities once in a
  table; the encoding is lossless. Universes are not in the sidecar: the
  printed snapshots, under Set Printing Universes, protect them.

The sidecar adds name identity to the other protections; it is not a hash
of the meaning of the terms or of their environment.
"""

import hashlib
import json
import json.scanner
import os
import re
import shutil
import subprocess
import sys
import threading

PREFIX = "KERNEL_IDENTITY "
SCHEMA = "rocq-kernel-identity-pilot-v3"
ROCQ = "9.1.1"
SIDECAR_SCHEMA = "phase13-identity-sidecar-v1"
INVENTORY_SCHEMA = "phase13-identity-inventory-v1"
# The opaque roots printed by a snapshot, listed by name: never inferred.
OPAQUE = ("EllipsoidFitting.GaussianProbabilityProductDefinitions."
          "gaussian_pair_probability_setT_subproof",)
# Snapshots kept for history only, compared with no build of the tree.
HISTORICAL_ONLY = ("SnapshotAcceptedStatements",)
REFERENCE_KINDS = ("Const", "Ind", "Construct", "Proj", "Case")
# Every tag that the exporter writes (kernel_identity.ml: terms, sorts,
# levels, qualities, relevances, inversions, module paths, universe
# contexts); a record with any other tag is refused, so that a change of the
# exporter cannot drop references silently.
TAGS = frozenset((
    "App", "Array", "Case", "CaseInvert", "Cast", "CoFix", "Const", "Construct", "Fix",
    "Float", "Ind", "Int", "Lambda", "LetIn", "LevelGlobal", "LevelVar", "MPdot",
    "MPfile", "NoInvert", "Polymorphic", "PrivateMonomorphic", "PrivatePolymorphic",
    "Prod", "Proj", "QGlobal", "QSort", "QVar", "Rel", "RelevanceVar", "Set", "Sort",
    "String", "Type"))
# The recursion limit of the parse of one output (records nest 20,042
# levels deep in SnapshotPhase12Batch2); deeper records fail closed.
RECURSION_LIMIT = 1_000_000
# The exporter's sources in check/identity/, and the commands that build it,
# run in a copy of them (src/ and findlib/kernel_identity/ of the build
# directory).
PLUGIN_SOURCES = ("kernel_universe.ml", "kernel_identity.ml")
PLUGIN_COMMANDS = [
    ["ocamlfind", "ocamlopt", "-rectypes", "-package", "rocq-runtime.kernel",
     "-w", "+8", "-warn-error", "+8", "-c", "src/kernel_universe.ml"],
    ["ocamlfind", "ocamlopt", "-rectypes", "-I", "src", "-package", "rocq-runtime.vernac",
     "-w", "+8", "-warn-error", "+8", "-c", "src/kernel_identity.ml"],
    ["ocamlfind", "ocamlopt", "-rectypes", "-package", "rocq-runtime.vernac", "-shared",
     "src/kernel_universe.cmx", "src/kernel_identity.cmx",
     "-o", "findlib/kernel_identity/kernel_identity.cmxs"]]
PRINT = re.compile(r"Print ([^\s.][^\s]*)\.")
CHECK = re.compile(r"Check @?([^\s.][^\s]*)\.")


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def recipe_sha256():
    """The SHA-256 of the build recipe of the exporter."""
    return sha256(canonical(PLUGIN_COMMANDS).encode())


def ocaml_toolchain(timeout):
    """The OCaml toolchain that builds the exporter: the versions of
    ocamlopt and findlib and the directory of rocq-runtime, which must lie in
    the switch of rocq (rocq -where); ValueError otherwise."""
    env = ocaml_free_environment()

    def ask(cmd):
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=timeout)
        except (OSError, subprocess.SubprocessError) as error:
            raise ValueError(f"{' '.join(cmd)}: {error}")
        if r.returncode != 0 or not r.stdout.strip():
            raise ValueError(f"{' '.join(cmd)}: exited with status {r.returncode}")
        return r.stdout.strip().splitlines()[0]
    found = {"ocaml": ask(["ocamlfind", "ocamlopt", "-version"]),
             "findlib": ask(["ocamlfind", "query", "findlib", "-format", "%v"]),
             "rocq-runtime": ask(["ocamlfind", "query", "rocq-runtime"])}
    where = ask(["rocq", "-where"])
    if os.path.dirname(os.path.realpath(found["rocq-runtime"])) != \
            os.path.dirname(os.path.realpath(where)):
        raise ValueError(f"rocq-runtime ({found['rocq-runtime']}) is not in the switch of "
                         f"rocq ({where})")
    return found


def ocaml_free_environment():
    """The environment without the variables that steer OCaml, findlib and
    the OCaml compiler (OCAMLFIND_CONF, OCAMLPARAM, CAMLLIB and the others)."""
    return {k: v for k, v in os.environ.items() if not k.startswith(("OCAML", "CAML"))}


def build_plugin(sources, directory, timeout):
    """Build the exporter from sources (check/identity/) in the new
    directory: its findlib directory, or ValueError with the failure."""
    (directory / "src").mkdir(parents=True)
    (directory / "findlib" / "kernel_identity").mkdir(parents=True)
    for name in PLUGIN_SOURCES:
        shutil.copyfile(sources / name, directory / "src" / name)
    shutil.copyfile(sources / "META", directory / "findlib" / "kernel_identity" / "META")
    for cmd in PLUGIN_COMMANDS:
        try:
            r = subprocess.run(cmd, cwd=directory, capture_output=True, text=True,
                               env=ocaml_free_environment(), timeout=timeout)
        except (OSError, subprocess.SubprocessError) as error:
            raise ValueError(f"{' '.join(cmd)}: {error}")
        if r.returncode != 0:
            raise ValueError(" ".join(cmd) + "\n" + "\n".join(
                (r.stdout + r.stderr).splitlines()[-12:]))
    return directory / "findlib"


def driver_environment(findlib):
    """The environment of a driver compilation: OCAMLPATH names the
    exporter's findlib directory, and nothing else steers OCaml."""
    env = ocaml_free_environment()
    env["OCAMLPATH"] = str(findlib)
    return env


def parse_snapshot(text):
    """The Require lines and the queries of a snapshot file, in order."""
    requires, queries = [], []
    for line in text.splitlines():
        if line.startswith("Require "):
            requires.append(line)
        elif line.startswith("Print Module "):
            continue
        elif line.startswith("Print "):
            m = PRINT.fullmatch(line)
            if not m:
                raise ValueError(f"not a Print of one declaration: {line!r}")
            target = m.group(1)
            queries.append({"target": target,
                            "mode": "opaque-body" if target in OPAQUE else "definition",
                            "parts": ["type", "body"]})
        elif line.startswith("Check "):
            m = CHECK.fullmatch(line)
            if not m:
                raise ValueError(f"not a Check of one declaration: {line!r}")
            queries.append({"target": m.group(1), "mode": "type", "parts": ["type"]})
    for k, q in enumerate(queries):
        q["ordinal"] = k
    return requires, queries


def inventory(snapshot_texts):
    """{name: text of check/snapshots/<name>.v} -> the inventory."""
    snapshots = {}
    for name in sorted(snapshot_texts):
        if name in HISTORICAL_ONLY:
            continue
        requires, queries = parse_snapshot(snapshot_texts[name])
        if queries:
            snapshots[name] = {"requires": requires, "queries": queries}
    return {"schema": INVENTORY_SCHEMA, "opaque": list(OPAQUE), "snapshots": snapshots}


def inventory_text(inv):
    return json.dumps(inv, indent=1, sort_keys=True) + "\n"


def driver_text(name, entry):
    lines = ["(* The identity driver of the statement snapshot " + name + " (rule 30 (e)",
             "   of scripts/check_sources.py): the references of the kernel term of",
             "   each declaration that check/snapshots/" + name + ".v prints, read by",
             "   the exporter of check/identity/. Written by",
             "   scripts/snapshot_baselines.py from check/identity/inventory.json; its",
             "   reference is check/identity/Identity" + name + ".json. *)",
             ""]
    lines += entry["requires"]
    lines += ['Declare ML Module "kernel_identity".', ""]
    lines += [f'KernelIdentity "{q["mode"]}" "{q["target"]}".' for q in entry["queries"]]
    return "\n".join(lines) + "\n"


_DECODER = json.JSONDecoder()
_DECODER.scan_once = json.scanner.py_make_scanner(_DECODER)


def _decode(text):
    """The C decoder, or, on records nested deeper than its fixed recursion
    limit (Python 3.12; 20,042 levels in SnapshotPhase12Batch2), the
    pure-Python decoder, whose recursion sys.setrecursionlimit bounds. Both
    give the same objects."""
    try:
        return json.loads(text)
    except RecursionError:
        return _DECODER.decode(text)


def _in_large_stack(function, *args):
    """Run function(*args) in a thread with a 1 GiB stack and a high
    recursion limit; re-raise what it raises."""
    result, failure = [], []

    def target():
        try:
            result.append(function(*args))
        except BaseException as error:
            failure.append(error)
    old_limit = sys.getrecursionlimit()
    old_size = threading.stack_size(1 << 30)
    sys.setrecursionlimit(RECURSION_LIMIT)
    try:
        worker = threading.Thread(target=target)
        worker.start()
        worker.join()
    finally:
        threading.stack_size(old_size)
        sys.setrecursionlimit(old_limit)
    if failure:
        raise failure[0]
    return result[0]


def decode_output(raw):
    """The text of a driver's output: strict UTF-8, ValueError otherwise."""
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"not UTF-8: {error}")


def _frame(stdout, queries):
    lines = stdout.split("\n")
    if not lines or lines[-1] != "":
        raise ValueError("the output does not end with a complete line")
    lines = lines[:-1]
    if len(lines) != len(queries):
        raise ValueError(f"{len(lines)} output lines for {len(queries)} queries")
    records = []
    for k, (line, q) in enumerate(zip(lines, queries)):
        if not line.startswith(PREFIX):
            raise ValueError(f"line {k + 1}: not an identity record")
        try:
            record = _decode(line[len(PREFIX):])
        except (ValueError, RecursionError) as error:
            raise ValueError(f"line {k + 1}: not a complete record ({type(error).__name__})")
        if not isinstance(record, dict):
            raise ValueError(f"line {k + 1}: not a record")
        if record.get("schema") != SCHEMA or record.get("rocq") != ROCQ:
            raise ValueError(f"line {k + 1}: schema {record.get('schema')!r}, "
                             f"Rocq {record.get('rocq')!r}")
        if record.get("target") != q["target"] or record.get("mode") != q["mode"]:
            raise ValueError(f"line {k + 1}: a record of {record.get('target')} "
                             f"({record.get('mode')}) where {q['target']} ({q['mode']}) "
                             "is expected")
        missing = [p for p in q["parts"] if p not in record]
        extra = [p for p in ("body",) if p in record and p not in q["parts"]]
        if missing or extra:
            raise ValueError(f"line {k + 1}: parts missing {missing}, unexpected {extra}")
        try:
            root = kernel_name(record["identity"]["user"])
        except (KeyError, TypeError) as error:
            raise ValueError(f"line {k + 1}: no root identity ({error})")
        if root != q["target"]:
            raise ValueError(f"line {k + 1}: the root identity {root} is not {q['target']}")
        records.append(record)
    return records


def references(term):
    """The reference-bearing nodes of a term, depth-first in the record's key
    order, each [path, kind, identity]. Iterative: terms nest deeper than
    Python's recursion allows."""
    out, stack = [], [(term, [])]
    while stack:
        x, path = stack.pop()
        if isinstance(x, dict):
            tag = x.get("tag")
            if tag is not None and tag not in TAGS:
                raise ValueError(f"an unknown node {tag!r} at {'/'.join(map(str, path))}")
            if tag in ("Const", "Ind", "Construct", "Proj"):
                out.append([path, tag, x["identity"]])
            elif tag == "Case":
                out.append([path, tag, x["inductive"]])
            stack.extend((v, path + [k]) for k, v in reversed(list(x.items())))
        elif isinstance(x, list):
            stack.extend((v, path + [i]) for i, v in reversed(list(enumerate(x))))
    return out


def encode_refs(refs, table, index):
    out, prev = [], []
    for path, kind, identity in refs:
        k = 0
        while k < len(prev) and k < len(path) and prev[k] == path[k]:
            k += 1
        key = canonical(identity)
        if key not in index:
            index[key] = len(table)
            table.append(identity)
        out.append([k, path[k:], kind, index[key]])
        prev = path
    return out


def decode_refs(encoded, table):
    out, prev = [], []
    for k, suffix, kind, i in encoded:
        path = prev[:k] + suffix
        out.append([path, kind, table[i]])
        prev = path
    return out


def _sidecar(name, stdout, queries):
    records = _frame(stdout, queries)
    entries, table, index = [], [], {}
    for q, r in zip(queries, records):
        parts = {}
        for part in q["parts"]:
            refs = references(r[part])
            parts[part] = encode_refs(refs, table, index)
            if decode_refs(parts[part], table) != refs:
                raise ValueError(f"{q['target']} {part}: the encoding is not lossless")
        entries.append({"ordinal": q["ordinal"], "target": q["target"], "mode": q["mode"],
                        "identity": r["identity"], "parts": parts})
    data = {"schema": SIDECAR_SCHEMA, "snapshot": name, "count": len(entries),
            "identities": table, "entries": entries}
    return (canonical(data) + "\n").encode()


def sidecar_bytes(name, stdout, queries):
    """The canonical sidecar of a driver's output; ValueError if the output
    is not exactly framed."""
    return _in_large_stack(_sidecar, name, stdout, queries)


def qualified(k):
    """(full name, file) of a kernel name: the file is the dirpath of its
    MPfile, the full name that dirpath, the labels of the modules inside the
    file and the label."""
    m, labels = k["module"], []
    while m["tag"] == "MPdot":
        labels.append(m["label"])
        m = m["parent"]
    if m["tag"] != "MPfile":
        raise ValueError(f"an unknown module path {m['tag']!r}")
    file = ".".join(m["path"])
    return ".".join(list(m["path"]) + labels[::-1] + [k["label"]]), file


def kernel_name(k):
    return qualified(k)[0]


def qualified_names(kind, identity):
    """The (full name, file) pairs, user and canonical, of a reference."""
    if kind == "Const":
        return {qualified(identity["user"]), qualified(identity["canonical"])}
    if kind == "Proj":
        return (qualified_names("Const", identity["constant"])
                | qualified_names("Ind", identity["inductive"]))
    if kind in ("Ind", "Case"):
        return {qualified(identity["mutual"]["user"]),
                qualified(identity["mutual"]["canonical"])}
    if kind == "Construct":
        return qualified_names("Ind", identity["inductive"])
    raise ValueError(f"unknown reference kind {kind!r}")


def names(kind, identity):
    """The full names (user and canonical) that a reference designates."""
    return {full for full, _ in qualified_names(kind, identity)}


def referenced_names(data):
    """{(full name, file): (target, kind)} of every reference of a sidecar,
    user and canonical names apart."""
    found = {}
    for entry in data["entries"]:
        for refs in entry["parts"].values():
            for _, _, kind, i in refs:
                for pair in qualified_names(kind, data["identities"][i]):
                    found.setdefault(pair, (entry["target"], kind))
    return found


def unprotected(found, characterization, subjects, frozen_files, pinned, check_files, roots):
    """The protection closure of rule 30 (e) over the kernel names of the
    references: found is {snapshot: referenced_names(sidecar)}. A project
    name (one of roots) that a snapshot other than a characterization one
    references must be a subject of that snapshot, be defined in a frozen
    file (its file is one of frozen_files), be pinned, be referenced by a
    characterization snapshot, or, under Checks., be defined in a check file
    (check_files: the logical names Checks.<Name> of the check files, whose
    code is fixed). Each of the user and the canonical name must hold.
    Returns [(snapshot, target, full name, kind)]."""
    characterized = {full for name in characterization
                     for full, _ in found.get(name, {})}
    out = []
    for name, refs in sorted(found.items()):
        if name in characterization:
            continue
        for (full, file), (target, kind) in sorted(refs.items()):
            if not full.startswith(tuple(r + "." for r in roots)):
                continue
            if file.startswith("Checks."):
                if file in check_files:
                    continue
            elif (full in subjects.get(name, ()) or file in frozen_files
                    or full in pinned or full in characterized):
                continue
            out.append((name, target, full, kind))
    return out


def show(kind, identity):
    return kind + " " + " / ".join(sorted(names(kind, identity)))


def first_differences(ref_bytes, out_bytes, limit=3):
    """A short account of how two sidecars differ, for the message of a
    failure; the comparison itself is the equality of the bytes. Entries are
    compared decoded, identities resolved, and the account is never empty for
    unequal bytes."""
    if ref_bytes == out_bytes:
        return []
    try:
        x, y = json.loads(ref_bytes), json.loads(out_bytes)
        found = []
        for key in ("schema", "snapshot", "count"):
            if x.get(key) != y.get(key):
                found.append(f"{key} {x.get(key)!r} in the reference, {y.get(key)!r} here")
        if len(x["entries"]) != len(y["entries"]):
            found.append(f"{len(x['entries'])} entries in the reference, "
                         f"{len(y['entries'])} here")

        def decoded_entries(d):
            return [(e, {p: decode_refs(v, d["identities"]) for p, v in e["parts"].items()})
                    for e in d["entries"]]
        for (e, pe), (f, pf) in zip(decoded_entries(x), decoded_entries(y)):
            if len(found) >= limit:
                break
            head = f"#{e.get('ordinal')} {e.get('target')}"
            if (e.get("ordinal"), e.get("target"), e.get("mode")) != \
                    (f.get("ordinal"), f.get("target"), f.get("mode")):
                found.append(f"{head}: the query #{f.get('ordinal')} {f.get('target')} "
                             f"({f.get('mode')}) here")
            elif e.get("identity") != f.get("identity"):
                found.append(f"{head}: another root identity")
            elif set(pe) != set(pf):
                found.append(f"{head}: parts {sorted(pe)} in the reference, "
                             f"{sorted(pf)} here")
            else:
                for part in pe:
                    r, s = pe[part], pf[part]
                    if r == s:
                        continue
                    for u, v in zip(r, s):
                        if u != v:
                            found.append(f"{head} {part} at {'/'.join(map(str, u[0]))}: "
                                         f"{show(u[1], u[2])} in the reference, "
                                         f"{show(v[1], v[2])} here")
                            break
                    else:
                        found.append(f"{head} {part}: {len(r)} references in the "
                                     f"reference, {len(s)} here")
                    break
        return found[:limit] or ["the sidecars differ outside their entries"]
    except (ValueError, KeyError, TypeError, IndexError, AttributeError):
        return ["the sidecars differ, and one of them is not a well-formed sidecar"]
