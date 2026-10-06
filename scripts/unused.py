#!/usr/bin/env python3
"""List the declarations of theories/ that the main theorem does not use.

Run it after a build: it reads the .glob file that rocq compile writes next
to each module. A .glob file records the byte position of the name of each
declaration of the module, and of each reference that the module makes to a
declaration, with the module that declares it. The script splits each
module into sentences and groups each declaration with its proof into a
block. It attributes each reference to the block that contains it, which
gives a graph between blocks.

A declaration is used when its block is reachable in this graph from a
block of the frozen files (the statement, the main theorem and the
definitions of the statement). A proof can use some declarations without
naming them, so the following blocks are used as soon as the file, section
or module that contains them contains a used block: the commands Hint,
Instance, Canonical, HB.instance, Coercion, Notation and Ltac, the
Variable, Context and Let commands of sections, and the commands that
declare nothing (Open Scope, Set, ...). Everything that a used block
mentions is used. The .glob files do not record the uses of Ltac
definitions, so a block uses an Ltac definition when the name of the tactic
occurs in its code and the module of the tactic is the module of the block
or one that it requires.

The output is a list of candidates, not a proof of non-use: the build
decides.

    python3 scripts/unused.py            one Module.name per line for each
                                         unused declaration
    python3 scripts/unused.py --modules  the modules that nothing used
                                         depends on
    python3 scripts/unused.py --delete DIR
        writes to the repository DIR the analyzed tree without its unused
        modules and declarations. It deletes the files of the unused
        modules, their compiled files and their lines in _CoqProject, and
        removes them from the Require and Import commands of the other
        modules. It deletes the blocks of unused declarations with the
        comments just above them, the Arguments commands that mention them,
        and the sections and modules that nothing used is left in. It does
        not write the files that do not change.

--root DIR analyzes the repository DIR instead of the repository of this
script. --keep FILE treats as used the declarations that FILE lists, one
Module.name per line, and every declaration of the modules that it lists by
their name alone: the build, as arbiter, adds there what the analysis
missed.
"""

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from check_sources import FROZEN  # noqa: E402

PREFIX = "EllipsoidFitting."
BLANK = b" \t\r\n"

# Kinds of blocks.
DECL = "declaration"      # used when a used block refers to it
IMPLICIT = "implicit"     # Hint, Instance, Notation, Ltac, HB.instance, ...
LOCAL = "local"           # Variable, Context, Let, ... of a section
ATTACHED = "attached"     # Arguments, Print, ...: kept with what it mentions
REQUIRE = "require"
IMPORT = "import"
OPEN = "open"             # Section X. or Module X.
CLOSE = "close"           # End X.
OTHER = "other"           # Open Scope, Set, ...

ALWAYS_PROOF = {"Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark",
                "Property", "Example", "Goal"}
DECLARATIONS = ALWAYS_PROOF | {
    "Definition", "Fixpoint", "CoFixpoint", "Function", "Record", "Structure",
    "Inductive", "CoInductive", "Variant", "Class", "Scheme", "Combined"}
IMPLICIT_COMMANDS = {"Hint", "Instance", "Canonical", "Coercion", "Notation", "Infix",
                     "Ltac", "Ltac2", "Tactic", "Existing", "Add"}
LOCAL_COMMANDS = {"Variable", "Variables", "Hypothesis", "Hypotheses", "Context",
                  "Let", "Implicit", "Generalizable"}
ATTACHED_COMMANDS = {"Arguments", "Opaque", "Transparent", "Strategy", "Print", "Check",
                     "About", "Locate", "Compute", "Eval", "Search", "Typeclasses"}
PROOF_END = {"Qed", "Defined", "Admitted", "Abort", "Save"}
MODIFIERS = {"Local", "Global", "Polymorphic", "Monomorphic", "Program", "Private",
             "Cumulative", "NonCumulative"}
# Kinds of .glob references to a declaration, as opposed to a bound
# variable, a section variable ("var"), a Let ("vardef"), a library ("lib")
# or a module ("mod").
DECLARATION_REFERENCES = {"thm", "def", "abbrev", "inst", "proj", "rec", "constr", "ind",
                          "class", "meth", "coe", "scheme", "defax", "prfax", "variant",
                          "not", "syndef"}
IDENT = re.compile(rb"[A-Za-z_][A-Za-z0-9_']*")
# .glob files do not record the definition of constructors.
RECORD_CONSTRUCTOR = rb":=\s*([A-Za-z_][\w']*)\s*\{"
INDUCTIVE_CONSTRUCTOR = rb"(?:\||:=)\s*([A-Za-z_][\w']*)"
CONSTRUCTORS = {"Record": RECORD_CONSTRUCTOR, "Structure": RECORD_CONSTRUCTOR,
                "Class": RECORD_CONSTRUCTOR, "Inductive": INDUCTIVE_CONSTRUCTOR,
                "Variant": INDUCTIVE_CONSTRUCTOR, "CoInductive": INDUCTIVE_CONSTRUCTOR}


def namespace(kind):
    """Notations (Notation x := ...) and definitions have separate names."""
    return "abbrev" if kind == "abbrev" else "term"


def skip_string(data, i):
    """Position after the string literal that starts at i."""
    i += 1
    while i < len(data):
        if data[i] == 0x22:
            if data.startswith(b'""', i):
                i += 2
                continue
            return i + 1
        i += 1
    return len(data)


def skip_comment(data, i):
    """Position after the comment that starts at i. Comments nest, and a
    string in a comment is read as a string, as Rocq's lexer does."""
    depth = 0
    while i < len(data):
        if data.startswith(b"(*", i):
            depth += 1
            i += 2
        elif data.startswith(b"*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        elif data[i] == 0x22:
            i = skip_string(data, i)
        else:
            i += 1
    return len(data)


def lex(data):
    """The code of a source and its comments: data with comments and strings
    replaced by blanks, and the ranges [start, end) of its comments."""
    out, comments, i = bytearray(data), [], 0
    while i < len(data):
        if data.startswith(b"(*", i):
            j = skip_comment(data, i)
            comments.append((i, j))
        elif data[i] == 0x22:
            j = skip_string(data, i)
        else:
            i += 1
            continue
        out[i:j] = b" " * (j - i)
        i = j
    return bytes(out), comments


def sentences(code):
    """The sentences of a source, given its code, as ranges [start, end):
    from the first character that is not blank to the period that ends the
    sentence. Bullets and braces stay with the sentence that follows them."""
    out, start = [], None
    for i, c in enumerate(code):
        if c in BLANK:
            continue
        if start is None:
            start = i
        if c == 0x2E and (i + 1 == len(code) or code[i + 1] in BLANK) and code[i - 1] != 0x2E:
            out.append((start, i + 1))
            start = None
    return out


def command(code):
    """The first words of a sentence without bullets, braces, attributes and
    locality modifiers: the command and its first arguments."""
    text = code.decode(errors="replace")
    while True:
        text = text.lstrip(" \t\r\n-+*{}")
        if text.startswith("#["):
            text = text[text.find("]") + 1:]
            continue
        words = text.split(None, 1)
        if words and words[0] in MODIFIERS:
            text = words[1] if len(words) > 1 else ""
            continue
        return text.split()[:3]


class Container:
    """A module file, or a section or a module inside one."""

    def __init__(self, module, name, parent, is_module):
        self.module, self.name, self.parent, self.is_module = module, name, parent, is_module
        self.blocks = []

    def path(self):
        """The module path inside the file, as .glob files write it."""
        names, container = [], self
        while container.parent is not None:
            if container.is_module:
                names.append(container.name)
            container = container.parent
        return ".".join(reversed(names)) or "<>"


class Block:
    """A sentence, or a declaration with its proof."""

    def __init__(self, module, start, end, words):
        self.module, self.start, self.end, self.words = module, start, end, words
        self.keyword = words[0].rstrip(".") if words else ""
        self.kind = OTHER
        self.names = []        # (module path, name, kind) of what it declares
        self.container = None  # where it is; for Section X. and End X., X
        self.targets = set()   # the blocks that it refers to
        self.mentions = []     # (start, end, container) of the modules it names


class Module:
    """A module of theories/: its source, its blocks and its .glob file."""

    def __init__(self, name, path):
        self.name, self.path = name, path
        self.data = path.read_bytes()
        self.code, comments = lex(self.data)
        self.comment_starts = {end: start for start, end in comments}
        self.file = Container(name, name, None, True)
        self.blocks = []
        self.requires = set()   # the modules of theories/ that it requires
        self.definitions = []   # (kind, start, end, module path, name)
        self.references = []    # (start, end, module, module path, name, kind)
        self.split()
        self.read_glob(path.with_suffix(".glob"))

    def split(self):
        spans = sentences(self.code)
        stack, i = [self.file], 0
        while i < len(spans):
            start, end = spans[i]
            words = command(self.code[start:end])
            block = Block(self.name, start, end, words)
            keyword, container = block.keyword, stack[-1]
            if keyword.startswith("HB."):
                block.kind = IMPLICIT
            elif keyword in DECLARATIONS | IMPLICIT_COMMANDS | LOCAL_COMMANDS:
                block.kind = (DECL if keyword in DECLARATIONS else
                              IMPLICIT if keyword in IMPLICIT_COMMANDS else LOCAL)
                after = command(self.code[slice(*spans[i + 1])]) if i + 1 < len(spans) else []
                if keyword in ALWAYS_PROOF or (after and after[0].rstrip(".") == "Proof"):
                    while i + 1 < len(spans):
                        i += 1
                        words = command(self.code[slice(*spans[i])])
                        if words and words[0].rstrip(".") in PROOF_END:
                            break
                    block.end = spans[i][1]
            elif keyword in ATTACHED_COMMANDS:
                block.kind = ATTACHED
            elif keyword == "Require" or (keyword == "From" and "Require" in words):
                block.kind = REQUIRE
            elif keyword in ("Import", "Export"):
                block.kind = IMPORT
            elif keyword in ("Section", "Module") and b":=" not in self.code[start:end]:
                block.kind = OPEN
                name = [w for w in words[1:] if w not in ("Import", "Export")][0]
                container = Container(self.name, name.rstrip("."), stack[-1],
                                      keyword == "Module")
                stack.append(container)
            elif keyword == "End" and len(stack) > 1:
                block.kind = CLOSE
                container = stack.pop()
            block.container = container
            container.blocks.append(block)
            self.blocks.append(block)
            i += 1

    def read_glob(self, path):
        for line in path.read_text(errors="replace").splitlines():
            parts = line.split()
            if line.startswith("R"):
                start, end = map(int, parts[0][1:].split(":"))
                self.references.append((start, end + 1, *parts[1:]))
            elif len(parts) == 4 and ":" in parts[1] and not line.startswith("binder"):
                start, end = map(int, parts[1].split(":"))
                self.definitions.append((parts[0], start, end + 1, parts[2], parts[3]))

    def block_at(self, position):
        """The block that contains position, or None."""
        low, high = 0, len(self.blocks)
        while low < high:
            middle = (low + high) // 2
            if self.blocks[middle].end <= position:
                low = middle + 1
            else:
                high = middle
        if low < len(self.blocks) and self.blocks[low].start <= position:
            return self.blocks[low]
        return None


class Analysis:
    def __init__(self, root, keep=()):
        self.root = root
        self.project = (root / "_CoqProject").read_text()
        # A module in a folder of theories/, theories/A/B.v, is named A.B, as
        # its logical name EllipsoidFitting.A.B.
        files = re.findall(r"^theories/([\w/]+)\.v\s*$", self.project, re.M)
        self.modules = {f.replace("/", "."): Module(f.replace("/", "."), root / "theories" / f"{f}.v")
                        for f in files}
        self.index = defaultdict(list)    # (module, module path, name, namespace)
                                          # -> the blocks that declare it, in order
        self.lets = defaultdict(list)     # (module, name) -> blocks of Let name
        self.ltacs = defaultdict(list)    # name -> blocks of Ltac name
        self.containers = {}              # (module, module path) -> container
        self.warnings = []
        self.index_declarations()
        self.resolve_references()
        self.add_ltac_references()
        self.used, self.live = self.reach(keep)

    def index_declarations(self):
        for module in self.modules.values():
            for kind, start, end, path, name in module.definitions:
                block = module.block_at(start)
                if block is None:
                    self.warnings.append(f"{module.name}: {kind} {name} is in no sentence")
                elif kind == "var" and block.keyword == "Let":
                    self.lets[(module.name, name)].append(block)
                elif kind not in ("var", "sec", "mod"):
                    block.names.append((path, name, kind))
                    self.index[(module.name, path, name, namespace(kind))].append(block)
            self.containers[(module.name, "<>")] = module.file
            for block in module.blocks:
                if block.kind == OPEN and block.container.is_module:
                    self.containers[(module.name, block.container.path())] = block.container
                elif block.keyword == "Ltac" and len(block.words) > 1:
                    self.ltacs[block.words[1]].append(block)
                elif block.keyword in CONSTRUCTORS:
                    text = module.code[block.start:block.end]
                    for name in re.findall(CONSTRUCTORS[block.keyword], text):
                        key = (module.name, block.container.path(), name.decode(), "term")
                        self.index[key].append(block)

    def resolve_references(self):
        for module in self.modules.values():
            for start, end, target, path, name, kind in module.references:
                block = module.block_at(start)
                if block is None or not target.startswith(PREFIX):
                    continue
                other = target[len(PREFIX):]
                if other not in self.modules:
                    self.warnings.append(f"{module.name}: {target} is not in _CoqProject")
                elif kind in ("lib", "mod"):
                    if kind == "lib":
                        module.requires.add(other)
                    container = self.containers.get((other, path))
                    if container is None:
                        self.warnings.append(f"{module.name}: unknown module {target} {path}")
                    else:
                        block.mentions.append((start, end, container))
                elif kind == "vardef":
                    lets = [let for let in self.lets[(other, name)]
                            if self.inside(block, let.container)]
                    block.targets.update(lets[-1:])
                elif kind in DECLARATION_REFERENCES and ":" not in name:
                    # name:3 is the recursive call of a Fixpoint being defined.
                    found = self.declaration(other, path, name, namespace(kind),
                                             start if other == module.name else None)
                    if found is None:
                        self.warnings.append(f"{module.name}: unresolved {kind} {target}.{name}")
                    elif found is not block:
                        block.targets.add(found)

    def declaration(self, module, path, name, space, position=None):
        """The block that declares a name: the last one before position, if
        the reference is at position in the same module, or else the last one.
        A notation (Notation x := ...) may reuse the name of a definition, and
        notations of different sections may have the same name."""
        blocks = self.index.get((module, path, name, space), [])
        before = [b for b in blocks if position is None or b.start <= position]
        return (before or blocks or [None])[-1]

    @staticmethod
    def inside(block, container):
        inner = block.container
        while inner is not None and inner is not container:
            inner = inner.parent
        return inner is container

    def closure(self, name, seen=None):
        """name and the modules that it requires, directly or not."""
        seen = set() if seen is None else seen
        if name not in seen:
            seen.add(name)
            for other in self.modules[name].requires:
                self.closure(other, seen)
        return seen

    def add_ltac_references(self):
        if not self.ltacs:
            return
        for module in self.modules.values():
            visible = self.closure(module.name)
            for block in module.blocks:
                for word in set(IDENT.findall(module.code[block.start:block.end])):
                    for ltac in self.ltacs.get(word.decode(), ()):
                        if ltac is not block and ltac.module in visible and (
                                ltac.module != module.name or ltac.start < block.start):
                            block.targets.add(ltac)

    def reach(self, keep):
        """The used blocks, and the containers that contain one."""
        roots = [block for path in FROZEN for block in self.modules[Path(path).stem].blocks]
        for entry in keep:
            # the longest prefix of entry that names a module
            parts = entry.split(".")
            k = next((k for k in range(len(parts), 0, -1)
                      if ".".join(parts[:k]) in self.modules), 1)
            module, name = ".".join(parts[:k]), ".".join(parts[k:])
            path, _, name = name.rpartition(".")
            if module not in self.modules:
                self.warnings.append(f"--keep: unknown module {module}")
            elif not name:
                roots.extend(self.modules[module].blocks)
            else:
                found = [self.declaration(module, path or "<>", name, space)
                         for space in ("term", "abbrev")]
                if found == [None, None]:
                    self.warnings.append(f"--keep: unknown declaration {entry}")
                roots.extend(block for block in found if block is not None)
        used, live, stack = set(), set(), roots

        def enter(container):
            while container is not None and container not in live:
                live.add(container)
                stack.extend(b for b in container.blocks if b.kind not in (DECL, ATTACHED, IMPORT))
                container = container.parent

        while stack:
            block = stack.pop()
            if block not in used:
                used.add(block)
                enter(block.container)
                stack.extend(block.targets)
        return used, live

    def kept(self, block):
        """Whether the block stays in the trimmed tree."""
        if block.container not in self.live:
            return False
        if block.kind == DECL:
            return block in self.used
        if block.kind == ATTACHED:
            return block.targets <= self.used and all(c in self.live for _, _, c in block.mentions)
        if block.kind in (REQUIRE, IMPORT) and block.mentions:
            return any(c in self.live for _, _, c in block.mentions)
        return True

    def unused_modules(self):
        return [module for module in self.modules.values() if module.file not in self.live]

    def unused_declarations(self):
        for module in self.modules.values():
            for block in module.blocks:
                if block.kind == DECL and not self.kept(block):
                    for path, name, kind in block.names:
                        if kind != "proj":
                            yield ".".join([module.name] + [path] * (path != "<>") + [name])

    # Writing the trimmed tree.

    def trimmed(self, module):
        """The source of a used module without what is unused, as bytes."""
        edits = []
        first = module.blocks[0].start if module.blocks else 0
        for block in module.blocks:
            if not self.kept(block):
                edits.append((*self.extent(module, block, first), b""))
            elif block.kind in (REQUIRE, IMPORT) and any(
                    c not in self.live for _, _, c in block.mentions):
                edits.append((block.start, block.end, self.without_names(module, block)))
        return self.apply(module.data, edits)

    def without_names(self, module, block):
        """A Require or Import command without the modules that are not used,
        each line keeping its indentation."""
        dead = {(s, e) for s, e, c in block.mentions if c not in self.live}
        lines, position = [], block.start
        for line in module.data[block.start:block.end - 1].split(b"\n"):
            words = [(position + m.start(), position + m.end()) for m in re.finditer(rb"\S+", line)]
            kept = [module.data[s:e] for s, e in words if (s, e) not in dead]
            if kept:
                indent = re.match(rb"[ \t]*", line).group() if lines else b""
                lines.append(indent + b" ".join(kept))
            position += len(line) + 1
        return b"\n".join(lines) + b"."

    @staticmethod
    def extent(module, block, first):
        """The range to delete for a block: whole lines when the block has
        them to itself, and the comments just above it that are not
        separated from it by a blank line. The header of the file, before
        its first sentence, stays."""
        data = module.data
        start, end = block.start, block.end
        while True:
            line = data.rfind(b"\n", 0, start) + 1
            if data[line:start].strip():
                break
            start = line
            above = data.rfind(b"\n", 0, max(line - 1, 0)) + 1
            if line == 0 or not data[above:line - 1].rstrip().endswith(b"*)"):
                break
            comment = module.comment_starts.get(data.rfind(b"*)", 0, line - 1) + 2)
            if comment is None or comment < first or \
                    data[data.rfind(b"\n", 0, comment) + 1:comment].strip():
                break
            start = comment
        newline = data.find(b"\n", end)
        if newline >= 0 and not data[end:newline].strip():
            end = newline + 1
        return start, end

    @staticmethod
    def apply(data, edits):
        """data with the edits (start, end, replacement) made, and at most one
        blank line where something was deleted."""
        out, position, junctions = bytearray(), 0, []
        for start, end, replacement in sorted(edits):
            start = max(start, position)
            out += data[position:start]
            out += replacement
            if not replacement:
                junctions.append(len(out))
            position = max(end, start)
        out += data[position:]
        limit = len(out) + 1
        for junction in reversed(junctions):
            if junction >= limit:
                continue
            left = junction
            while left > 0 and out[left - 1] in BLANK:
                left -= 1
            right = junction
            while right < len(out) and out[right] in BLANK:
                right += 1
            if out[left:right].count(b"\n") > 2 or right == len(out):
                indent = out[out.rfind(b"\n", left, right) + 1:right]
                out[left:right] = b"\n" if right == len(out) else b"\n\n" + indent
            limit = left
        return bytes(out)

    def write(self, target):
        removed = {module.name for module in self.unused_modules()}
        for module in self.modules.values():
            path = target / "theories" / (module.name.replace(".", "/") + ".v")
            if module.name in removed:
                for suffix in (".v", ".vo", ".vos", ".vok", ".glob"):
                    path.with_suffix(suffix).unlink(missing_ok=True)
                path.with_name(f".{path.stem}.aux").unlink(missing_ok=True)
                continue
            text = self.trimmed(module)
            if not path.exists() or path.read_bytes() != text:
                path.write_bytes(text)
        project = "".join(line for line in self.project.splitlines(keepends=True)
                          if re.sub(r"^theories/([\w/]+)\.v\s*$", r"\1", line).replace("/", ".")
                          not in removed)
        path = target / "_CoqProject"
        if path.read_text() != project:
            path.write_text(project)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=ROOT,
                        help="repository to analyze (default: this one)")
    parser.add_argument("--keep", type=Path, help="file of declarations to treat as used")
    parser.add_argument("--modules", action="store_true",
                        help="list the modules that nothing used depends on")
    parser.add_argument("--delete", type=Path, metavar="DIR",
                        help="write the tree without what is unused to the repository DIR")
    args = parser.parse_args()
    keep = args.keep.read_text().split() if args.keep else []
    analysis = Analysis(args.root.resolve(), keep)
    for line in analysis.warnings:
        print("warning:", line, file=sys.stderr)
    if args.delete:
        analysis.write(args.delete.resolve())
    elif args.modules:
        for module in analysis.unused_modules():
            print(module.name)
    else:
        for name in analysis.unused_declarations():
            print(name)


if __name__ == "__main__":
    main()
