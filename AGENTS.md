# Guide for contributors and agents

This guide is for the people and AI agents who change this repository;
`CLAUDE.md` is a symbolic link to it. Start with [README.md](README.md). "The
user" is the person who directs the project (see the glossary of
[doc/README.md](doc/README.md)). Until 25 October 2026 the AI agents followed
the rules now in [doc/history/agent-rules.md](doc/history/agent-rules.md);
source comments that cite "AGENTS.md, section Phase N" mean that file.

## For this project's own agents

This project's own agents are the AI agents that the user runs for this
project: the coordinator on the user's Mac and the agents that worked on the
VM. An AI agent working for anyone else is a contributor, to whom the next
sections apply.

- doc/history/agent-rules.md binds this project's agents, a session restarted
  later with `/resume` included, unless the user or this file says otherwise.
- This file takes precedence over doc/history/agent-rules.md wherever they
  differ. For documentation-only commits it replaces the rule that `make check`
  passes after every commit (section "The invariant") and the rules on which
  agent edits the documentation. It replaces every rule that makes the hub the
  reference repository or GitHub its mirror (section "Git", the bullet "Pushes"
  at the top, the push rules of phases 13 and 14).
- doc/history/agent-rules.md is out of date in places: the tag `shifted` was
  placed on 305747af on 24 October 2026, and `CLAUDE.md` links here.
- If a rule seems unclear, or two rules conflict, stop and ask the user.

## Status and contributions

This repository is a research artifact, maintained by Marc Lelarge (Inria).
Issue reports are welcome; responses may be delayed. Corrections to the
documentation are welcome. A pull request that changes only the paths of the
next section is checked as that section says. One that changes any other path
needs a `make check` run in the pinned image, which is not public: open an issue
first.

## The documentation exception

On 25 October 2026 the user made one narrow exception to the rule that
`make check` passes after every commit. A commit is documentation-only when
every path it changes is one of these:

- `README.md`, `AGENTS.md`, `CLAUDE.md`, `LICENSE`, `LICENSE-docs`, `NOTICE`,
  `CITATION.cff`, `CHANGELOG.md` and `.gitignore`;
- the deletion of `.mcp.json`;
- a file under `doc/` other than a PDF or a `.v` file;
- `library/README.md`, `extension/README.md` and `applications/README.md`.

Such a commit may be made on the coordinator's Mac and pushed to GitHub on the
user's word, without the full `make check`: the checker reads the content of
none of these paths. Its message says that the change is documentation only and
names the last commit on which `make check` passed, with its run identifier. Any
other change (a `.v` file, the `Makefile`, `_CoqProject`, `scripts/`, `check/`,
`.github/`, the opam file) is committed only after `make -f Makefile check`
passes in the pinned image on that exact tree. Its message gives the run
identifier, as in 5893184e. One exception: a change to the metadata fields of
the opam file may instead be approved by the user's written word on the exact
diff, named in the commit message, as for the metadata commit of October 2026.

Comments in `.v` files cite `doc/shifted-gaussian.tex`, `extension/README.md`
and `AGENTS.md` with its sections (now doc/history/agent-rules.md). Keep these
three paths and doc/history/agent-rules.md: do not move, rename or delete them.
PDFs stay outside git: a release PDF is built at the release's commit, and the
release notes give that commit and the PDF's SHA-256.

The exception keeps four checks: the source rules, the link check, the paper
build and the metadata validation. Before the push, check each new commit,
oldest first, in a fresh clone whose `origin` is GitHub, into which the new
commits are fetched (`git fetch <path of the clone that holds them> <branch>`),
then for each commit of `git rev-list --reverse origin/main..FETCH_HEAD`: set
`C` to its hash and run `git checkout --quiet --detach "$C"`. Then `python3 -I
-B scripts/check_sources.py --before-build` prints "the sources follow the rules
of scripts/check_sources.py"; if `CITATION.cff` changed, `cffconvert --validate
-i CITATION.cff` passes. These commands, in sh, bash or zsh, print nothing
(`--no-renames` lists both paths of a move):

```sh
changed=$(git diff --name-only --no-renames "$C^" "$C") || echo "guard: git diff failed for $C"
printf '%s' "$changed" | grep -v -E '^(README\.md|AGENTS\.md|CLAUDE\.md|\.mcp\.json|LICENSE|LICENSE-docs|NOTICE|CITATION\.cff|CHANGELOG\.md|\.gitignore|doc/.+|(library|extension|applications)/README\.md)$'
printf '%s' "$changed" | grep -q -x -F .mcp.json && git cat-file -e "${C}:.mcp.json" 2>/dev/null && echo ".mcp.json: only its deletion is allowed"
printf '%s' "$changed" | grep -E '\.(pdf|v)$'
for p in AGENTS.md doc/history/agent-rules.md doc/shifted-gaussian.tex extension/README.md; do git cat-file -e "${C}:${p}" 2>/dev/null || echo "missing: $p"; done
if printf '%s' "$changed" | grep -q -E '^doc/(paper/|statements\.bib$)'; then cmp -s doc/paper/statements.bib doc/statements.bib || echo "paper: the copy of statements.bib differs"
  (cd doc/paper && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper.tex >/dev/null 2>&1 && ! grep -E 'Warning|pdfTeX warning' build/paper.log build/paper.blg) || echo "paper: build failed or warned"; fi
git ls-files '*.md' | python3 -I -c 'import os, re, sys
[print(f, u) for f in sys.stdin.read().split() for u in re.findall(r"\]\(([^)\s#]+)", open(f, encoding="utf-8").read()) if ":" not in u and not os.path.exists(os.path.join(os.path.dirname(f), u))]'
```

## The repositories and the records

- Since 25 October 2026, GitHub (`LLM4Rocq/ellipsoid_fitting_rocq`, branch
  `main`) is authoritative; nothing is pushed there without the user's word.
- The former hub, `/srv/ellipsoid-fitting/hub.git` on the VM, is an archive at
  5893184e; a bundle of all its branches and tags is preserved. A restarted
  session must not resume from any of its branches, `main` included, or from
  the clones on the VM (`agent1`, `agent2`, `agent3`, `integration`), which
  hold the old `AGENTS.md`. Start instead from a fresh clone of GitHub `main`.
- The GitHub workflow `build` has been disabled since 25 October 2026, and its
  file is kept. By the user's decision of 21 October 2026, CI is not release
  evidence until a CI on the pinned image is shown to pass.
- [doc/details.md](doc/details.md) describes the results, the checks and the
  provenance as they stood at 5893184e. The commit messages give the run
  identifiers. The private records of the project are not public: the user's
  decisions, the reviews, the release evidence and the preserved archives.

## The pinned image and the full check

`make check` runs in the pinned Docker image `ellipsoid-rocq:2026-10-01` (image
id `sha256:d28a2af774271dc1c3592aa423b064ae134a16bc22220ff5faf897b7aa9468fb`),
which is not public: Rocq 9.1.1, MathComp 2.6.0, MathComp-Analysis 1.16.0,
OCaml 5.3.0 and findlib 1.9.8. The checker compares the plugin it builds with
the one that wrote `check/identity/`, so elsewhere a run is expected to fail.
Inside the image, run `make -f Makefile check ROCQ_SWITCH= JOBS=3` with the
environment prefix of the subsection "The checker repair and the release" of
section "Phase 13" in doc/history/agent-rules.md, whose section "Building" has
the details. Use 4 CPUs and 12 GiB: with `JOBS=4` a fresh full build exceeds
12 GiB. The last run passed at 5893184e (run d8bb8f380183817de780a550701eabc6).
