# Rules for agents

`CLAUDE.md` is a symbolic link to this file. Read it, then `README.md` and
`library/README.md`, before touching anything.

## The task

`theories/` holds a proof of the three main theorems of the paper
(`theories/MainStatement.v`, proved in `theories/MainTheorem.v`). It is a
faithful copy of a proof written by several agents in another repository.
It is untidy, and much of its mathematics is general but written for this
paper only: Gaussian vectors as lists of coordinates, Stdlib's `R`, names
prefixed `PaperMain`.

The task has two parts.

1. **Build a reusable library in `library/`** (logical root
   `GaussianAnalysis`). Take the general mathematics out of the proof,
   state it in general form over an arbitrary `R : realType`, in
   MathComp-Analysis style, and prove it, reusing the existing proofs where
   they help. Examples: Gaussian integration by parts, Gaussian
   interpolation, concentration of Lipschitz functions, Slepian and Gordon
   comparison, escape through a mesh, the spectral theorem for real
   symmetric matrices, nets on spheres, Paley-Zygmund. The user wants the
   library to be usable in other settings, and parts of it to be good
   enough for MathComp-Analysis. `library/README.md` gives its conventions.
   You choose the general statements; the user reviews them afterwards.
   Prefer the general form that a probabilist would state over the special
   case the paper needs.
2. **Make the proof of the paper use the library and shrink it.** Replace
   the special-case lemmas of `theories/` by instances of library results at
   Stdlib's `R`, delete what is no longer used, remove notes about how the
   files were produced from comments, fix the deprecation warnings, and at
   the end rename the remaining modules and group them in folders.

Three agents share the work. Agent 1 coordinates.

## The invariant

After every commit, `make check` passes. It builds every module of
`_CoqProject`, then runs `scripts/check_sources.py`, which checks:

1. the axioms of the main theorem are among the eight classical axioms of
   `check/assumptions.expected` (fewer is fine);
2. the frozen files are unchanged;
3. no module contains `Admitted`, `Axiom`, `Parameter` or `Conjecture`;
4. no module of `library/` requires a module of `theories/`, Stdlib's real
   analysis (`Reals`, `Lra`, `Psatz` and the others) or MathComp's
   `Rstruct`.

The frozen files are `MainStatement.v`, `MainTheorem.v`,
`PaperMainResults.v`, and the five definition modules of the statement:
`PaperMainDefinitions.v`, `GaussianProbabilityProductDefinitions.v`,
`GaussianProbabilityDefinitions.v`, `GaussianDefinitions.v` and
`AnalysisIntegralDefinitions.v`. The user reviewed the statement and these
definitions against the paper. Their code must not change: not a
definition, not a name, not an import. Only agent 1 may edit their
comments. The files of `check/` and `scripts/check_sources.py` do not change
either. Only the user changes `check/frozen-baseline`.

If the work seems to require changing a frozen file, stop and ask the user.

## Ownership

Each file belongs to one lane, and an agent edits only the files of its own
lane.

| Lane | Agent | Library directories | Modules of `theories/` | Size at the start |
|---|---|---|---|---|
| A | 1 | `library/gaussian/` | every module whose name does not start with `PaperMain`, except the frozen files | 253 modules, 41,600 lines |
| B | 2 | `library/comparison/` | `PaperMain` followed by `Gaussian`, `Gordon`, `Geometry`, `Cone`, `Measurability`, `Projection`, `Projected`, `Hybrid`, `Polynomial`, `Sampling`, `Pinching` or `Feature` | 192 modules, 34,600 lines |
| C | 3 | `library/matrix/`, `library/probability/` | every other `PaperMain` module, except the frozen files | 196 modules, 39,100 lines |

`library/README.md` gives the topic of each library directory. Each lane
edits only its own rows of the table of main results there.

Agent 1 alone edits `_CoqProject`, `Makefile`, `README.md`, the CI, the
comments of the frozen files and the rest of `library/README.md`, and merges
the lanes. To add or remove a module, ask agent 1. To ask another lane for
something (a lemma in its library files, a change to one of its modules),
write the request in `requests/<your lane>-to-<their lane>.md`; the owner
answers by doing it or by explaining why not, in a commit message.

## Phases

**Phase 1. Agent 1 alone; the others wait.**

1. Compute which declarations the main theorem uses. Build, then read the
   `.glob` files: they record every reference with its position, so each
   reference can be attributed to the declaration that contains it. Treat
   as used everything that a `Hint`, `Instance`, `Canonical`,
   `HB.instance`, `Coercion`, `Notation` or `Ltac` command mentions, since
   a proof can use those without naming them. The result is a list of
   candidates, not a proof of non-use: the build decides. Commit the script
   as `scripts/unused.py` and its output as `unused.txt`, one
   `Module.name` per line.
2. Delete the modules that nothing used depends on, and remove them from
   `_CoqProject`. Deleted code stays in the history: commit `29df54e` has
   the full copy, so a lane can recover a general result from there.
3. Write the core of `library/gaussian/`: the standard Gaussian measure on
   `'rV[R]_n` (or `'cV[R]_n`; choose one and say why in the file header),
   proved to be a probability measure, with its one-dimensional marginals.
   Prove, in `theories/`, that at Stdlib's `R` it agrees with
   `gaussian_product_law` of the frozen definitions, so that the paper can
   use the library. Lanes B and C build on this core.
4. Run `make check`, commit, and tag the commit `phase1`.

**Phase 2. Three lanes in parallel, each on a branch from `phase1`:
`lane/a`, `lane/b`, `lane/c`.**

For your lane, in this order of priority:

1. Write the library files of your topic. Start from the results that the
   paper's proof uses, stated in general form, and add the companion
   results a user of the library would expect next to them.
2. Change the modules of your lane in `theories/` to use them, and delete
   the special-case lemmas they replace.
3. Delete the declarations of your lane listed in `unused.txt`, clean the
   comments, fix the warnings.

Do not rename or move modules of `theories/` in this phase. Write proposed
renames and merges to `renames/<lane>.tsv`, one `old<TAB>new` per line (a
merge is several old names with one new name).

When a deletion breaks a module, restore the declaration and name it in the
commit message. Do not edit `unused.txt`: the three lanes would conflict on
it. Run `make check` before every commit. Agent 1 merges the lanes into
`main` regularly, one at a time, running `make check` after each merge, so
that each lane can use the library files of the others.

**Phase 3. Agent 1 alone, after the three lanes are merged.**

Apply the renames, merges and folders of `theories/` in one scripted
commit: file names, `From EllipsoidFitting Require` lines and `_CoqProject`.
The frozen files keep their names. Run `make check`. Then update the
"Planned clean-up" section of `README.md`, and check that the table of main
results in `library/README.md` is complete: it is what the user will review.

## Bridging Stdlib's `R` and the library

At Stdlib's `R`, MathComp's `+ - * / ^-1` are Stdlib's operations up to
unfolding. For the rest, `Rstruct` gives pointwise equations: `RleP`,
`RltP`, `RabsE`, `RsqrtE`, `RpowE`, `RexpE`, `RlnE`, `INRE`, `RmaxE`,
`RminE`. Lifted with `boolp.funext` (and `propext` for `Rle` and `Rlt`),
they become equalities of functions, such as
``Rabs = (fun x : R => `|x|)``, that `rewrite` can use under binders. Put
these bridge lemmas in one module of `theories/` (lane A). They never go in
`library/`.

## Building

- Use the switch `rocq-analysis` (Rocq 9.1.1, MathComp 2.6.0,
  MathComp-Analysis 1.16.0). Inside a container where those binaries are on
  `PATH`, use `make check ROCQ_SWITCH=`. Never install or upgrade packages;
  if one seems necessary, ask the user.
- On a 16-vCPU machine shared by three agents, use `JOBS=4`. On a Mac with
  16 cores and `JOBS=12`, a full build took 13 minutes; expect longer here.
- `make build` recompiles only what changed and what depends on it. A
  change to lane A recompiles most of `theories/`.
- Each agent has its own clone and its own build. Never share `.vo` files.
- `.mcp.json` starts `rocq-mcp-evolve` in the switch `rocq-analysis`. One
  agent owns one server session. A proof found interactively counts only
  once it is saved in the `.v` file and `make check` passes.

## Git

- Commit messages say what changed in plain words ("State and prove
  Gordon's comparison inequality for finite index sets"), not how the tools
  were driven.
- Keep generated files out of commits (`.gitignore` lists them).
- Do not push, and do not create remotes, unless the user asks.
- Do not add journals, progress reports or logs to the repository. Put
  what a reviewer needs in the commit message, and the main results in
  `library/README.md`.

## Writing

Write plainly: short sentences, no em-dashes, no marketing, no emoji. Say
what was checked and how, and never claim more than the checks show.
