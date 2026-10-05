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
2. **Make the proof of the paper use the library and shrink it.** Re-prove
   the special-case lemmas of `theories/` from library results at Stdlib's
   `R`, delete what is no longer used, remove notes about how the files
   were produced from comments, fix the deprecation warnings, and at the end
   rename the remaining modules and group them in folders.

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
   `Rstruct` or `Rstruct_topology`.

**Frozen files.** Eight files are frozen: `MainStatement.v`,
`MainTheorem.v`, `PaperMainResults.v`, and the five definition modules of
the statement: `PaperMainDefinitions.v`,
`GaussianProbabilityProductDefinitions.v`,
`GaussianProbabilityDefinitions.v`, `GaussianDefinitions.v` and
`AnalysisIntegralDefinitions.v`. The user reviewed the statement and these
definitions against the paper. Their code must not change: not a
definition, not a name, not an import. Only agent 1 may edit their
comments. The files of `check/`, `scripts/check_sources.py` and
`scripts/export_from_ellipsoid_rocq.py` (whose comment stripper the check
imports) do not change either. Only the user changes `check/frozen-baseline`.

`PaperMainResults.v` imports two lane C modules and uses one theorem of
each: `paper_main_results_from_conditioned` of `PaperMainFinalAssembly` and
`paper_main_conditioned_limit` of `PaperMainConditionedLimit`. These two
module names and these two theorems keep their names and statements in
every phase. Their proofs may change.

Only these eight files are frozen here. Comments in `theories/` that call a
module "frozen", "trusted" or part of a "challenge" describe the protocol of
the source repository and do not apply.

If the work seems to require changing a frozen file, stop and ask the user.

## Ownership

Each file belongs to one lane, and an agent edits only the files of its own
lane.

| Lane | Agent | Library directories | Modules of `theories/` | Size at the start |
|---|---|---|---|---|
| A | 1 | `library/gaussian/` | every module whose name does not start with `PaperMain`, except the frozen files | 253 modules, 41,600 lines |
| B | 2 | `library/comparison/` | `PaperMain` followed by `Gaussian`, `Gordon`, `Geometry`, `Cone`, `Measurability`, `Projection`, `Projected`, `Hybrid`, `Polynomial`, `Sampling`, `Pinching` or `Feature` | 192 modules, 34,600 lines |
| C | 3 | `library/matrix/`, `library/probability/` | every other `PaperMain` module, except the frozen files | 196 modules, 39,100 lines |

No lane A module requires a lane B or C module: lane A is the base layer.
Lanes B and C require lane A heavily (961 and 568 direct requires, on 104
lane A modules).

`library/README.md` gives the topic of each library directory. Each lane
edits only its own rows of the table of main results there. Agent 1 alone
edits `_CoqProject`, `Makefile`, `README.md`, the CI, the comments of the
frozen files and the rest of `library/README.md`, and merges the lanes. To
add or remove a module, ask agent 1.

**Requests.** To ask another lane for something (a lemma in its library
files, a change to one of its modules), add an entry to
`requests/<your lane>-to-<their lane>.md`. That file belongs to you. The
owner answers in a commit message that names the request, by doing it or
by explaining why not; you then delete the answered entry. Agent 1 deletes
`requests/` in phase 3.

## Git

All clones live on the VM and share one local bare repository, the hub
(for example `/srv/ellipsoid-fitting/hub.git`; the user creates it). There
is no other remote.

- Each agent clones the hub and works in its own clone, on its lane branch:
  `lane/a`, `lane/b` or `lane/c`. It pushes only that branch, and only to
  the hub.
- Agent 1 merges in a separate integration clone, not in its lane clone, so
  that merging does not invalidate its lane build. Agent 1 alone pushes
  `main` and tags to the hub.
- To use the work of other lanes, merge `main` from the hub into your lane
  branch.
- Never push anywhere else, and never create another remote, unless the
  user asks.
- Commit messages say what changed in plain words ("State and prove
  Gordon's comparison inequality for finite index sets"), not how the
  tools were driven.
- Keep generated files out of commits (`.gitignore` lists them).
- Do not add journals, progress reports or logs to the repository. Put
  what a reviewer needs in the commit message, and the main results in
  `library/README.md`.

## Phases

**Phase 1. Agent 1 alone; the others wait.**

1. Compute which declarations the main theorem uses. Build, then read the
   `.glob` files: they record every reference with its position, so each
   reference can be attributed to the declaration that contains it. Treat
   as used everything that a `Hint`, `Instance`, `Canonical`,
   `HB.instance`, `Coercion`, `Notation` or `Ltac` command mentions, since
   a proof can use those without naming them. Commit the script as
   `scripts/unused.py`. Its output is a list of candidates, not a proof of
   non-use: the build decides.
2. Delete the modules that nothing used depends on, and remove them from
   `_CoqProject`. Then delete the unused declarations of all lanes in one
   scripted pass, with the build as arbiter: restore whatever a failed build
   needs, and repeat until `make check` passes. Doing this once, centrally,
   avoids the cross-lane breakage of lane-by-lane deletions.
3. Re-run the analysis and commit its output as `unused.txt`, one
   `Module.name` per line. It now lists only the surviving declarations
   that the analysis calls unused.
4. Update the "Where the proof comes from" section of `README.md`: the
   export script reproduces commit `29df54e`, not the current tree.
   Deleted code stays in the history, so a lane can recover a general
   result from `29df54e`.
5. Run `make check`, commit, push `main`, and tag the commit `phase1`.

**Phase 2. Three lanes in parallel, each on its branch from `phase1`.**

In each lane, in order of priority:

- **Lane A.** First the core of `library/gaussian/`. MathComp-Analysis 1.16
  has the one-dimensional normal law (`normal_prob`), binary products with
  Fubini, and the sigma-algebra on tuples, but no measurable structure on
  row vectors, no n-fold product and no Gaussian vector. Define the
  standard Gaussian measure on `'rV[R]_n` (or `'cV[R]_n`; say in the file
  header why), prove that it is a probability measure, and prove, in
  `theories/`, that at Stdlib's `R` it agrees with `gaussian_product_law` of
  the frozen definitions. The tuple construction there is already generic
  in the real type, so the new work is the row-vector side and that bridge.
  Next, Gaussian integration by parts in several dimensions and Gaussian
  interpolation between two covariances: lane B's main results need them.
  Merge these to `main` as soon as each is complete.
- **Lane B.** Start with what needs only the one-dimensional law: tails,
  moment generating functions, chi-square laws. Then linear images and
  rotation invariance, Lipschitz concentration, and, once lane A has merged
  interpolation, the Slepian, Sudakov-Fernique and Gordon comparison
  inequalities, escape through a mesh and norms of Gaussian matrices.
- **Lane C.** None of its topics needs the Gaussian measure. MathComp's
  `spectral.v` works over a `numClosedFieldType`, and the real-closed
  package is not installed, so it gives no spectral theorem over a
  `realType`. Generalize the proof's own route instead
  (`PaperMainSymmetricDiagonalization`: an eigenvector from a maximum of
  the quadratic form on the unit sphere, then Householder reflections),
  which needs a `realType`, not an `rcfType`. Then operator and Frobenius
  norms, nets on spheres, Paley-Zygmund and other moment inequalities, and
  the Lindeberg replacement method.

In every lane, after a library result exists:

- Re-prove the special-case lemmas of your lane from it. **When such a
  lemma has users outside your lane, keep its name and statement and only
  change its proof.** Delete it only in phase 3. When all its users are in
  your lane, you may change them and delete it.
- Clean the comments of your lane and fix its warnings.
- Do not rename or move modules of `theories/` in this phase. Write
  proposed renames and merges to `renames/<lane>.tsv`, one `old<TAB>new`
  per line (a merge is several old names with one new name).

**Rebuild cost.** A lane A module has a median of 226 modules that depend
on it, and 80 have more than 300. Every lane A change that reaches `main`
makes lanes B and C recompile most of `theories/`. So:

- Lane A leaves these twelve modules untouched, comments included, until
  the end of phase 2: `MatrixEuclideanProduct`, `MatrixDefinitions`,
  `SoftDefinitions`, `OperatorDefinitions`, `GibbsDefinitions`,
  `ThirdDefinitions`, `AnalysisBridge`, `AnalysisBridge2`,
  `TensorDefinitions`, `MatrixGibbsDefinitions`, `MatrixSecondDefinitions`
  and `MomentDefinitions` (400 or more dependents each).
- New modules go where few modules depend on them. Put the bridge between
  Stdlib's `R` and the library in a new module of `theories/` (below), not
  in `AnalysisBridge` or `AnalysisBridge2`.
- Agent 1 merges lane A into `main` at milestones (a library topic done
  and used), not after every commit.
- While iterating on a module, compile only it and what it requires, not
  what depends on it: `make theories/<Module>.vo` or
  `make library/<dir>/<file>.vo`. This does not replace `make check` before
  a commit. (Checking statements only, with `.vos` files, saves about 10
  percent here, so it is not offered.)

**End of phase 2.** Agent 1 ends phase 2 when the table of main results in
`library/README.md` covers every topic of its layout table and the three
lanes are merged, or earlier if the user says so.

**Phase 3. Agent 1 alone.**

1. Re-run the unused analysis on the merged tree, and delete what it finds
   with the build as arbiter, including special-case lemmas whose users
   outside their lane are gone.
2. Apply the renames, merges and folders of `renames/` in one scripted
   commit: file names, `From EllipsoidFitting Require` lines and
   `_CoqProject`. The frozen files, `PaperMainFinalAssembly` and
   `PaperMainConditionedLimit` keep their names.
3. Delete `requests/`, `renames/` and `unused.txt`. Update the "Planned
   work" section of `README.md`, and check that the table of main results
   in `library/README.md` is complete: it is what the user will review.
4. Run `make check`, commit and push `main`.

## Bridging Stdlib's `R` and the library

At Stdlib's `R`, MathComp's `+ - * / ^-1` are Stdlib's operations up to
unfolding. For the rest there are pointwise equations: `RleP`, `RltP`,
`RabsE`, `RsqrtE`, `RpowE`, `INRE`, `RmaxE` and `RminE` in `Rstruct`, and
`RexpE` and `RlnE` in `Rstruct_topology`. Lifted with `boolp.funext` (and
`propext` for `Rle` and `Rlt`), they become equalities of functions, such
as ``Rabs = (fun x : R => `|x|)``, that `rewrite` can use under binders.
Put these bridge lemmas in one new module of `theories/` (lane A). They
never go in `library/`.

## Building

- Use the switch `rocq-analysis` (Rocq 9.1.1, MathComp 2.6.0,
  MathComp-Analysis 1.16.0). Inside a container where those binaries are on
  `PATH`, use `make check ROCQ_SWITCH=`. Never install or upgrade packages;
  if one seems necessary, ask the user.
- On a 16-vCPU machine shared by three agents, use `JOBS=4`. On a Mac with
  16 cores and `JOBS=12`, a full build took 13 minutes; expect longer here.
- `make build` recompiles only what changed and what depends on it.
- Each agent has its own clone and its own build. Never share `.vo` files.
- `.mcp.json` starts `rocq-mcp-evolve` in the switch `rocq-analysis`. One
  agent owns one server session. A proof found interactively counts only
  once it is saved in the `.v` file and `make check` passes.

## Writing

Write plainly: short sentences, no em-dashes, no marketing, no emoji. Say
what was checked and how, and never claim more than the checks show.
