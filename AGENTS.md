# Rules for agents

## Local shifted-Gaussian development, 16 October 2026

The user has authorized starting the shifted-Gaussian formal proof on the
Mac while VM access is unavailable. This isolated worktree is based on
e34ddcf and follows `../../reviews/shifted-gaussian-formalization-plan.md`.
This authorization permits new supporting modules for that plan; it does
not accept the pending checker repair or authorize a release, tag or push.
All historical frozen code and check machinery remain unchanged.

For this local session the coordinator assigns individual new files and
alone updates `_CoqProject` and documentation. Read the assignment before
editing; do not modify another worker's file. Compile with the pinned
`rocq-analysis` switch (Rocq 9.1.1), without sharing compiled objects from
other worktrees. General lemmas may be proved before their acceptance;
public application statements still require the planned review. No
unfinished proof may be retained as a proved result. Build and axiom
reports are development evidence, not phase 13 release acceptance.

Local ownership: this session owns `matrix/quadric_certificate.v`,
`probability/symmetric_shift.v` and `Shifted/GaussianInputs.v`. The separate
agent working in `/Users/lelarge/Recherche/Antoine/tmp/shifted-local` has
stopped its overlapping certificate prototype and owns the new generic
module `library/convex/image_projection.v` for changing-image projection
continuity. It delivers source for review and integration here. Its Rocq
9.2 diagnostics and edits to its isolated archive are not part of this
development: every integrated proof must compile on Rocq 9.1.1, without
copying compiled objects or altering the pinned toolchain.

The user has appointed this Codex session as local master while away.
The current separate assignments are `Shifted/ConditionGap.v` and `Shifted/ResidualCertificate.v` (master),
`Shifted/GaussianExports.v` and `Shifted/GaussianRows.v` (Gaussian worker),
`matrix/centered_correction.v` (matrix worker), and
`random_matrix/rademacher_series.v` (probability worker). The initial
three modules are complete. Continue with the accepted S1-S7 plan; the
master reviews interfaces and integrates complete proof chunks.

Checkpoint `436dafd` contains twelve supporting modules, verified by
`make check`, supplemental axiom reports and recursive kernel checking.
The next assignments are `Shifted/Translations.v`,
`Shifted/ConditionTranslation.v` and `matrix/centered_translation.v`
(master); `matrix/condition_perturbation.v` and
`Shifted/GaussianTargets.v` (Gaussian worker);
`random_matrix/isotropic_rows.v` (matrix worker);
`random_matrix/symmetric_reserve.v` (probability worker); and
`Shifted/ProjectionCertificate.v` (the separate projection agent).
The separate agent also delivered `convex/psd_residual.v` for integration.
Only source files are transferred; every module is compiled at its final
logical name in this worktree. Active draft files are not completed
results and must be finished and registered before the next checkpoint.

The Gaussian worker continues in `Shifted/GaussianTargetBounds.v`.
The separate projection agent has completed `analysis/infimum_measurability.v`
and `Shifted/TranslationError.v`, and owns the deterministic assembly in
`Shifted/ReserveCertificate.v`. The matrix worker's
`random_matrix/isotropic_rows.v` is complete; further law bridges are
assigned separately after its survey. The probability worker continues
the independent-product and centered-covariance bounds in
`random_matrix/symmetric_reserve.v`. The master reviews and registers
these completed modules and keeps their original source ownership.

Further assignments: `random_matrix/even_weights.v` and
`Shifted/GaussianSmallShift.v` belong to the master;
`Shifted/GaussianExistence.v` to the Gaussian worker;
`probability/isotropic_mixtures.v`, `Shifted/MixtureRows.v` and
`Shifted/MixtureAdjoint.v` to the matrix worker; and
`probability/independent_row_signs.v` to the separate projection agent.
The completed Gaussian matrix bounds remain owned by the matrix worker.

Checkpoint `ddb2a3a` contains the next seventeen supporting modules,
verified by a source-only full build, the historical checks and recursive
kernel checking. The next checkpoint assembles the Gaussian condition and
error limits and symmetric-mixture quadric exclusion. Its completed source
inventory is maintained outside the repository in
`../../reviews/shifted-runtime/local-checkpoint-03-progress.json`.

Current remaining ownership: the Gaussian worker owns
`probability/sign_shift_sample.v` and `Shifted/SignMixture.v`; the matrix
worker owns `Shifted/SparseTargets.v`; the probability worker owns
`Shifted/SparseRows.v`; the separate local agent owns
`analysis/family_reindexing.v`. The master handles sparse-existence
assembly, source review, registration, documentation and verified local
commits. Do not edit another owner's module or any historical checker,
frozen statement, or main-branch source. Only sources cross worktrees.

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

Three agents share the work. Agent 1 coordinates phases 1 to 5; in
phases 6 to 13, agent 3 coordinates (sections "Phase 6" to "Phase 13").

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

| Lane | Agent | Library directories | Modules of `theories/` | Size at the start | Phase 5: `library/` and `extension/` |
|---|---|---|---|---|---|
| A | 1 | `library/gaussian/` | every module whose name does not start with `PaperMain`, except the frozen files | 253 modules, 41,600 lines | `library/gaussian/`, `library/probability/`, `library/random_matrix/`; `extension/Model/`, `extension/Features/`, its files in `extension/Unsat/` and `extension/Sat/` |
| B | 2 | `library/comparison/` | `PaperMain` followed by `Gaussian`, `Gordon`, `Geometry`, `Cone`, `Measurability`, `Projection`, `Projected`, `Hybrid`, `Polynomial`, `Sampling`, `Pinching` or `Feature` | 192 modules, 34,600 lines | `library/comparison/`, `library/convex/`; `extension/Unsat/Regularized.v`, `extension/Gaussian/Subcritical.v`, its files in `extension/Sat/` |
| C | 3 | `library/matrix/`, `library/probability/` | every other `PaperMain` module, except the frozen files | 196 modules, 39,100 lines | `library/matrix/`, `library/fourier/`; `extension/Gaussian/` except `Subcritical.v`, `extension/Unsat/Ridge.v`, its files in `extension/Sat/` |

In phase 5 the last column applies, and the file tables of the section
"Phase 5" override it for single files. `extension/` has the logical root
`EllipsoidUniversality`. Its two statement files,
`UniversalityDefinitions.v` and `UniversalityStatement.v`, are frozen like
the eight frozen files of `theories/`: their code does not change
(`scripts/check_sources.py` compares it with commit `3c6afa1`), only agent
1 edits their comments, and if a proof seems to require a change, stop and
ask the user. `extension/UniversalityTheorem.v` is agent 1's.

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

All clones live on the VM, in `/srv/ellipsoid-fitting/`, and share one
local bare repository there, the hub `hub.git`. There is no other remote.

| Clone | Used by | tmux session |
|---|---|---|
| `agent1` | agent 1, for phase 1 and lane A | `arthur` |
| `integration` | agent 1, for merging | `arthur` |
| `agent2` | agent 2, for lane B | `marcol` |
| `agent3` | agent 3, for lane C | `lancelot` |

- Each agent works in its own clone, on its lane branch: `lane/a`,
  `lane/b` or `lane/c`. It pushes only that branch, and only to the hub.
- The hub refuses pushes that rewrite history. Merge; do not rebase or
  force-push commits that are on the hub.
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

Phases 1 to 12 below are done: tag `phase12` is at 9046883. The
current work is phase 13, described after phase 12.

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

## Phase 4. Fourier analysis and the Brascamp-Lieb inequality

Phases 1 to 3 are done (`main` 3998195). Phase 4 adds to `library/` the
tools behind the anti-concentration estimate of Koehler and Sohn (arXiv
2608.27372; on the VM `/srv/ellipsoid-fitting/papers/2608.27372/arxiv_v1.tex`,
Proposition 2.4 at lines 906-927, proved at lines 2531-2781), and then
that estimate itself. Every result is stated over an arbitrary
`R : realType` in the library's conventions, for other users of the
library: nothing in this phase mentions ellipsoid fitting, and nothing in
`theories/` or `extension/` changes. The feasibility study on the branch
`extension/feasibility` (`extension/README.md`, item S5) is the context;
that branch is not merged.

### The target

For a probability `mu` on `R` and `L > 0`, the Levy concentration
function is `Q(mu, L) = sup_a mu [a, a + L]`.

**Vector small-ball estimate.** Let `v, lambda, eps > 0`. There is a
constant `C = C(v, lambda, eps)` such that for all `n` and `m >= 1`, all
laws `mu_1, ..., mu_n` on `R` with `int x^2 dmu_i <= v` and
`Q(mu_i, lambda) <= 1 - eps`, all `w_1, ..., w_n : 'rV[R]_m` with
`sum_i w_i^T w_i >= I_m` as quadratic forms and `|w_i| <= rho`, all
`eta >= C rho` and all `z`,

    P(|sum_i xi_i w_i - z| <= eta sqrt m) <= (C eta)^m,

where `xi_1, ..., xi_n` are independent with laws `mu_1, ..., mu_n`
(`tuple_prod`). The paper assumes mean zero, variance one and
`E[xi^2 1_{|xi| <= M}] >= 1/2`, and gets `C = C(M)`: that is a corollary,
by the first half of its Lemma 3.5 (lines 2583-2611), which gives
`Q(mu, 1/8) <= 1 - c(M)`. The mean plays no role in the proof, and the
paper notes (line 950) that only such a scalar anti-concentration
hypothesis is used.

### The route

The paper's proof, with four changes that make it formalizable in
MathComp-Analysis 1.16, which has no characteristic function, no Fourier
transform, no convolution, no change of variables formula in several
dimensions, no complex numbers (`complex.v` is in the real-closed
package, not installed) and no Lebesgue measure on `'rV[R]_n`. It has
`fubini_tonelli`, `differentiation_under_integral`,
`integration_by_parts` on an interval, `lebesgue_regularity_outer`,
`dynkin_induction`, `hoelder`, `powR` and `poweR`, `cosD`, `sinD`,
`cos_max`, `continuous_cos`, `normal_pdf` and `integral_normal_pdf`,
`markov` and `chebyshev`.

1. **Characteristic functions without complex numbers.** For a law `mu`
   on `R`, `cf_re mu t = int cos (t x) dmu(x)` and
   `cf_im mu t = int sin (t x) dmu(x)`. The squared modulus
   `cf_re^2 + cf_im^2` is `int int cos (t (x - y)) dmu(x) dmu(y)`, the
   characteristic function of the symmetrized law (the law of `X - X'`).
   Products of characteristic functions are products of complex numbers
   written on real and imaginary parts, with `cosD` and `sinD`. For a law
   `nu` on `'rV[R]_m`, `cf nu theta` is the characteristic function of the
   law of `<x, theta>` at `1`.

2. **No Fourier inversion theorem is needed.** The density bound of Lemma
   3.8 (line 2677) is replaced by a bound on probabilities. For a law `nu`
   on `'rV[R]_m`, `Y` of law `nu`, an independent `G` of law `gauss m`,
   `sigma > 0` and a measurable `B`,

       P(Y + sigma G in B) <= (2 pi)^-m (int_{R^m} |cf nu|) Leb(B),

   because `E[exp(-|Y - y|^2 / (2 sigma^2))]` equals
   `(sigma^2 / (2 pi))^{m/2} int exp(-sigma^2 |theta|^2 / 2)
   (cos <theta, y> cf_re nu theta + sin <theta, y> cf_im nu theta) dtheta`
   (Fubini and the characteristic function of `gauss m`, which is
   `exp(-|theta|^2 / 2)`), and `P(Y + sigma G in B)` is
   `int_B E[g_sigma(Y - y)] dy` with `g_sigma` the density of
   `sigma G`. Letting `sigma -> 0` gives
   `P(Y in B) <= (2 pi)^-m (int |cf nu|) Leb(B)` for every closed ball
   `B`, from `P(sigma |G| > delta) -> 0` and the continuity of Lebesgue
   measure along `B + delta`. This is all the theorem needs. The
   inversion theorem (if `int |cf nu| < oo`, `nu` has the bounded
   continuous density `(2 pi)^-m int (cos <theta, y> cf_re nu theta +
   sin <theta, y> cf_im nu theta) dtheta`) follows from the same
   identity on boxes and `measure_rowbox_unique`; it is the last item
   of lane A, after the theorem.

3. **The Brascamp-Lieb inequality in Gaussian form, by the
   Ornstein-Uhlenbeck semigroup.** Ball's geometric form (Theorem 3.7,
   line 2660): for unit vectors `u_1, ..., u_n` of `'rV[R]_m` and
   `c_i > 0` with `sum_i c_i u_i^T u_i = I_m`, and measurable
   `f_i : R -> [0, oo]`,

       int prod_i f_i(<u_i, x>)^{c_i} dgauss_m(x) <= prod_i (int f_i dgauss_1)^{c_i}.

   The Lebesgue form of the paper follows by
   `f_i(t) = F_i(t) sqrt(2 pi) exp(t^2 / 2)`, since
   `sum_i c_i <u_i, x>^2 = |x|^2` and `sum_i c_i = m` (take the trace).
   Proof. For `f_i` bounded, continuous and bounded below by
   `delta > 0`, let `P_t f(x) = int f(exp(-t) x + sqrt(1 - exp(-2t)) z)
   dgauss_1(z)` (the Ornstein-Uhlenbeck semigroup, Mehler's formula) and
   `Lambda(t) = int prod_i (P_t f_i)(<u_i, x>)^{c_i} dgauss_m(x)`. Then
   `Lambda(t) -> prod_i (int f_i dgauss_1)^{c_i}` as `t -> oo` (dominated
   convergence), `Lambda(t) -> Lambda(0)` as `t -> 0` (continuity of
   `f_i`), and `Lambda' >= 0` on `(0, oo)`: with `g_i = P_t f_i` and
   `a_i = g_i' / g_i`, the generator identity
   `d/dt P_t f = (P_t f)'' - x (P_t f)'` and Gaussian integration by parts
   along `u_i` (from `gauss_ibp`, by linearity) give

       Lambda'(t) = int prod_j g_j(<u_j, x>)^{c_j} (sum_i c_i a_i^2 - |sum_i c_i a_i u_i|^2) dgauss_m(x),

   where `a_i` is evaluated at `<u_i, x>`; the bracket is nonnegative by
   Cauchy-Schwarz with the weights `c_i`, because
   `sum_i c_i <u_i, v>^2 = |v|^2` for every `v`. Then bounded measurable
   `f_i`, by the density of bounded continuous functions in
   `L^1(gauss_1)` (`lebesgue_regularity_outer` or `dynkin_induction` on
   the sets whose indicator is such a limit) and the continuity of the
   left side for it (`|a^c - b^c| <= |a - b|^c` for `0 < c <= 1`, then
   `hoelder`; the law of `<u_i, x>` under `gauss m` is `gauss 1`, by
   `gauss_mxdot`); then `delta -> 0` and monotone convergence. Barthe's
   transport proof is not an option: it needs the change of variables
   formula in `R^m`. The heat semigroup against Lebesgue measure would
   work but needs the limit `t -> oo` with a rescaling; the Gaussian
   form has no such step. The semigroup is built from the library:
   `normal_prob_lincomb` gives the invariance of `gauss 1`,
   `integral_gauss_shift` (Cameron-Martin) and `is_derive_Rintegral` the
   derivatives in `x` and `t` for a bounded measurable `f`, as
   `gauss_smoothing.v` does, and `normal_ibp` the generator identity.

4. **The Kolmogorov-Rogozin inequality under a second moment
   condition.** The paper cites the classical inequality (line 2543)
   without proof. Its Fourier proof is delicate: the characteristic
   function of a lattice law has modulus one at periodic points, and the
   proof controls the width of those peaks. The application has second
   moments, and with them Esseen's inequality on a small window
   suffices. Esseen: for every law `mu` on `R` and `T > 0`,

       Q(mu, 2 pi / T) <= (pi^2 / (4 T)) int_{-T}^{T} |cf mu t| dt,

   because `T (sin(T x / 2) / (T x / 2))^2 = int_{-T}^{T} (1 - |t| / T)
   cos(t x) dt` (integration by parts) and the left side is at least
   `4 T / pi^2` on `|x| <= pi / T` (`sin y / y >= 2 / pi` on
   `[0, pi / 2]`). Sums: for independent `X_1, ..., X_N` of laws `mu_k`
   with `int x^2 dmu_k <= v` and `Q(mu_k, lambda) <= 1 - eps`, the law
   of `S_N = sum_k X_k` satisfies, for every `L > 0`,

       Q(S_N, L) <= C (L + sqrt(v / eps)) / (lambda sqrt(eps N))

   with an absolute constant `C` (`C = pi^2 sqrt(8 pi) / 2` works).
   Proof: the symmetrization `X~_k` has `P(lambda / 2 <= |X~_k| <= R) >=
   eps / 2` for `R^2 = 4 v / eps` (`P(|X~_k| < lambda / 2) <=
   Q(mu_k, lambda)` and Chebyshev), so for `|t| <= pi / R`,
   `1 - |cf mu_k t|^2 = E(1 - cos(t X~_k)) >= t^2 lambda^2 eps / (4 pi^2)`
   by `1 - cos u >= 2 u^2 / pi^2` on `|u| <= pi`; hence
   `|cf S_N t| <= exp(-N t^2 lambda^2 eps / (8 pi^2))` there, Esseen with
   `T = pi / R` bounds `Q(S_N, 2 R)`, and
   `Q(S_N, L) <= (L / (2 R) + 1) Q(S_N, 2 R)`. The classical inequality
   without moments is not part of this phase.

With these, the paper's Lemma 3.5 (lines 2565-2578) reads: for `mu` with
`int x^2 dmu <= v` and `Q(mu, lambda) <= 1 - eps`, and `0 < r <= s <= 1/2`,

    (1 / r) int_R |cf mu u|^{1 / r^2} exp(-s^2 u^2 / (2 r^2)) du <= C(v, lambda, eps),

proved as in the paper: `|cf mu u|^{1 / r^2} <= |cf mu u|^{2 N}` with
`N = floor(1 / (2 r^2)) >= 1 / (4 r^2)`, which is the characteristic
function of a sum `S_N` of `N` independent copies of the symmetrized law;
`int cf S_N (u) exp(-u^2 / 2) du = sqrt(2 pi) E[exp(-S_N^2 / 2)]` by
Fubini and the Gaussian characteristic function;
`E[exp(-S^2 / 2)] <= 2 (sum_{k >= 0} exp(-k^2 / 2)) Q(S, 1)` by cutting
`R` into unit intervals; and `Q(S_N, 1) <= C' / sqrt N <= 2 C' r` by
point 4. Lemma 3.8 (line 2677) then bounds `int_{R^m} |cf nu|` by `C^m`
for the law `nu` of `sum_i xi_i w_i + s G` with `sum_i w_i^T w_i = I_m`
and `s = max_i |w_i| <= 1/2`, by point 3 in Lebesgue form with
`u_i = w_i / |w_i|`, `c_i = |w_i|^2` and
`F_i(t) = |cf mu_i (|w_i| t)|^{1 / c_i} exp(-s^2 t^2 / 2)`; point 2 and
`Leb(B_m(r)) <= (2 pi e / m)^{m/2} r^m` (from
`1_{|x| <= r} <= exp(m (r^2 - |x|^2) / (2 r^2))` and the Gaussian
integral) give `P(|sum_i xi_i w_i + s G - z| <= 2 eta sqrt m) <=
(C eta)^m`. The theorem follows as at lines 2733-2781: whitening by a
matrix `W` with `W Sigma W^T = I_m` and `|x W| <= |x|`
(`symmetric_spectral`), then `P(s |G| <= eta sqrt m) >= 1/2`
(Chebyshev, `eta >= C rho >= C s`) and independence to remove `G`.

### Files, owners and results

The directory `library/fourier/` is new. Lane C owns it, except the two
files of lane A listed here. The other directories keep their owners.
Line counts are estimates of new Rocq, plus or minus fifty percent.

| File | Lane | Results | Reuses | Lines |
|---|---|---|---|---|
| `fourier/charfun.v` | C | `cf_re`, `cf_im`, `cf_norm` of a law on `R`; modulus at most one; continuity in `t`; the law of `a X + b`; the squared modulus as the characteristic function of the symmetrized law; for independent `X_1, ..., X_N` (`tuple_prod`) and reals `a_k`, the real and imaginary parts of `cf` of `sum_k a_k X_k` as the complex product of the `cf mu_k (a_k t)`, so the modulus is the product of moduli; `cf (normal_prob m s)`: `exp(-s^2 t^2 / 2) cos(m t)` and `exp(-s^2 t^2 / 2) sin(m t)` (`normal_ibp` and the differential equation `y' = -t y`, or `differentiation_under_integral`) | `tuple_prod`, `Rintegral_tuple_prodS`, `normal_ibp`, `normal_prob_affine`, `trigo.v` | 700 |
| `fourier/esseen.v` | C | `conc_fun mu L` (`Q`); at most one, monotone in `L`, `Q(mu, k L) <= k Q(mu, L)`; adding an independent variable does not increase it; `P(|X - X'| < lambda / 2) <= Q(mu, lambda)` for the symmetrization; the integral of the triangle kernel; Esseen's inequality; the inequality for sums of point 4 | `charfun.v`, `integration_by_parts`, `fubini_tonelli` | 900 |
| `fourier/gauss_factor.v` | C | `Q(mu, 1/8) <= 1 - c(M)` from mean zero, variance one and `E[x^2 1_{|x| <= M}] >= 1/2` (Lemma 3.5, first half); `E[exp(-S^2 / 2)] <= C Q(S, 1)`; the Gaussian Fubini identity `int cf_re nu (u) exp(-u^2 / 2) du = sqrt(2 pi) E[exp(-X^2 / 2)]`; the bound of Lemma 3.5 displayed above | `esseen.v`, `charfun.v`, `integral_normal_pdf` | 700 |
| `matrix/real_spectral.v` or a new `matrix/whitening.v` | C | for a symmetric `Sigma` with `x Sigma x^T >= |x|^2` for all `x`, a `W` with `W Sigma W^T = I` and `|x W| <= |x|` (`W = P^T diag(d)^{-1/2}` from the spectral decomposition) | `symmetric_spectral`, `spectral_psd` | 300 |
| `gaussian/lebesgue_rV.v` | A | `lebesgue_rV n`, Lebesgue measure on `'rV[R]_n`, built as `gauss n` is (`gaussS`, `rV_cons`); sigma-finite; the measure of a box; uniqueness on boxes; Fubini for the first coordinate and for a block (`row_mx`); invariance under translations and permutations; the image under `x |-> a x` (factor `|a|^-n`); `gauss n` has density `(2 pi)^{-n/2} exp(-|x|^2 / 2)`; `int exp(-|x|^2 / (2 tau^2)) dx = (2 pi tau^2)^{n/2}`; `Leb(B_n(r)) <= (2 pi e / n)^{n/2} r^n` for the closed Euclidean ball | `gauss.v`, `measure_rowbox_unique`, `normal_pdf`, `lebesgue_measure_affine` | 1,100 |
| `fourier/charfun_rV.v` | A | `cf_re`, `cf_im`, `cf_norm` of a law on `'rV[R]_m`, as the characteristic function of `<x, theta>` at `1`; `cf (gauss m) theta = exp(-|theta|^2 / 2)` (`gauss_mxdot`); the modulus for the law of `sum_i xi_i w_i + s G`; the Gaussian regularization identity of point 2; `P(Y + sigma G in B) <= (2 pi)^-m (int |cf nu|) Leb(B)`; the same for `Y` and a closed ball | `charfun.v`, `lebesgue_rV.v`, `gauss_mxdot`, `gauss_box` | 1,000 |
| `fourier/small_ball.v` | A | Lemma 3.8 (`int |cf nu| <= C^m`); the vector small-ball estimate; the corollary in the paper's form | everything above | 900 |
| `fourier/inversion.v` | A, last | the inversion theorem of point 2, with the density bounded by `(2 pi)^-m int |cf nu|` and continuous | `charfun_rV.v`, `measure_rowbox_unique` | 600 |
| `comparison/ornstein_uhlenbeck.v` | B | `ou t f x`, for `f` bounded measurable on `R`: bounded by the bound of `f`, bounded below by a lower bound of `f`, `int ou t f dgauss_1 = int f dgauss_1`, contraction in `L^1(gauss_1)`; for `t > 0`, derivatives of all orders needed in `x` and the derivative in `t` (Cameron-Martin), the generator identity; `ou t f x -> int f dgauss_1` as `t -> oo`; as `t -> 0`, `ou t f x -> f x` for `f` continuous, and `ou t f -> f` in `L^1(gauss_1)` for `f` bounded measurable, through the density of bounded continuous functions | `gauss_smoothing.v`, `gauss_shift.v`, `normal_prob_lincomb`, `normal_ibp`, `lebesgue_regularity_outer` | 1,300 |
| `comparison/brascamp_lieb.v` | B | `sum_i c_i = m` and `sum_i c_i <u_i, x>^2 = |x|^2` for a frame; the weighted Cauchy-Schwarz inequality; Gaussian integration by parts along a vector; `Lambda' >= 0`; the Gaussian form for bounded continuous `f_i >= delta`, then bounded measurable, then `[0, oo]`-valued (`poweR`); the Lebesgue form | `ornstein_uhlenbeck.v`, `gauss_ibp`, `gauss_mxdot`, `differentiation_under_integral`, `hoelder`, `lebesgue_rV.v` for the Lebesgue form | 2,200 |

About 9,700 lines. Lane A about 3,600, lane B about 3,500, lane C about
2,600; agent 1 also merges and assembles.

### Order

Arrows mean "is needed by". `charfun.v -> charfun_rV.v, esseen.v`;
`esseen.v -> gauss_factor.v`; `lebesgue_rV.v -> charfun_rV.v` and the
Lebesgue form in `brascamp_lieb.v`; `ornstein_uhlenbeck.v ->
brascamp_lieb.v`; `brascamp_lieb.v, gauss_factor.v, charfun_rV.v, the
whitening -> small_ball.v`. The longest chain is lane B's.

1. **First hours.** Lane C commits `charfun.v` with the definitions and
   the first lemmas and pushes; agent 1 merges it to `main` at once, so
   that lane A can build on the definitions. Lane A starts
   `lebesgue_rV.v`, lane B `ornstein_uhlenbeck.v`.
2. Lane A merges `lebesgue_rV.v` to `main` when done. Lane C: `esseen.v`.
   Lane B: the semigroup.
3. Lane A: `charfun_rV.v`. Lane C: `gauss_factor.v`, the whitening.
   Lane B: the Gaussian form.
4. Lane B: the Lebesgue form. Agent 1 merges the three lanes, writes
   `small_ball.v`, completes the table of main results and the layout
   table of `library/README.md`, runs `make check`, pushes `main` and tags
   it `phase4`. Then lane A writes `inversion.v`.

Each lane merges `main` into its branch when a file it needs has landed.
Where a lane is blocked, it writes the header and the statements of its
next file, or helps the lane on the longest chain through `requests/`.

### Rules for this phase

- Branches: `lane/a`, `lane/b` and `lane/c`, continued: first merge
  `main` (3998195) into your lane branch (a fast-forward), run
  `make build` once (up to an hour with `JOBS=3`), then work. Agent 1
  merges in the `integration` clone and alone pushes `main` and tags.
- `_CoqProject`: in this phase each lane adds its own new files, in the
  block of its directory; agent 1 resolves the conflicts when merging.
  Nothing else of agent 1's files changes without agent 1.
- Requests between lanes go through `requests/<your lane>-to-<their
  lane>.md`, as in phase 2. Agent 1 deletes `requests/` at the end.
- The VM is shared with another project: use `JOBS=3`, never more. The
  wrapper gives the containers a low CPU weight. While iterating compile
  one file (`make library/fourier/charfun.vo`); run `make check` before
  every commit, which is quick here because nothing in `theories/`
  depends on the new files.
- Statements: the general form a probabilist would state, in the
  library's vocabulary (laws rather than random variables, `tuple_prod`
  for independence, `gauss n`, `normal_prob`, `mxdot`, `frobenius`,
  `lebesgue_rV`). Constants are explicit where that costs little
  (Esseen, the ball volume, the inequality for sums); otherwise they may
  be existential but depend only on the stated parameters. Values in
  `[0, oo]` where the classical statement has them (Brascamp-Lieb).
- Every file has the documentation header of the library's conventions,
  and each lane adds its rows to the table of main results of
  `library/README.md`. Agent 1 adds the `fourier/` row to the layout
  table. The library stays independent of `theories/` and of Stdlib's
  reals: `make check` enforces it.
- Nothing changes in `theories/`, `extension/`, the frozen files,
  `scripts/` or `check/`.
- Commit messages say what was proved, in plain words. No journals, no
  progress files; what a reviewer needs goes in the commit message and
  the README rows.

Phase 4 is done when `vector_small_ball` and its corollary are proved on
`main`, `make check` passes, the README rows are in, and `main` is tagged
`phase4`.

## Phase 5. The universality theorem

Phases 1 to 4 are done (`main` d3bb5fb, tag `phase4`). Phase 5 proves
`universality_statement` of `extension/UniversalityStatement.v`: Theorem
1.2 of Koehler and Sohn (arXiv 2608.27372; on the VM
`/srv/ellipsoid-fitting/papers/2608.27372/arxiv_v1.tex`), both phases,
every fourth moment `kappa > 1`. The feasibility study
`extension/README.md` (branch `extension/feasibility`, merged in step 0) is
the reference: its section (b) maps every component of the paper's proof,
with the paper's line numbers, to what exists, to new general library and
to new paper-specific work, and its section (e) explains the statement.
This section fixes the stages, the owners, the order and the rules. The
vector small-ball estimate (item S5 of the study) is done: phase 4.

### Step 0, before any proof

1. **The statement.** The user reviews `extension/UniversalityDefinitions.v`
   and `extension/UniversalityStatement.v` against the paper, with the ten
   choices of section (e) of the study (the mode of the limit, the family
   of laws, the subgaussian norm, the threshold, the cutoffs as suprema,
   the fit of value 1, the condition number, the error, the positivity of
   `e*`, the numerals). Once accepted, the two files are frozen like the
   eight files of the first theorem: their code does not change, only
   agent 1 edits their comments, and if a proof seems to require a change,
   stop and ask the user.
2. **The rules.** Agent 1 merges `extension/feasibility` into `main` and,
   with the user's permission given for this step only, changes the
   checked files: `scripts/check_sources.py` scans `extension/` as it scans
   `theories/` and `library/`, and checks the two statement files against
   the merge commit as a second baseline; `scripts/stale_citations.py`
   reads `extension/` too; the `Makefile` gets the pattern rule
   `extension/%.vo`; `README.md` and the ownership table of this file get
   the new directories. `check/Assumptions.v` is not touched; the axioms of
   the final theorem get their own `check/UniversalityAssumptions.v` and
   expected list at the end of stage 3.
3. **The directories and the servers.** Agent 1 creates every new
   directory of the tables below, each with the header of its first file,
   and pushes `main`; the user then reconnects the three Rocq servers
   (`/mcp`), which bind the load path when they start.

### The three stages

| Stage | Theorem | What it proves |
|---|---|---|
| 1 | `universality_unsat_fourth_moment_three` | the first conjunct of Theorem 1.2 (ii) at `kappa = 3`: no positive semidefinite fit above `1/4`, for every family of coordinate laws of fourth moment 3 (the study's milestone 1, re-scoped, by the paper's barrier route) |
| 2 | `universality_gaussian_model`, `universality_unsat` | Proposition 1.4 (the Gaussian model, both parts), then the second conjunct of `universality_statement` for every `kappa`: no fit above the threshold, and the error tends to `e*(alpha, kappa) > 0` (Theorems 1.2 (ii) and 1.7) |
| 3 | `universality_sat`, `universality_theorem` | the first conjunct, Theorem 1.2 (i): a well-conditioned positive definite fit below the threshold, by the approximate fit and the small-residual interpolation (Theorem 1.9); then `universality_theorem : universality_statement` in `extension/UniversalityTheorem.v` |

Each stage ends with a merged `main`, `make check`, a tag (`stage1`,
`stage2`, `phase5`), and the user's review of the stage theorem and of the
new rows of the table of main results of `library/README.md`. Stage 1 is
the paper's architecture end to end on the simplest case; it reuses from
the formal Gaussian proof only the GOE gap at head dimension zero and the
measurability of the fit event, and nothing from `Orientation/`,
`Hybrid/`, `Loss/` or `Projection/`, which the study shows cannot carry
non-Gaussian data.

### Components, owners and order

Item numbers are those of section (b) of the study, where each has its
paper lines, its reusable pieces and its estimate. Library files are
general, over `R : realType`, in the library's conventions; the
paper-specific files live in `extension/` under the root
`EllipsoidUniversality`, at Stdlib's `R` like `theories/`, and use the
library through the bridge modules of `theories/Analysis/` and
`theories/Gaussian/Law/LibraryBridge`. File names are proposals; each
lane fixes them in its stage plan (below). Lines are the study's
estimates, plus or minus fifty percent.

**Stage 1.** The Lindeberg argument with a barrier, the threshold at
`kappa = 3`, and the assembly.

| Item | Content | Lane | Files | Lines |
|---|---|---|---|---|
| U3 | the subgaussian toolkit: the `psi_2` norm and its moment generating function, sums, squares are subexponential, Bernstein's inequality, concentration of the norm, the operator norm of a matrix with independent subgaussian entries | A | `library/probability/subgaussian.v`, `subgaussian_matrix.v` | 2,000 |
| U2 | Efron-Stein for `tuple_prod`, the `L^p` recursion (p = 2, 4, 8), then the regularity of the quadratic features `W = (x x^T - I) / sqrt d` (Definition 2.5), at `kappa = 3` first | A | `library/probability/efron_stein.v`; `extension/Features/Regular.v` | 2,400 |
| U12 | the sample law as rows: the reshaping between the flat law on `(n d).-tuple` and `tuple_prod` of row laws, block marginals, independence of disjoint blocks, with the Gaussian twin for `gaussian_product_law` | A | `library/probability/tuple_rows.v`; `extension/Model/Rows.v` | 1,100 |
| U11 | measurability of the events of the statement (the fit event is reused; the positive definite and conditioned fit events and the error event are new) | A | `extension/Model/Measurability.v` | 800 |
| GOE bridge | from `paper_main_hybrid_gap_event` at head dimension 0 to `P(Gamma_{G,3} >= c_0) -> 1`: normalizations, the GOE row scaling, all rows kept, the identification of the formal GOE array with the paper's Gaussian features | A | `extension/Unsat/GoeBridge.v` | 1,500 |
| U10 at 3 | the stage theorem from U9, the bridge and U12 | A | `extension/Unsat/FourthMomentThree.v` | 1,000 |
| U4 | self-concordant barriers: Definition 2.7, the comparison along a segment (Lemma 2.15), the gradient bound (Lemma 2.10) | B | `library/convex/self_concordant.v` | 1,200 |
| U5 | the log-determinant barrier on the trace slice of the positive definite cone and the two-sided barrier (Lemma 2.8), by the spectral theorem | B | `library/convex/logdet_barrier.v` | 1,300 |
| U6 | the convex analysis the paper's Theorem 2.9 needs (minimizers of a strongly convex objective with a barrier on a relatively open bounded convex set, first-order conditions, Taylor's formula with the Bregman remainder), then Theorem 2.9 itself in the paper's abstract feature form: leave-one-out, the insertion formula, Propositions 2.14 and 2.16, Lemmas 4.1 and 4.2, the telescoping over rows from `lindeberg_replacement` generalized to integrable functionals with integrable per-row bounds, the variance bound by Efron-Stein | B | `library/convex/minimizers.v`, `library/convex/barrier_lindeberg.v` | 6,000 |
| U7 | removing the barrier (Lemma 2.11) | B | `library/convex/barrier_removal.v` | 400 |
| U9 | Corollary 2.13: the reference point, the choices of `gamma` and `beta_d`, the relations between the regularized and the unregularized values | B | `extension/Unsat/Regularized.v` | 1,200 |
| U8 | removing the ridge (Lemma 2.12): symmetrization and Rademacher complexity, the small-ball method for pointwise separable classes, Lemma 4.3 by the nets of `matrix/nets.v` and a scalar Bernstein inequality | C | `library/probability/symmetrization.v`, `small_ball_method.v`; `extension/Unsat/Ridge.v` | 3,900 |
| G5 | the scalar variational problem: Lemmas 5.7 and 5.8 for a general law with finite second moment, Lemma 5.9, Proposition 5.10, the semicircle facts (mass one, second moment `1/2`, the symmetry identities), hence the equality of the two definitions of `alpha*`, the identification of the cutoffs with the paper's unique solutions, and `universality_alpha_star 3 = 1/4` | C | `library/probability/variational.v`; `extension/Gaussian/Threshold.v` | 4,000 |
| G1 | the cones `S^d_kappa`, the map `T_kappa`, the dual cones (Lemma 5.2) | C | `extension/Gaussian/Cones.v` | 800 |

About 27,600 lines. Order: U3 and U4 first, they unblock everything;
then U5 and U6 (lane B) in parallel with U2 and U12 (lane A) and U8 and G5
(lane C); then U7, U9, the bridge, U10. The study's dependencies:
U3 -> U2, U8; U4 -> U5, U6, U7; U5, U6, U7, U8 -> U9; U12 -> U6, U10;
U9, the bridge, U12 -> U10.

**Stage 2.** The Gaussian model, then the general unsatisfiable phase.

| Item | Content | Lane | Files | Lines |
|---|---|---|---|---|
| G7 | Wigner's semicircle law for the GOE by the moment method (traces of powers, Catalan numbers), with the convergence of the second moments; a crude spectral-norm bound through `gauss_opnorm_tail`; von Neumann's trace inequality for symmetric matrices | A | `library/random_matrix/semicircle.v`, `goe.v`; `library/matrix/von_neumann.v` | 5,800 |
| G6 | the second-moment identities of a uniform direction `g / |g|` from the rotation invariance of the GOE and of `gauss n`, replacing Haar averaging (Lemma 5.13) | A | `library/random_matrix/goe_rotation.v` | 1,500 |
| U10 | Theorem 1.7 and the second conjunct of Theorem 1.2 (ii) for every `kappa`: Chebyshev on the variance bound of Theorem 2.9, Corollary 2.13 (ii), Proposition 1.4 (ii); U2 for general `kappa`; U11 for the error event | A | `extension/Unsat/Universality.v` | 1,500 |
| G2 | Moreau's decomposition for a closed convex cone of `'rV[R]_N`: the projection onto a closed convex set, the polar cone | B | `library/convex/moreau.v` | 1,200 |
| G3 | the convex Gaussian min-max theorem in probability form on compact convex sets, from `gordon` and `gauss_concentration`, with the minimax exchange | B | `library/comparison/cgmt.v` | 3,800 |
| G9 | the well-conditioned Gaussian fit below the threshold (Lemma 5.17) | B | `extension/Gaussian/Subcritical.v` | 1,200 |
| G4 | the Gaussian representation `A_{G,kappa}(R) = sqrt(2/d) A T_kappa R` (Lemmas 5.4 to 5.6), from `gauss_mulmx_law` and `paper_main_projected_law` | C | `extension/Gaussian/Representation.v` | 1,200 |
| G8 | the shifted cone-projection limit (Proposition 5.15, Lemma 5.16) and Proposition 1.4; the measurability of the spectrum and the continuity of the positive part of a symmetric matrix | C | `library/matrix/spectral_continuity.v`; `extension/Gaussian/Limit.v` | 4,000 |

About 20,200 lines. Order: G7 and G5 are the long items and start as
soon as their lanes are free, G7 even during stage 1; then G2, G3, G4;
then G6, G8, G9; then U10. Dependencies: G5 -> G7, G8, G9; G1, G2, G3 (i),
G4, G6, G7 -> G8; G3 (ii), G6, G7 -> G9; U2, U9, G8 -> U10.

**Stage 3.** The satisfiable phase.

| Item | Content | Lane | Files | Lines |
|---|---|---|---|---|
| HW | the Hanson-Wright inequality for independent subgaussian coordinates (Lemma 3.2), with decoupling | A | `library/probability/hanson_wright.v` | 2,500 |
| S1 | the approximate fit (Proposition 2.1) from Corollary 2.13 (i) with the two-sided barrier, Proposition 1.4 (i), the operator norm of the average of the features, the leave-one-out bound in `l_oo` | A | `extension/Sat/ApproximateFit.v` | 2,500 |
| S11 | Theorem 1.2 (i) and `universality_theorem` | A | `extension/Sat/Universality.v`, `extension/UniversalityTheorem.v` | 800 |
| S6 | covering the nuclear-norm ball by product balls (Lemma 3.10): Lebesgue measure on matrices from `lebesgue_rV`, the volumetric bound, Urysohn's inequality or another entropy bound with the constant `C^{mq}` | B | `library/matrix/covering.v` | 3,000 |
| S8 | the one-stage small-ball bound (Lemma 3.14) from `vector_small_ball`, with conditioning on a block of coordinates of `tuple_prod` and the conditional independence of the other block | B | `library/probability/conditioning.v`; `extension/Sat/OneStage.v` | 2,200 |
| S9 | the light-tail quotient-norm lower bound (Proposition 3.4): sequential block revealing, nets of light tails and sparse heads, the union bound | B | `extension/Sat/LightTail.v` | 2,500 |
| S2 | the nuclear norm and its duality with `opnorm`, the range duality (Lemma 2.2) | C | `library/matrix/nuclear.v` | 1,500 |
| S3 | the a priori estimates (Proposition 3.1): the restricted isometry estimate for matrices with subexponential columns (the cited ALPT theorem, or a self-contained substitute for the two uniform bounds), the subgaussian feature edge | C | `library/random_matrix/restricted_isometry.v`; `extension/Sat/Apriori.v` | 5,000 |
| S4 | the sparse lower bound (Proposition 3.3) | C | `extension/Sat/SparseLower.v` | 600 |
| S7 | the effective-rank bound (Lemma 3.12, Corollary 3.13) | C | `extension/Sat/EffectiveRank.v` | 800 |
| S10 | Theorem 2.3 (the shelling argument) and Theorem 1.9 | C | `extension/Sat/Interpolation.v` | 1,200 |

About 22,600 lines. Order: S3 first (it feeds S4, S7, S9), S2, S6 and HW
in parallel; then S7, S8, S9, S10; S1 after G9; then S11. Dependencies:
U3 -> S1, S3; U9, G9, HW -> S1; S3 -> S4, S7, S9; S6, S7, S8 -> S9;
S2, S3, S4, S9 -> S10; S1, S10, G5 -> S11.

**Across stages.** A lane that has no item left in the current stage
takes its items of the next stage in order, without waiting. The four
hard items, U6, G7, S3 and S6, start as early as their dependencies
allow; the lane says in its first report on each what route it takes and
what it has verified, and stops to ask when a cited theorem (ALPT,
Urysohn) turns out to need more than the stage allows: a weaker
self-contained substitute that suffices for the paper is preferred over a
faithful formalization of the citation.

### Rules for this phase

- **Ownership.** `library/`: `gaussian/`, `probability/` and the new
  `random_matrix/` to lane A; `comparison/` and the new `convex/` to lane
  B; `matrix/` and `fourier/` to lane C; the file tables above override
  this for single files. `extension/`: `Model/`, `Features/`, the files of
  lane A in `Unsat/` and `Sat/` to lane A; `Unsat/Regularized.v` to lane B and
  `Unsat/Ridge.v` to lane C; `Gaussian/` to lane C except
  `Subcritical.v`; `Sat/` as in the table; the two statement files are
  frozen; `UniversalityTheorem.v` is agent 1's. Each lane adds its own
  files to `_CoqProject`, in the block of its directory.
- **Stage plans.** In the first hours of each stage, each lane writes the
  plan of its items: the file names, the statements of the main results
  as comments in the file headers, and the interfaces it expects from the
  other lanes, in `requests/` where needed; agent 1 merges these plans
  to `main` at once, so that the interfaces are shared before the proofs.
- **Branches and merges.** `lane/a`, `lane/b`, `lane/c`, continued from
  `main`; agent 1 merges in `integration` at milestones (a component done
  and used, or the end of a stage) and alone pushes `main` and the tags.
  `requests/<lane>-to-<lane>.md` as before; agent 1 deletes `requests/`
  at the end of the phase.
- **Building.** The VM is shared: `JOBS=3`. A clone's first build after
  the merge of `extension/feasibility` may recompile up to the 488 modules
  downstream of the frozen definitions (about an hour); afterwards the
  builds are incremental, and nothing in `theories/` depends on the new
  files. Compile one file while iterating, with the Rocq server where it
  helps (it attaches an `End` of a section and the `Let`s that follow to
  the previous lemma: close sections with a lemma, not a `Let`);
  `make check` before every commit.
- **Statements.** Library results in the general form a probabilist or an
  analyst would state, in the library's vocabulary; constants explicit
  where that costs little; the paper's Gaussian specializations and its
  ellipsoid-specific steps go to `extension/`, never to `library/`. The
  user reviews the library rows and the stage theorem at the end of each
  stage.
- **Nothing changes** in `theories/`, in the ten frozen files, in
  `check/` or in `scripts/` outside step 0 and the end of stage 3.
- Commit messages say what was proved; no journals or progress files.

### Estimates

About 70,000 lines over the three stages, against 21,000 in the library
today. Phase 4 produced 10,000 lines of new mathematics in a day with the
three lanes; at that pace each stage is about a week, if the hard items
behave: Theorem 2.9 with its convex analysis (U6), the semicircle law
(G7), the a priori estimates (S3) and the covering bound (S6) are each the
kind of result that can take several days or need a change of route.
Count on two to four weeks of continuous work, with stage 1 as the first
checkpoint after about a week. The weekly quotas of the accounts are the
other limit: at phase 4's consumption, lane A's account reaches its
weekly limit in about two days; lanes report when throttled, and the
user decides on the accounts.

Phase 5 is done when `universality_theorem` is proved on `main`, its
axioms are among the expected ones, `make check` passes, the README rows
cover every new file, and `main` is tagged `phase5`.

## Phase 6. Exact fitting for finite mixtures of product laws

Phases 1 to 5 are done (`main` 112d6a2, tag `phase5`). Phase 6 proves a
theorem that is not in the literature checked so far: Theorem 1.2 of
Koehler and Sohn, both phases, for i.i.d. points whose law is, at each
dimension `d`, a finite mixture of product laws whose components have
coordinates of mean 0, variance 1 and `psi_2` norm at most `K`, with a
fixed unconditional fourth moment `kappa > 1` (assumptions (M1)-(M3));
the number of components may grow with `d`. Its corollary is exact
fitting for the paired law (pairs of coordinates with density
`(1 + eps h(x) h(y)) / 12` on `[-sqrt 3, sqrt 3]^2`, `h` the rescaled
Legendre polynomial `P_4`) for every `eps` in `[-1, 7/3]`.

The sources, on the VM:

- the mathematics: `/srv/ellipsoid-fitting/notes/mixture-product-universality.md`
  (the general theorem and its proof), `paired-dependent-sat.md` (the
  paired law), and the response to the first review,
  `/srv/ellipsoid-fitting/reviews/paired-law-response.md`;
- the plan: `/srv/ellipsoid-fitting/notes/paired-law-plan-v2.md`, written
  by agent 3. Its section 4 is the plan of this phase: the four statement
  files (4.1), the route (4.2), the items L1-L3 (library), X1-X8
  (generalizations of modules of `extension/`) and P0-P3 (statements and
  the paired law) (4.3), the order (4.6), the risks (4.7) and the
  estimates (4.8: about 9,200 lines, untested). This section fixes the
  roles and the rules; where they differ, this section wins.

### Roles

- **Agent 3 is the master of this phase**, by the user's decision. It
  keeps the plan, assigns the items to the three lanes (its own
  included, as it judges), and gives agents 1 and 2 their work directly
  in their sessions (below). It writes the statement files (P0), freezes
  them after the user's review, creates the new directories, merges the
  lanes in the `integration` clone, and alone pushes `main` and tags.
  Wherever the sections above give agent 1 a coordinating task (merging,
  `main`, tags, the comments of frozen files, `Makefile`, `README.md`, the
  rest of `library/README.md`), read "the master" in this phase.
- **Agents 1 and 2** take their items from the master, work on `lane/a`
  and `lane/b`, push only those branches, and merge `main` into them when
  the master says. An item is reported by a commit message that says what
  was proved; a question or a blocker goes to the master in
  `requests/<lane>-to-c.md`, or in the pane when it is urgent.
- **Ownership.** Files keep the owners of phase 5 (the last column of the
  table "Ownership"); the master assigns `extension/Mixture/`,
  `extension/Paired/` and any file the plan reassigns, and keeps the
  current table of items, owners and states in
  `/srv/ellipsoid-fitting/runtime/phase6/assignments.md` (outside the
  repository). One file has one owner at a time.
- **The coordinator.** Messages signed "Coordinator" come from the user's
  supervising session on the user's machine. In this phase it assigns no
  item; it verifies pushed commits, keeps GitHub in sync and relays the
  user's decisions.

**How the master gives work.** From its own shell on the VM:
`tmux send-keys -t arthur -l "<message>"`, then
`tmux send-keys -t arthur Enter` (agent 2's session is `marcol`). A
message sent during a turn waits until the turn ends. Write the message so
that it stands alone (the item, its files, the statements expected, the
interfaces with other lanes), keep apostrophes out of double-quoted shell
strings, and read the pane (`tmux capture-pane -p -t arthur`) to see that
it arrived. Never type into a pane whose prompt holds text that the user
typed. Never restart a session, run `/clear`, or change a model or an
account: the user does that.

### Step 0

1. **The statements.** The master writes the four statement files of
   section 4.1 of the plan (`extension/MixtureDefinitions.v`,
   `MixtureStatement.v`, `PairedDefinitions.v`, `PairedStatement.v`),
   compiles them, pushes `main`, and says so in its pane; the coordinator
   asks the user to review them. Library items and generalizations that do
   not depend on these files start at once.
2. **The freeze.** Once the user accepts the statement files, the master
   freezes them like the ten frozen files: their code does not change,
   only the master edits their comments, and if a proof seems to require
   a change, stop and ask the user. `scripts/check_sources.py` compares
   them with the acceptance commit as a third baseline. When the theorems
   exist, `check/MixtureAssumptions.v` and `check/PairedAssumptions.v`,
   with their expected lists, are added on the pattern of
   `check/UniversalityAssumptions.v`, and the `Makefile`'s `check` target
   runs them. The user's launch of this phase permits these changes to
   `scripts/` and `check/`, in step 0 and at the end of the phase, and no
   other.
3. **The directories and the servers.** The master creates
   `extension/Mixture/` and `extension/Paired/`, each with the header of
   its first file, and pushes `main`; the user then reconnects the three
   Rocq servers (`/mcp`), which bind the load path when they start.

### Rules for this phase

- Nothing changes in `theories/`, in the ten frozen files of phases 1 to
  5, or in `check/Assumptions.v`, `check/UniversalityAssumptions.v` and
  their expected lists. `universality_theorem` keeps building at every
  commit: a generalized lemma keeps its old statement as a corollary
  under its old name, or its callers change in the same commit.
- Library results are stated over `R : realType` in the library's
  vocabulary; nothing in `library/` mentions mixtures of ellipsoid data,
  Legendre polynomials or the uniform law on `[-sqrt 3, sqrt 3]`. The
  general theorem lives in `extension/Mixture/`, the paired law in
  `extension/Paired/`.
- Every new file has the documentation header of the library's
  conventions; each lane adds its rows to the table of main results of
  `library/README.md` and its files to `_CoqProject`, in the block of
  their directory; the master adds a section on the general theorem and
  its corollary to `extension/README.md`.
- Requests between lanes go through `requests/<lane>-to-<lane>.md`; the
  master deletes `requests/` at the end of the phase.
- The VM is shared: `JOBS=3`. Compile one file while iterating;
  `make check` before every commit. Commit messages say what was proved;
  no journals or progress files in the repository.

Phase 6 is done when `mixture_theorem : mixture_theorem_statement` and
`paired_theorem : paired_statement` are proved on `main`, their axioms
are among the eight expected ones, `make check` passes, the README rows
cover every new file, and `main` is tagged `phase6`.

## Phase 7. The phase 6 release: documentation, checks, a third corollary

Phase 6 is done (`main` c3e555e, tag `phase6`). A review of that release,
`/srv/ellipsoid-fitting/reviews/phase6-release-review.md` (it ends with
the coordinator's checks of its claims), proposed the four items below,
and the user accepted all four on 9 October 2026. The roles are those of
phase 6: agent 3 is the master, assigns the items (its own lane
included), gives agents 1 and 2 their work in their sessions, merges in
the `integration` clone, and alone pushes `main` and tags; the
coordinator assigns no item, verifies pushed commits, keeps GitHub in
sync and relays the user's decisions. The master keeps its table of
items, owners and states in
`/srv/ellipsoid-fitting/runtime/phase7/assignments.md`. New files go in
existing directories (statement files at the top of `extension/`,
proofs in `extension/Paired/` or `extension/Mixture/`), so that the Rocq
servers need no reconnection.

### The items

1. **Documentation.** `README.md` and `extension/README.md` present the
   finite-mixture theorem as the main result of phase 6: both phases of
   Theorem 1.2 of Koehler and Sohn for i.i.d. points whose law is a
   finite mixture of product laws, with a number of components that may
   grow with `d`, under (M1)-(M3): componentwise mean 0, variance 1 and a
   uniform `psi_2` bound, and a common unconditional fourth moment
   `kappa > 1`. The paired law is its corollary, over the whole range
   `eps` in `[-1, 7/3]`, with constants uniform in `eps`. On novelty, say
   that no matching theorem was found in a targeted literature search;
   priority is not confirmed. Fix the stale passages: the opening of
   `extension/README.md` (line 12, "Nothing proves the statement"); its
   summary of `approximate_fit_law` (line 894, "from any regular feature
   law", which omits the covariance `unsat_cov kappa d`, `tau d -> 0` and
   the subexponential tails); the layout section of `README.md` (75
   library files, the folders `Mixture/` and `Paired/`, the theorems
   `mixture_theorem` and `paired_theorem`). In `library/README.md`, the
   owners of the rows add the hypotheses that the rows leave out:
   `variance_mixture` needs `X` square integrable under every component,
   `mixture_cover` measurable sets `E i`, and `moment4_integrable` a bound
   on `|g z|`.
2. **Checks.** The user permits these changes to
   `scripts/check_sources.py` and `check/`, and no other:
   - the three check files `check/UniversalityAssumptions.v`,
     `check/MixtureAssumptions.v` and `check/PairedAssumptions.v` and
     their three expected lists are compared byte for byte with commit
     c3e555e, a separate baseline; the historical baselines and
     `check/frozen-baseline` do not change;
   - an axiom report that has neither an `Axioms:` section nor the line
     "Closed under the global context" is an error (today `axiom_names`
     reads an empty report as no axioms);
   - the definition of `tuple_prod` (`library/probability/lindeberg.v`),
     on which the frozen statements of phases 5 and 6 depend, is
     protected: either its code is compared with c3e555e, or a new check
     file proves a characterization of it that does not depend on its
     implementation (for example its value on products of measurable
     sets) and is frozen like the other check files. The master chooses,
     and says which in the commit message;
   - the statement files of item 3, once the user accepts them, are
     frozen with the acceptance commit as a new baseline, and the theorem
     of item 3 gets an axiom check and an expected list on the pattern of
     `check/PairedAssumptions.v`, run by `make check`.
3. **The latent-sign corollary.** For `0 <= s <= 1`, i.i.d. points of law
   `(1/2) lambda_s^{(x) d} + (1/2) lambda_{-s}^{(x) d}`, where
   `lambda_a = (1 + a h) mu` is `paired_law mu a` of
   `extension/Paired/Uniform.v`: one hidden sign couples all the
   coordinates of a point. The two components have mean 0, variance 1,
   bounded support and fourth moments `9/5 +- 8 s / 35`
   (`paired_law_component`, `paired_law_fourth`), so the coordinates have
   unconditional fourth moment `9/5`, and the theorem follows from
   `mixture_theorem` with two components. Step 0 as in phase 6: the
   master writes the statement files, compiles them, pushes `main` and
   says so in its pane, and the coordinator asks the user to review them.
   A suggestion for the statement: define the law directly, by its
   density `(prod_j (1 + s h(x_j)) + prod_j (1 - s h(x_j))) / 2` against
   the product of `mu`, as `paired_probability` is defined, and let `s`
   depend on `d`, with the constants chosen before `s`, as `eps` in
   `paired_statement`. The proof may start before the review.
4. **Library generalizations.** In `library/convex/feature_mixture.v`,
   `mixture_regular_feature` under the weaker hypothesis
   `sum_i w_i <Sig i - Sigma, T>^2 <= c^2 |T|_F^2` for every symmetric
   `T`; the present theorem keeps its name and statement and becomes a
   corollary (Cauchy-Schwarz for the Frobenius product). In
   `library/probability/density_law.v`, a constructor of the law from a
   function with an explicit proof that it is a density
   (`prob_density mu f`), with the equations that relate it to
   `density_prob`.

### Rules for this phase

The rules of phase 6 apply. Nothing changes in `theories/` or in the
code of the fourteen frozen files (the eight of `theories/`, the two of
phase 5, the four of phase 6). `universality_theorem`, `mixture_theorem`
and `paired_theorem` keep building at every commit. Library results are
stated in the library's vocabulary, every new file has its documentation
header and its rows, `make check` runs before every commit, builds use
`JOBS=3`, requests go through `requests/` (the master deletes it at the
end), and the repository gets no journals or progress files.

Phase 7 is done when the four items are on `main`, the latent-sign
theorem is proved with its axioms among the eight expected ones,
`make check` passes, the README rows cover every new file, and `main` is
tagged `phase7`.

## Phase 8. Countable mixtures and the optimal condition number

Phases 1 to 7 are done (`main` 7d0677c, tag `phase7`). Phase 8
formalizes the three extensions of the finite-mixture theorem in
`/srv/ellipsoid-fitting/notes/phase6-three-extensions.md` (the note),
written on the user's machine on 9 October 2026: ordinary proofs, with
novelty unconfirmed. It follows the plan of agent 3,
`/srv/ellipsoid-fitting/notes/three-extensions-plan.md` (the plan), which
the user launched on 9 October 2026 without the optional items of its
section 5.3. The plan's sections 2 (the formal route), 4 (the statement
files), 5 (components, files and lanes), 6 (order), 7 (risks) and 8
(about 9,900 lines, an untested estimate) are the plan of this phase.
This section fixes the roles and the rules; where they differ, this
section wins.

The three tracks:

1. **Countable mixtures** (items L1, K2, K3):
   `countable_theorem : countable_theorem_statement`, the conclusions of
   the frozen mixture theorem, with its constants, for countably many
   components. The proof truncates the tail as in the note's section 3,
   replacing it by the product of its coordinate marginals, and transfers
   the conclusions by the coupling of label tuples.
2. **The optimal condition number at fourth moment three** (L2 to L5, Q1
   to Q9): `condition_theorem : condition_theorem_statement`. It gives
   the threshold alpha_C for every fixed C > 1 and alpha != alpha_C (the
   note's (20)), and the convergence of the optimal data condition number
   to C_star^G(alpha) for 0 < alpha < 1/4 ((21)), for finite and
   countable mixtures. The route avoids the note's cited black boxes. The
   CGMT of `library/comparison/cgmt.v` gives the Gaussian witness and the
   gap. Theorem 2.9 with its barrier (`af_conc`) works on each two-sided
   slice of a finite cover, and the slice is chosen deterministically from
   the Gaussian centers.
3. **The scope of the latent-sign law** (S1): the covariance (10) and the
   variance (11) of the note.

Not in this phase: the robustness corollary (17), the tensorization
bounds (13)-(14), the continuous-latent counterexample (18), the endpoint
expansions (34)-(35) and an exact Gaussian kernel element (the plan's
items R1 to R5).

### Roles

As in phases 6 and 7. **Agent 3 is the master.**
- It assigns the items (its own lane included) and gives agents 1 and 2
  their work in their sessions.
- It writes the statement files and freezes them after the user's
  review, and it creates the new directories.
- It merges in the `integration` clone and alone pushes `main` and tags.
- It keeps the table of items, owners and states in
  `/srv/ellipsoid-fitting/runtime/phase8/assignments.md`.

Its starting point is the plan's lane proposal:
- A: L1, L4, K2, K3, Q6, Q7;
- B: L5, Q3, Q4, Q8, S1;
- C: L2, L3, Q1, Q2, Q5, Q9.

Agents 1 and 2 take their items from the master. The coordinator assigns
no item; it verifies pushed commits, keeps GitHub in sync and relays the
user's decisions.

### Step 0

1. **The statements.** The master writes the five statement files of the
   plan's section 4: `CountableMixtureDefinitions.v`,
   `CountableMixtureStatement.v`, `ConditionDefinitions.v`,
   `ConditionStatement.v` and `LatentSignScope.v`, at the top of
   `extension/`. Their comments guide the reviewer, as in the frozen
   files. It compiles them, pushes `main` and says so in its pane; the
   coordinator asks the user to review them, with the choices of the
   plan's section 4.6. Items that do not depend on the statement files
   start at once (wave 1 of the plan's section 6).
2. **The freeze.** Once the user accepts the files, the master freezes
   them like the frozen files of phases 5 to 7: their code does not
   change, only the master edits their comments, and
   `scripts/check_sources.py` compares them with the acceptance commit as
   a new baseline. When the theorems exist,
   `check/CountableAssumptions.v`, `check/ConditionAssumptions.v` and
   `check/LatentScopeAssumptions.v` join `make check` on the pattern of
   `check/LatentSignAssumptions.v`, each with an expected list of the
   eight classical axioms. The user's launch permits these changes to
   `scripts/check_sources.py`, `check/` and the `Makefile`, in step 0 and
   at the end of the phase, and no other.
3. **The directories and the servers.** The master creates
   `extension/Countable/` and `extension/Condition/`, each with the header
   of its first file, in the same push as the statement files. The user
   then reconnects the three Rocq servers (`/mcp`) once.

### Rules for this phase

The rules of phase 6 apply.
- Nothing changes in `theories/`, in the code of the sixteen frozen files
  (eight in `theories/`, two of phase 5, four of phase 6, two of phase 7),
  in the check files and expected lists of phases 1 to 7, or in the
  pinned section `tuple_prod` of `library/probability/lindeberg.v`.
- `universality_theorem`, `mixture_theorem`, `paired_theorem` and
  `latent_sign_theorem` keep building at every commit. A generalized
  lemma keeps its old statement under its old name; for example
  `approximate_fit_law` and `af_at_d`, which item Q6 generalizes.
- Library results are stated over `R : realType` in the library's
  vocabulary. Nothing in `library/` mentions ellipsoid fitting.
- Every new file has the documentation header and its README rows.
- Build with `JOBS=3`, and run `make check` before every commit.
- Requests between lanes go through `requests/`, which the master
  deletes at the end.
- The repository gets no journals or progress files.

Phase 8 is done when the following hold:
- `countable_theorem`, `condition_theorem` and the scope results of
  `LatentSignScope.v` are proved on `main`;
- their axioms are among the eight expected ones;
- `make check` passes;
- the README rows cover every new file;
- `main` is tagged `phase8`.

## Phase 9. The optional items of the three extensions

Phases 1 to 8 are done (`main` a89ed1e, tag `phase8`). On 9 October 2026
the user asked to formalize the four results that phase 8 left out. They
are in `/srv/ellipsoid-fitting/notes/phase6-three-extensions.md` (the
note) and in section 5.3 of
`/srv/ellipsoid-fitting/notes/three-extensions-plan.md` (the plan), which
names them R1 to R4 and sketches them. The plan's item R5, an exact
Gaussian kernel element, is not part of this phase.

1. **R1. Robustness in total variation** (the note's section 3.2).
   - If arbitrary point laws P~_d satisfy |P~_d - P_d|_TV = o(d^-2) for
     an admissible finite or countable mixture family (P_d), then
     independent samples from P~_d inherit all the conclusions of the
     family. The perturbed laws need not keep the moment or tail
     assumptions.
   - The error in the probability of any measurable set of samples is at
     most n |P~_d - P_d|_TV, which `lindeberg_replacement` gives with an
     indicator.
   - The contamination example shows that the scale is necessary. Below
     the threshold, P~_d = (1 - lambda/n) P_d + (lambda/n) delta_0 has
     exact fitting probability tending to e^(-lambda), because a point at
     0 blocks every fit of value one.
   - New definitions to review: the total variation distance of two laws
     on R^d, and the law of a sample of n i.i.d. points of an arbitrary
     law on R^d.
2. **R2. Tensorization of the latent-sign law** (the note's section 2.3,
   (12)-(14)).
   - Define the conditional variance Var(f | X_{-j}) under the
     latent-sign law through its conditional density, and the
     tensorization inequality (12) with a constant T_d.
   - Prove T_d >= 1 + (d - 1) s_d^2 / 9, from f = sum_j h(X_j).
   - Prove, for fixed s > 0, T_d >= (c' / d) exp(c s^2 (d - 1)) for large
     d, from f_d = 1{sum_j h(X_j) > 0}, Hoeffding's inequality under each
     component, and Var f_d -> 1/4.
3. **R3. The continuous-latent counterexample** (the note's section 3.3,
   (18)).
   - The latent parameter a is uniform on [1, 2]. Given a, the
     coordinates are independent with P(X = a) = 1/(1 + a^2) and
     P(X = -1/a) = a^2/(1 + a^2).
   - Each component has mean 0, variance 1, |X| <= 2 and fourth moment
     a^2 - 1 + a^-2, whose average is 11/6.
   - For d >= 2, the point law has total variation distance one from
     every countable mixture of product laws. The pair (X_1, X_2) lives
     on a finite union of curves with finite sections, a product law
     charges such a set only through pairs of atoms, and the law of
     (X_1, X_2) has no atom.
4. **R4. The endpoint expansions** (the note's (34) and (35)).
   - (34): C_star^G(alpha) = 1 + (3 pi / (2 sqrt 2)) sqrt alpha
     + (9 pi^2 / 16) alpha + O(alpha^(3/2)) as alpha -> 0.
   - (35): C_star^G(alpha) ~ 8 / (3 pi (1/4 - alpha)) as alpha -> 1/4.
   - Both are stated on `condition_alpha` and `condition_star` of the
     frozen `ConditionDefinitions.v`.
   - They follow from the expansions (11) and (13) of
     `notes/gaussian-condition-number-theorem.md`, through the behavior
     of m and v near 0 and near the edge sqrt 2 of the semicircle law.
5. **R6. The follow-ups of the review of the phase 8 release**
   (`/srv/ellipsoid-fitting/reviews/phase8-release-review.md`), which the
   user accepted on 9 October 2026.
   - **The checker.** An axiom report with the line `Axioms:` must list
     at least one axiom, and an axiom-free report is accepted only
     through the line "Closed under the global context".
   - **The check baseline.** The check files of phases 7 and 8 and their
     expected lists are compared byte for byte with a89ed1e, as a
     separate baseline. These are `check/LatentSignAssumptions.v`,
     `check/CountableAssumptions.v`, `check/ConditionAssumptions.v`,
     `check/LatentScopeAssumptions.v` and their four `.expected` files.
     The historical baselines and `check/frozen-baseline` do not change.
   - **The marginal lemma.** For every j < d, dimension one included,
     coordinate j of a point of the latent-sign law has law mu and
     h(x_j) is centered. It is a new lemma beside the frozen scope
     statement, which does not change.
   - **Measurability.** `data_condition_number (n d) d` is a measurable
     function of the sample. The proof goes through the measurable,
     monotone fit events: the event {C < r} is the union over rational
     q < r of the fit events at q.
   - **The documentation** (the review's sections 1.3 to 1.5):
     - narrow the concentration wording to "these laws do not satisfy
       dimension-free Gaussian concentration for convex 1-Lipschitz
       functions", and separate the formal identities from their
       consequences;
     - replace "the proofs are ordinary" by "the ordinary arguments of
       the notes are now formalized", keeping "novelty is not
       confirmed";
     - fix the covariance comment of `ConditionStatement.v` (comments
       only), the rows of `esum_tuple_prod` and `clip_energy`, and the
       event count in `Condition/Sat.v`.
   - **The presentation.** `README.md` and `extension/README.md` lead
     with the optimal condition-number theorem. Countable closure comes
     next as a generality result, and the latent-sign identities as
     evidence of persistent dependence.

### Roles

As in phases 6 to 8. **Agent 3 is the master.**
- It assigns the items (its own lane included) and gives agents 1 and 2
  their work in their sessions.
- It writes the statement files and freezes them after the user's
  review.
- It merges in the `integration` clone and alone pushes `main` and tags.
- It keeps the table of items, owners and states in
  `/srv/ellipsoid-fitting/runtime/phase9/assignments.md`.

Agents 1 and 2 take their items from the master. The coordinator assigns
no item; it verifies pushed commits, keeps GitHub in sync and relays the
user's decisions.

### Step 0

1. **The plan and the statements.** The master writes a short plan of
   the four items in `/srv/ellipsoid-fitting/notes/optional-items-plan.md`:
   the components, lanes, order, risks, and untested estimates. The
   plan's section 5.3 estimated about 5,500 lines. The master also writes
   the statement files of the four items at the top of `extension/`, with
   comments that guide the reviewer as in the frozen files. It compiles
   them, pushes `main` and says so in its pane; the coordinator asks the
   user to review them. Items that do not depend on the statement files
   start at once.
2. **The freeze.** Once the user accepts the statement files, the master
   freezes them like the frozen files of phases 5 to 8: their code does
   not change, only the master edits their comments, and
   `scripts/check_sources.py` compares them with the acceptance commit as
   a new baseline. When the theorems exist, their axiom checks and
   expected lists join `make check` on the pattern of
   `check/LatentScopeAssumptions.v`. The user's request permits these
   changes to `scripts/check_sources.py`, `check/` and the `Makefile`, in
   step 0 and at the end of the phase, and the two checker changes of
   item 5, and no other.
3. **No new directories.** New files go in existing directories:
   - statement files at the top of `extension/`;
   - proofs in `extension/Countable/`, `extension/Paired/` or
     `extension/Condition/`;
   - library results in the existing library directories.

   The Rocq servers then need no reconnection.

### Rules for this phase

The rules of phase 8 apply.
- Nothing changes in `theories/`, in the code of the twenty-one frozen
  files (eight in `theories/`, two of phase 5, four of phase 6, two of
  phase 7, five of phase 8), in the check files and expected lists of
  phases 1 to 8, or in the pinned section `tuple_prod` of
  `library/probability/lindeberg.v`.
- The seven theorems keep building at every commit: `universality_theorem`,
  `mixture_theorem`, `paired_theorem`, `latent_sign_theorem`,
  `countable_theorem`, `condition_theorem` and `latent_scope_theorem`.
- Library results are stated over `R : realType` in the library's
  vocabulary.
- Every new file has the documentation header and its README rows.
- Build with `JOBS=3`, and run `make check` before every commit.
- Requests between lanes go through `requests/`.
- The repository gets no journals or progress files.

Phase 9 is done when the following hold:
- the four items R1 to R4 are proved on `main` against the accepted
  statements, and the follow-ups of item 5 are on `main`;
- their axioms are among the eight expected ones;
- `make check` passes;
- the README rows cover every new file;
- `main` is tagged `phase9`.

## Phase 10. The follow-ups of the review of the phase 9 release

Phases 1 to 9 are done (`main` e4c46e1, tag `phase9`). A review of the
phase 9 release, `/srv/ellipsoid-fitting/reviews/phase9-release-review.md`,
accepts its mathematics. On 9 October 2026 the user accepted its four
proposals as this phase.

1. **D. Documentation corrections** (the review's section 1).
   - The contamination is at total variation distance at most lambda / n
     from the family, not exactly lambda / n: the distance is smaller when
     the law of the family has an atom at zero.
   - The comment of `RobustDefinitions.v` should describe what the proof
     does: a comparison through truncation, not an exact identity between
     `robust_sample_law` and `countable_mixture_probability`. That file is
     frozen, so only its comment changes, by the master.
   - The tensorization rows should say "for fixed s > 0" where Var f_d
     tends to 1/4, and describe exactly how the test function is truncated
     coordinate by coordinate.
2. **R7. Robustness of the optimal condition number** (the review's
   section 7.1, its first priority). New corollaries of the frozen
   statements, stated for perturbed point laws P~_d with
   d^2 tv(P~_d, nu_d) -> 0 around an admissible finite or countable
   mixture family of fourth moment 3. The perturbed laws need no moment.
   - The threshold (20): for every fixed C > 1, the probability of a fit
     of condition number at most C tends to 1 if alpha < alpha_C and to 0
     if alpha > alpha_C.
   - The convergence (21) of the optimal data condition number to
     C_star(alpha), for 0 < alpha < 1/4.
   - Both follow from the transfer of `Countable/Robust.v` and
     `condition_theorem`, through the measurable fit events.
3. **T. A finite tensorization constant** (the review's section 7.3).
   - For 0 <= s <= 1 the latent-sign law satisfies the tensorization
     inequality (12) of the frozen `LatentTensorization.v` with
     T_0 = 2 ((1 + s) / (1 - 3 s / 7))^d.
   - On the support, (1/2) (1 - 3 s / 7)^d <= rho <= (1 + s)^d, so
     Var_P f <= U Var_Q f and E_P Var_P(f | X_-j) >= L E_Q Var_Q(f | X_-j),
     with U and L the two bounds.
   - Efron-Stein for the product law Q = mu^d then gives T_0 = U / L.
   - Together with the proved lower bound, this places the optimal
     constant between two explicit exponentials for every fixed s > 0.
4. **I. Reusable identities** (the review's section 7.2).
   - The countable analogue of `tuple_prod_mixture`, and the exact
     identity between `robust_sample_law` of the point law of a countable
     family and `countable_mixture_probability`. With it, the transfer
     bound becomes n tv(P~_d, nu_d), with no truncation term.
   - A probability wrapper for `cl_point_law d` with its marginal
     moments.
   - These are lemmas and need no statement review.

### Roles

As in phases 6 to 9. **Agent 3 is the master.**
- It assigns the items (its own lane included) and gives agents 1 and 2
  their work in their sessions.
- It writes the statement files of R7 and T and freezes them after the
  user's review.
- It merges in the `integration` clone and alone pushes `main` and tags.
- It keeps its table in
  `/srv/ellipsoid-fitting/runtime/phase10/assignments.md`.

Agents 1 and 2 take their items from the master. The coordinator assigns
no item; it verifies pushed commits, keeps GitHub in sync and relays the
user's decisions.

### Step 0

1. **The statements.** The master writes the statement files of R7 and T
   at the top of `extension/`, using the frozen definitions, with
   comments that guide the reviewer. It compiles them, pushes `main` and
   says so in its pane; the coordinator asks the user to review them. D, I
   and the parts of R7 and T that do not depend on the statements start at
   once.
2. **The freeze.** Once the user accepts the statement files, the master
   freezes them like the frozen files of phases 5 to 9, with the
   acceptance commit as a new baseline in `scripts/check_sources.py`.
   When the theorems exist, their axiom checks and expected lists join
   `make check` on the pattern of `check/RobustAssumptions.v`. The user's
   request permits these changes to `scripts/check_sources.py`, `check/`
   and the `Makefile`, in step 0 and at the end of the phase, and no
   other.
3. **No new directories.** New files go in existing directories, so the
   Rocq servers need no reconnection.

### Rules for this phase

The rules of phase 9 apply.
- Nothing changes in `theories/`, in the code of the twenty-six frozen
  files, in the check files and expected lists of phases 1 to 9, or in
  the pinned section `tuple_prod` of `library/probability/lindeberg.v`.
- The eleven theorems keep building at every commit: those of phases 5 to
  9 and the main theorem's checks.
- Every new file has the documentation header and its README rows.
- Build with `JOBS=3`, and run `make check` before every commit.
- The repository gets no journals or progress files.

Phase 10 is done when the following hold:
- D and I are on `main`;
- the statements of R7 and T are proved on `main`, with their axioms
  among the eight expected ones;
- `make check` passes;
- the README rows cover every new file;
- `main` is tagged `phase10`.

## Phase 11. The optimal condition number at every fourth moment

Phases 1 to 10 are done: tag `phase10` is at eda8a06, and `main` 8039877
also pins the eight check files of phase 9. Phase 11 extends the optimal
condition-number theorem of phase 8 from fourth moment 3 to every fixed
fourth moment kappa > 1. Three documents guide it:

- **The math plan,**
  `/srv/ellipsoid-fitting/notes/general-fourth-moment-condition-plan.md`,
  written on the user's machine on 12 October 2026, holds the mathematics.
- **The plan,** `/srv/ellipsoid-fitting/notes/phase11-plan.md`, written by
  the coordinator, is the formal plan.
- **The review,** `/srv/ellipsoid-fitting/reviews/phase11-plan-review.md`,
  is the user's review of the plan. The user approved the plan on 12
  October 2026 with the review's amendments, which the plan incorporates.

The plan of this phase is the plan's sections 3 (the route), 4 (the
statement files), 5 (ownership and items), 6 (order, interfaces and
checkpoint), 7 (risks), 8 (about 7,000 lines, an untested estimate) and 9
(done criteria and release order). This section fixes the roles and the
rules; where they differ, this section wins.

The three results, with c = (kappa - 3)/2 and the curve alpha(C, kappa) of
the math plan's section 2:

1. **The curve.** Take C > 1 and kappa > 1.
   - The root u of the math plan is the unique zero of its function F.
   - alpha(C, kappa) is the value of the constrained semicircle
     variational problem, and it equals
     (1/(3 pi)) int_ell^u (2 - z^2)^(3/2) dz.
   - For fixed kappa, it is continuous and strictly increasing in C, from
     0 to alpha*(kappa).
   - Its inverse C_star(alpha, kappa) is characterized by order.
   - At kappa = 3 it is `condition_alpha` (for C > 1), and its inverse is
     `condition_star` (for 0 < alpha < 1/4).
2. **The data theorem.** Take finite and countable mixtures of fourth
   moment kappa, mixture-averaged as in the frozen statements.
   - The probability of an exact fit of condition number at most C tends
     to 1 if alpha < alpha(C, kappa), and to 0 if alpha > alpha(C, kappa).
   - For 0 < alpha < alpha*(kappa), the optimal data condition number
     tends to C_star(alpha, kappa) in probability.
3. **Robustness.** Both conclusions hold for i.i.d. points of laws P_d
   with d^2 tv(P_d, nu_d) -> 0, where nu_d is the point law of such a
   countable family, or of such a finite family through `finite_weights`.

Not in this phase:
- the critical point alpha = alpha(C, kappa);
- uniformity as kappa -> 1;
- monotonicity in kappa;
- endpoint rates and the asymptotic for small C - 1 (the math plan's
  section 8).

### Roles

As in phases 6 to 10. **Agent 3 is the master.**
- It assigns the items (its own lane included) and gives agents 1 and 2
  their work in their sessions.
- It writes the statement files and freezes them after the user's
  review, and it creates the new directory.
- It merges in the `integration` clone and alone pushes `main` and tags.
- It keeps the table of items, owners and states in
  `/srv/ellipsoid-fitting/runtime/phase11/assignments.md`.

Its starting point is the plan's lane proposal:
- **A:** M1 to M5 (the surrogate maximizer, the Gaussian comparison, the
  spectral limit);
- **B:** B1, G1, D1, D2, A2, A3 (the shared transformed cone, the Gaussian
  witness and gap, the two data directions, the countable and robust
  versions);
- **C:** step 0, S1 to S5 (the curve), A1, A4, the checks and the release.

The shared files have the owners of the plan's section 5:
- `library/probability/variational.v`: lane C in this phase;
- a new library module for the general form of M1: lane A;
- `extension/ConditionKappa/Cone.v`, the single definition of the
  transformed cone and of its support function: lane B.

Agents 1 and 2 take their items from the master. The coordinator assigns
no item; it verifies pushed commits, keeps GitHub in sync and relays the
user's decisions.

### Step 0

1. **The launch.**
   - The master fast-forwards `lane/c` and `integration` to `main`, and
     records the ownership in its table.
   - It gives M1 and M2 to agent 1 and B1 to agent 2. These need no
     statement file.
   - It creates `extension/ConditionKappa/` with the headers of its first
     files (`Geometry.v`, `Cone.v`, `Scalar.v`), registers them in
     `_CoqProject` and pushes `main`.
   - The user then reconnects the three Rocq servers (`/mcp`) once.
2. **The definitions and the interfaces.**
   - The master writes `extension/ConditionKappaDefinitions.v` and the
     interfaces I1 to I4 of the plan's section 6, in the headers of the
     files that consume them, and pushes `main`.
   - S1, S2 and G1 start from this push.
   - Each interface gets its precise type from the first conditional
     lemma that takes it as a hypothesis. A comment alone does not fix
     normalizations or quantifiers.
3. **The statements.**
   - The master writes `ConditionKappaCurveStatement.v`,
     `ConditionKappaStatement.v` and `ConditionKappaRobustStatement.v` at
     the top of `extension/`. Their comments guide the reviewer, as in the
     frozen files.
   - It compiles them, pushes `main` and says so in its pane.
   - The coordinator asks the user to review the four files.
4. **The checks.** The user's launch permits changes to
   `scripts/check_sources.py`, `check/` and the `Makefile` at the three
   moments below, and no other.
   - **The freeze**, once the user accepts the four statement files:
     - the master freezes them like the frozen files of phases 5 to 10:
       their code does not change, and only the master edits their
       comments;
     - `scripts/check_sources.py` compares them with the acceptance commit,
       as a new baseline;
     - in the same commit, the two check files and the two expected lists
       of phase 10 are compared byte for byte with eda8a06, as a separate
       baseline.
   - **The axiom checks.** When the theorems exist, a commit P adds three
     check files, `check/ConditionKappaCurveAssumptions.v`,
     `check/ConditionKappaAssumptions.v` and
     `check/ConditionKappaRobustAssumptions.v`, on the pattern of
     `check/ConditionRobustAssumptions.v`, and `make check` runs them.
     - Each has an expected list of seven axioms: the eight of
       `check/assumptions.expected` without `Classical_Prop.classic`.
       Fewer are allowed.
     - Every older expected list stays unchanged.
   - **The pin.** A later commit compares those six files byte for byte
     with P, as a separate baseline, keeping every older one. The tag
     `phase11` goes on that checked commit (the plan's section 9).
5. **The checkpoint.** When S2 and M2 are on `main`, the master says so in
   its pane.
   - The coordinator inspects their proofs as well as their statements:
     - the scalar duality for both signs of c and for c = 0;
     - the coercivity for every c > -1;
     - both terms of the comparison of objective values;
     - the axiom reports.
   - The coordinator re-estimates M3 to M5 and reports to the user.
   - Independent items continue meanwhile. A defect is fixed before
     downstream work relies on the affected result.

### Rules for this phase

The rules of phase 10 apply.
- **Unchanged files.** Nothing changes in:
  - `theories/`;
  - the code of the twenty-eight frozen files;
  - the check files and expected lists of phases 1 to 10;
  - the pinned section `tuple_prod` of `library/probability/lindeberg.v`.
- **Theorems that keep building.** The fourteen theorems that
  `make check` checks keep building at every commit.
  - A generalized lemma keeps its old statement under its old name.
  - This holds in particular for the lemmas of `extension/Condition/`
    that the kappa = 3 theorems use.
- **No unproved step.** No commit contains `Admitted`, `Axiom` or
  `Parameter`.
  - A lane that needs a result not yet proved states it as an explicit
    hypothesis of its lemma, as `GaussianWitness.v` took the limit of
    `GaussianCone.v` in phase 8.
  - The lane removes the hypothesis when the result lands.
- **Lane A's quota.** Lane A commits M1 to M5 in small, self-contained
  steps. If its account is throttled, the master reassigns the next item
  rather than wait.
- **Robustness** uses `robust_transfer_tv` and its exact bound.
- **Constants** are changed by their role. The data fourth moment and the
  transformed base change; Gaussian constants such as the `3^(1/4)` of the
  regularity bound do not.
- **Library results** are stated over `R : realType` in the library's
  vocabulary. Nothing in `library/` mentions ellipsoid fitting. Generic
  lemmas use the second moment of the law, not the semicircle's 1/2.
- **Documentation.** Every new file has the documentation header and its
  README rows, with the actual hypotheses.
- **Building.** Build with `JOBS=3`, and run `make check` before every
  commit.
- **Requests** between lanes go through `requests/`, which the master
  deletes at the end.
- **No journals.** The repository gets no journals or progress files.

Phase 11 is done when the following hold:
- the three theorems prove the accepted statements on `main`. Their names
  are fixed in step 0; the plan proposes `condition_kappa_curve_theorem`,
  `condition_kappa_theorem` and `condition_kappa_robust_theorem`;
- their axioms are among the seven of their expected lists;
- the kappa = 3 implications of item A4 are proved;
- the phase 10 files are pinned to eda8a06, and the six new files to P;
- `make check` passes;
- the README rows cover every new file;
- `main` is tagged `phase11` at the checked pin commit.

## Phase 12. Library-reuse targets from the OpenAI math collection

Phases 1 to 11 are done (tag `phase11` at 48ecb60; `main` a6d542f).
Phase 12 formalizes, over `R : realType`, seven complete theorems from
manuscripts of the OpenAI math collection whose proofs reuse this
library. The new files are Rocq formalizations of credited arguments:
each cites its manuscript and, where it follows one, a Lean module of the
collection. Four documents guide the phase:

- **The candidates review,**
  `/srv/ellipsoid-fitting/reviews/rocq-library-reuse-candidates-2026-10-13.md`,
  is the user's review of the candidates. It fixes the targets and warns
  against unmeasured estimates.
- **The plan,** `/srv/ellipsoid-fitting/notes/phase12-plan.md`, written by
  the coordinator, is the formal plan.
- **The plan review,**
  `/srv/ellipsoid-fitting/reviews/phase12-plan-review.md`, is the user's
  review of the plan, with the user's decisions. The user approved the
  plan on 13 October 2026 with the review's amendments, which the plan
  incorporates.
- **The sources,** `/srv/ellipsoid-fitting/papers/openai-math-1581d4c/`,
  are the TeX of the cited manuscripts and two Lean directories of the
  collection (`openai/math` at 1581d4cbd, Apache License 2.0).

The plan of this phase is the plan's sections 3 (the targets), 4 (step 0),
5 (ownership and items), 6 (order and checkpoint), 8 (risks) and 9 (done
criteria). This section fixes the roles and the rules; where they differ,
this section wins.

The targets, with the plan's precise statements:

1. **T1. Gaussian matrix series** (family 154). For symmetric H_j,
   S = sum_j H_j^2 and g of law `gauss r`:
   E tr((sum_j g_j H_j)^(2q)) <= (2q - 1)!! opnorm(S)^(q-1) tr S for every
   q >= 1. The rectangular corollary follows by the symmetric dilation,
   with no ambient dimension in the bound.
2. **T2. Tensor packing** (154), in finite dimensions.
3. **T3. Sharp GOE upper edge** (227): E lambda_max(`goe_mx a`) <= 2, and
   P(lambda_max >= 2 + t) <= exp(-d t^2/4) for every t >= 0, for W and
   -W. `lambda_max` is a library definition, frozen with T3.
4. **T4. SK spectral gap** (227). Take 0 <= beta < 1/2 and
   kappa = (1 - 2 beta)/2. There are measurable events E_n of probability
   tending to one on which kappa Var_nu(f) <= E(f) for every f, uniformly
   over s in [0, 1] and fields theta. Here nu is the Ising law with
   interaction s J(a) and field theta, and E is the per-site heat-bath
   Dirichlet form. The covariance bound opnorm Cov_nu(x) <= kappa^(-1) is
   a corollary.
5. **T5. Orthogonal splitting** of L >= 1 positive semidefinite matrices
   (126): projections, possibly zero, that sum to the identity, with
   constant 2^(L-1) and the overlaps summed over ordered pairs.
6. **T6. Sign/Gaussian comparison** for the Ising perceptron pressure
   (222): |E_sign p_N - E_Gauss p_N| <= C M N^(-3/2) for N >= 1 and f of
   class C^3 with f, f', f'' and f''' bounded. C depends only on the four
   bounds, uniformly in M and N.
7. **T7. Capped variance** for random k-SAT (235): the largest
   satisfiable prefix length V_n up to the cap 2^(k+1) n has
   Var(V_n) = O_k(n^(1 + 2/k)).

Not in this phase:
- T8, the compressibility lemma of 239, is deferred. Its note may be
  prepared meanwhile, outside the repository; it does not delay the
  release.
- The candidates review's longer projects (096, 140, the field concavity
  and the repair of 222, 139, 097) and its classical inputs (093, 117,
  326, 102).

### Roles

As in phases 6 to 11. **Agent 3 is the master.**
- It assigns the items (its own lane included) and gives agents 1 and 2
  their work in their sessions.
- It creates `applications/`, writes the statement and definitions files
  and `library/matrix/lambda_max.v`, and freezes them after the user's
  review.
- It merges in the `integration` clone and alone pushes `main` and tags.
- It keeps the table of items, owners and states in
  `/srv/ellipsoid-fitting/runtime/phase12/assignments.md`.

Its starting point is the plan's lane proposal:
- **A:** T1, then T2 and T6;
- **B:** T3, then T4b (the good-disorder event) and T7;
- **C:** step 0, T5, T4a (the deterministic gap), the T4 assembly, the
  checks and the release.

Agents 1 and 2 take their items from the master. The coordinator assigns
no item; it verifies pushed commits, keeps GitHub in sync, relays the
user's decisions and runs the measurement checkpoint.

### Step 0

1. **The handoffs.** Before the launch, each agent wrote a handoff,
   `/srv/ellipsoid-fitting/runtime/<clone>/phase12-handoff.md`, merged
   `main` into its lane branch, and had its context cleared, as the user
   decided. Read your handoff after this file and the plan.
2. **The infrastructure.** The user's launch permits this commit
   (item 4).
   - The master creates `applications/` (logical root
     `GaussianApplications`), with its README and the headers of its
     first files.
   - `_CoqProject` gets `-Q applications GaussianApplications` and every
     new `.v` file, in the block of its directory. The root alone builds
     nothing.
   - The `Makefile` gets the pattern rule `applications/%.vo`.
   - `scripts/check_sources.py` changes in four ways:
     - its scan for `Admitted`, `Axiom`, `Parameter` and `Conjecture`
       covers `applications/`;
     - the import rules of `library/` apply to `applications/`: no
       module of Stdlib's real analysis, neither `Rstruct` nor
       `Rstruct_topology`, and nothing of `EllipsoidFitting` or
       `EllipsoidUniversality`;
     - no module of `library/` requires a module of
       `GaussianApplications`;
     - an omitted axiom report is a failure: the checker requires one
       report per theorem of its table, 17 now and 24 after commit P.
   - `scripts/stale_citations.py` scans `applications/`, and skips
     external Lean references marked explicitly. The plan proposes the
     marker `Lean:`.
   - The master mutation-tests these rules in a scratch copy outside the
     repository, and lists the mutations in the commit message (the
     plan's section 4.2).
   - It pushes `main`, and the three lanes merge it. Only then does the
     user reconnect the three Rocq servers (`/mcp`).
   - Work that needs no statement file starts at once: T1's trace
     recursion, T3's comparison and T5's two-matrix estimate.
3. **The statements.**
   - The master writes the statement files at the top of `applications/`
     in two batches. Batch 1 holds T1, T3 and T5, with
     `library/matrix/lambda_max.v`. Batch 2 holds T2, T4, T6 and T7, each
     with its definitions file.
   - T4's definitions (`SKGapDefinitions.v`) are settled first. T4a and
     T4b begin work that depends on them only after they are frozen. If a
     lane is waiting for them, the master sends them for review ahead of
     the rest of batch 2.
   - The master compiles each batch, pushes `main` and says so in its
     pane. The coordinator asks the user to review the batch, with the
     list of library definitions its statements depend on.
   - Comments guide the reviewer and give the provenance (see the rules).
4. **The checks.** The user's launch permits changes to
   `scripts/check_sources.py`, `scripts/stale_citations.py`, `check/` and
   the `Makefile` at the following moments, and no other. Every existing
   baseline and pin is kept, and each change is mutation-tested in a
   scratch copy (the plan's section 4).
   - **The infrastructure commit** of item 2.
   - **Each freeze.** Once the user accepts a batch, the master freezes
     its statement and definitions files like the frozen files of phases
     5 to 11. Their code is compared with the acceptance commit, as a new
     baseline, and only the master edits their comments. The master also
     protects every library definition that the statements unfold to and
     that is not yet protected. It either pins the definition's section,
     as the section `tuple_prod` is pinned, or freezes a check file that
     proves a characterization independent of its implementation. The
     commit message says which. A characterization states, in the frozen
     check file, a property that determines the object, not a lemma
     name: for `gauss n`, its value on measurable boxes as the product of
     the standard normal probabilities of the sides (`gauss_unique` can
     prove that this determines the measure).
   - **The axiom checks.** When the theorems exist, a commit P adds one
     check file per target in `check/`, on the pattern of
     `check/ConditionKappaAssumptions.v`: a definition whose type is the
     frozen statement and whose body is the theorem, then
     `Print Assumptions`. `scripts/check_sources.py` fixes their code.
     Each has an expected list of the seven axioms of phase 11 (the eight
     of `check/assumptions.expected` without `Classical_Prop.classic`).
     Fewer are allowed, and every older expected list stays unchanged.
     The checker then requires all 24 reports.
   - **The pin.** A later commit compares the new check files and
     expected lists byte for byte with P, as a separate baseline. The tag
     `phase12` goes on that checked commit.
5. **The checkpoint.** When T1, T3 and T5 are on `main`, the master says
   so in its pane.
   - The coordinator records, for each, the lines added, the hours and
     the new definitions. It also inspects the proofs: statements,
     hypotheses actually used and axiom reports.
   - It assesses the two-spin argument of T4 separately, since T1, T3 and
     T5 say little about it.
   - It then estimates the remaining items and reports to the user.
   - The checkpoint blocks nothing: work continues meanwhile.

### Rules for this phase

The rules of phase 11 apply.
- **Unchanged files.** Nothing changes in:
  - `theories/` and `extension/`;
  - the code of the frozen files of phases 1 to 11;
  - the check files and expected lists of phases 1 to 11;
  - the pinned section `tuple_prod` of `library/probability/lindeberg.v`.

  The 17 theorems that `make check` checks keep building at every
  commit.
- **Ownership.** Files keep their owners of phase 5. These new files take
  the owners of the plan's section 5:
  - `library/matrix/lambda_max.v`: lane C;
  - `library/random_matrix/goe_edge.v` and
    `library/probability/efron_stein_omission.v`: lane B;
  - `library/matrix/tensor_packing.v`: lane A;
  - `applications/`: as the master assigns.

  One file has one owner at a time.
- **Library and applications.**
  - `library/` statements and definitions are general, over
    `R : realType`, in the library's vocabulary. None is about the SK
    model, perceptrons, SAT or sign matrices. Library comments may cite
    the sources.
  - `applications/` is also over `realType`. It requires only `library/`
    and MathComp, never Stdlib's reals or MathComp's bridges to them.
    Dependencies flow only from `applications/` to `library/`.
  - Every new `.v` file is registered in `_CoqProject` in the commit that
    adds it.
- **Provenance.** Every new file's header cites the manuscript (title and
  family number), its section or lemma, the collection revision
  1581d4cbd, and any Lean module whose argument the file follows, after
  the marker `Lean:`. It calls the file a Rocq formalization of the
  credited argument. Nothing is copied from the Lean code.
- **Sources.**
  - The TeX of the collection is the mathematical source. Lean sources
    may be read for routes and conventions.
  - Where the frozen statement, the TeX and a Lean statement differ, the
    file header says so.
  - If a manuscript step fails, the lane stops and reports to the master,
    who reports to the user. A change of a frozen statement or
    definition, or a fall-back to an implication with explicit
    hypotheses, is the user's decision.
- **No unproved step.** No commit contains `Admitted`, `Axiom` or
  `Parameter`. During the work, a missing result may be an explicit
  hypothesis of a lemma; it is removed when the result lands.
- **Quotas.** Lanes commit in small, self-contained steps. If an account
  is throttled, the master reassigns the next item rather than wait.
- **Documentation.** Every new file has the documentation header and its
  README rows (`library/README.md` or `applications/README.md`), with the
  actual hypotheses.
- **Building.** Build with `JOBS=3`, and run `make check` before every
  commit.
- **Requests** between lanes go through `requests/`, which the master
  deletes at the end.
- **No journals.** The repository gets no journals or progress files.
  The handoffs and the master's table live in
  `/srv/ellipsoid-fitting/runtime/`.

Phase 12 is done when the following hold:
- T1 to T7 prove their accepted statements on `main`;
- their check files verify the frozen statements, and their axioms are
  among the seven of their expected lists;
- the checker requires all 24 reports, and the commit messages record the
  mutation tests;
- the new check files are pinned to P;
- `make check` passes;
- the README rows cover every new file;
- `main` is tagged `phase12` at the checked pin commit.

## Phase 13. The SAT threshold, the PSD pilot and reusable library modules

Phases 1 to 12 are done (tag `phase12` at 9046883). Phase 13 completes
the main theorem of one manuscript of the OpenAI math collection and
starts a second, with their general mathematics as explicit library
deliverables. Five documents guide it:

- **The direction,** `/srv/ellipsoid-fitting/reviews/phase13-direction.md`,
  is the user's text of 14 October 2026. The success criterion it sets,
  two completed applications supported by useful, independently
  reviewable mathematical modules, is met at the end of phase 14. Its
  point 4 (upstream contributions) is replaced by decision D6.
- **The plan,** `/srv/ellipsoid-fitting/notes/phase13-plan.md`, written by
  the coordinator.
- **The plan review,**
  `/srv/ellipsoid-fitting/reviews/phase13-plan-review.md`, is the user's
  review: it approves the plan with decisions D1 to D12 and six
  amendments, which the plan incorporates.
- **The maps,** `/srv/ellipsoid-fitting/notes/phase13-maps/`, are
  background: the SAT and PSD routes, draft statements (the PSD drafts in
  `psd-draft/` compile and follow the user's decisions), item sizes, the
  audit checklist of the PSD manuscript, the repository rules. Where they
  differ from the plan (file names, directories, owners, constants), the
  plan wins.
- **The sources,** `/srv/ellipsoid-fitting/papers/openai-math-1581d4c/`:
  the TeX of the manuscripts, and the Lean directories `RandomSAT` and
  `Combinatorics/MatchingPSD` of the collection (`openai/math` at
  1581d4cbd, Apache License 2.0).

The plan of this phase is the plan's sections 2 (the targets), 3 (the
library deliverables), 4 (step 0), 5 (ownership and items), 6 (order,
checkpoint, audit and gate), 9 (risks) and 11 (done criteria). This
section fixes the roles and the rules; where they differ, this section
wins.

The targets, with the plan's precise statements:

1. **T9. The SAT threshold** ("A Limiting Satisfiability Threshold for
   Every Fixed Clause Size", family 235). For every k >= 3 there is
   alpha > 0 such that the probability that floor(c n) independent uniform
   proper k-clauses on n variables are satisfiable tends to 1 for
   0 <= c < alpha and to 0 for c > alpha. It is stated over the frozen T7
   definitions.
2. **T10. The exact normalization of PSD factors** ("Exponential PSD
   rank of positively shifted matching matrices", family 126, Lemma
   "Normalization of PSD factors"). A general statement: factors of the
   same size with the same pairings, row traces at most m and column
   traces at most r.
3. **T11. Product smoothing of matrix squares** (126, Theorem "Fourier
   smoothing of matrix squares"). A general statement with shared
   witnesses: one global sum-of-squares family, with one row dimension
   for all histories and branches, carries the averaged potential
   estimate. A tuple of positive product weight, chosen from the same
   family, carries the Fourier coefficient estimate. Finite laws mu_i and
   nu_i, lambda > 0, frequencies in `'M['F_2]_(t, a)`.
4. **T12. Convergence from approximate minimum inequalities** (235, Lemma
   "Balanced comparisons"). For a real sequence with
   u(r + s) >= min(u r, u s) - A min(r, s)^(-beta) for comparable sizes
   and the neighbor step, a finite-size lower bound for every beta > 0;
   if the sequence is bounded, it converges, and its limit satisfies the
   same bound. The constant is Lean's, 3^beta / ((3/2)^beta - 1), larger
   than the manuscript's.

The PSD main statement (126, `introduction.tex` lines 37-44) is written,
reviewed and frozen in this phase (batch 3), with K after the real type
and before rho. Its proof is phase 14, which the user authorizes
separately.

Not in this phase:
- the proof of the PSD main theorem, the PSD duality and the corollary on
  affine semidefinite lifts, which belong to phase 14;
- Hall's theorem: the SAT proof uses a minimal unsatisfiable core
  instead;
- Fourier analysis on general finite abelian groups;
- T8, still deferred;
- any upstream submission (D6).

### Roles

As in phases 6 to 12. **Agent 3 is the master.**
- It assigns the items (its own lane included) and gives agents 1 and 2
  their work in their sessions.
- It assembles the statement batches, writes the statement and
  definitions files at the top of `applications/`, records the acceptance
  inventory, and freezes the batches after the user's review.
- It creates the new directories.
- It merges in the `integration` clone and alone pushes `main` and tags.
- It keeps the table of items, owners and states in
  `/srv/ellipsoid-fitting/runtime/phase13/assignments.md`.

Its starting point is the plan's lane proposal:
- **A:** the Boolean Fourier and T11 definitions first (P0), then the
  Boolean Fourier analysis (P2) and T11 (P3). This is the critical path.
- **B:** packet S's statements first (S0), then the commuting operators,
  the binomial means, the SAT application and T9.
- **C:** step 0 and the batches, T12 once the infrastructure is merged,
  T10, the PSD main statement, the skeleton of its final step (P6), the
  checks and the release.

Agents 1 and 2 take their items from the master. The coordinator assigns
no item. It verifies pushed commits, keeps GitHub in sync, relays the
user's decisions, and runs the checkpoint and the audit of the PSD
manuscript.

### Step 0

1. **The handoffs.** Before the launch, each agent wrote a handoff,
   `/srv/ellipsoid-fitting/runtime/<clone>/phase13-handoff.md`, merged
   `main` into its lane branch, and had its context cleared after the
   coordinator read the handoff, as the user decided. Read your handoff
   after this file and the plan.
2. **The infrastructure.** The user's launch permits this commit (item
   5).
   - The master creates `library/analysis/`, `library/combinatorics/` and
     `applications/PsdRank/`, each with the header of its first file,
     registered in `_CoqProject`, and their rows in the READMEs.
   - No script change is needed: the checks scan subdirectories, and the
     pattern rule `library/%.vo` covers them. Mutation tests confirm it.
   - The master pushes `main`, and every lane merges it. Then the user
     reconnects the three Rocq servers (`/mcp`), and the coordinator
     confirms it to the master. Until then, no lane uses a Rocq server on
     a file of the new directories; work in existing directories (lane A
     in `fourier/`, lane B in `probability/`) continues meanwhile.
3. **The statements.** Three batches.
   - **Who writes what.** Each lane writes, as the first commit of its
     item, the definitions and the `_statement` definitions of its own
     library files. The master merges these commits, adds the statement
     files at the top of `applications/`, compiles the batch, pushes
     `main` and says so in its pane. The coordinator asks the user to
     review it, with the list of the library definitions its statements
     unfold to.
   - **Batch 1:** T9 (`SatThresholdDefinitions.v`,
     `SatThresholdStatement.v`) and T12 (`MinSuperadditiveStatement.v`),
     with packet S from lane B.
   - **Batch 2:** T10 (`PsdNormalizationStatement.v`) and T11
     (`ProductSmoothingStatement.v`), with the definitions T11 unfolds to
     and packet P's statements of `boolean_fourier.v` from lane A, and
     packet P's statements of `psd_factorization.v` from the master.
   - **Batch 3:** the PSD main statement (`PsdRankDefinitions.v`,
     `PsdRankStatement.v`), as soon as `psd_factorization` is on `main`.
     It goes to the user with the full PSD audit, and is accepted only
     after it, unless the user explicitly defers that acceptance. Only
     the statement and the definitions it uses are frozen; variants and
     the corollary's definitions stay in an unfrozen file.
4. **The general statements.** Packets S and P hold the general
   statements that the targets use, written as compiled `Prop`-valued
   definitions (`Definition foo_statement : Prop := ...`) in their library
   files.
   - They are reviewed with their batch, accepted, not frozen. A
     `Prop` definition asserts nothing, so no `Admitted` is needed.
   - **The acceptance inventory.** At each acceptance, the master records
     in the checker, in the commit of the freeze, one entry per accepted
     statement: the full acceptance commit hash, the path, the declaration
     name, and the full proposition as `Print` shows it at that commit,
     with its section parameters and hypotheses. The inventory stays with
     the permanent checks.
   - An application proof that uses a general statement waits for its
     acceptance; for example, the SAT tails (A2) use Chebyshev's
     inequality of packet S. A library proof may start before, at the
     lane's risk.
   - A `_statement` definition is kept until its acceptance, even if its
     proof is ready earlier. When the proof lands after acceptance, the
     lemma is stated with the accepted text, and the `_statement`
     definition is deleted in the same commit, whose message says so.
     Comments outside the defining file cite the lemma, not the
     `_statement` name; the deletion commit removes every remaining
     citation of it, or the stale-citation check fails. A proof that took
     the statement as a hypothesis replaces it by the lemma; in another
     lane's file, its owner does it first and the master merges the two
     together.
   - A change to an accepted statement goes back to the user.
5. **The checks.** The user's launch permits changes to
   `scripts/check_sources.py`, `check/` and the `Makefile` at the moments
   below, and no other. Every existing baseline and pin is kept. Each
   change is mutation-tested in a scratch copy under the ignored `build/`
   of the master's clone, and the commit message lists the mutations.
   - **The infrastructure commit** of item 2, if it needs a change.
   - **Each freeze.**
     - Once the user accepts a batch, its files are frozen like the
       frozen files of phases 5 to 12. Their code is compared with the
       acceptance commit, as a new baseline, and only the master edits
       their comments.
     - The project-defined notions used by the frozen statements and by
       the accepted packets are protected by a new code-fixed check file,
       `check/Phase13Definitions.v`, with characterizations that determine
       each object and write out every library definition they mention,
       down to MathComp definitions. Proof bodies are not frozen;
       existing protections are reused.
     - Freeze 1 creates it, for packet S (for example `unif_mean`,
       `binomial_mean`, `meet_avg`). Freeze 2 extends it with what T11 and
       packet P use (the F_2 pairing, the Boolean character, the Fourier
       coefficient, the block degree and distance, low block degree,
       `prob_vec`, `prod_avg`, `weighted_gram`, `smoothing_hyps`). Freeze
       3 extends it with `psd_factorization`. Each freeze extends the
       file without altering it: the checker keeps each earlier freeze's
       constant and requires it as an unchanged prefix.
     - `make check` compiles that file as it compiles
       `check/ApplicationsDefinitions.v`. Its output is deleted before
       regeneration and is a required output, checked separately from the
       theorem reports.
   - **The axiom checks.** When the theorems exist, a commit P adds one
     check file per target, on the pattern of
     `check/SatVarianceAssumptions.v`: a definition whose type is the
     frozen statement and whose body is the theorem, then
     `Print Assumptions`.
     - Each has an expected list of the seven axioms of phases 11 and 12,
       so `Classical_Prop.classic` is not allowed; fewer are allowed.
       Older lists are unchanged.
     - The checker requires all 28 theorem axiom reports.
     - The same commit adds `check/LibraryStatements.v`, code-fixed. It
       states every proposition of the acceptance inventory in full and
       proves each by its library lemma. The checker requires that every
       inventory entry is covered. `make check` compiles it into a second
       required output, deleted before regeneration.
     - Mutation tests, besides those of phase 12: `Classical_Prop.classic`
       in a new target or its list; a missing, a duplicated and a
       substituted report; an accepted statement omitted from
       `LibraryStatements.v`; a packet definition changed while the text
       of `LibraryStatements.v` stays the same; after a successful build,
       the compile command of either auxiliary check file deleted while
       its old output still exists. The definition mutations are repeated
       after freeze 3.
   - **The pin.** A later commit compares ten new files byte for byte
     with P, as a separate baseline: the four theorem check files, their
     four expected lists, `check/Phase13Definitions.v` and
     `check/LibraryStatements.v`. The tag `phase13` goes on that checked
     commit.
6. **The checkpoint, the audit and the skeleton.**
   - **The checkpoint** does not stop any work. When the Boolean Fourier
     definitions and lemmas, T12 and the SAT library modules are on
     `main`, the master says so in its pane. The coordinator records
     lines, hours and new definitions, inspects the proofs and
     re-estimates the rest.
   - **The PSD audit** (coordinator) runs alongside unrelated SAT and
     library work and does not stop it. Its relevant findings accompany
     the review before freeze 2 (the parity and final-step items, since
     freeze 2 fixes the Boolean encoding) and before freeze 3 (the full
     audit).
   - **The skeleton P6** compiles the final step of the PSD theorem
     against explicit hypotheses for local averaging and the parity
     functional, and names each of them. Compiling it does not validate
     those hypotheses. It may be missing from the phase 13 tag.
   - Both the full audit and the skeleton are required before the user
     authorizes phase 14.

### Rules for this phase

The rules of phase 12 apply.
- **Unchanged files.** Nothing changes in:
  - `theories/` and `extension/`;
  - the code of the 42 frozen files of phases 1 to 12;
  - the check files and expected lists of phases 1 to 12;
  - the pinned sections `tuple_prod` of
    `library/probability/lindeberg.v` and `lambda_max` of
    `library/matrix/lambda_max.v`;
  - the code of `check/ApplicationsDefinitions.v`.

  The 24 theorems that `make check` checks keep building at every
  commit. T7's frozen definitions are reused, never edited.
- **Ownership.** Files keep their owners of phases 5 and 12. The new
  files take the owners of the plan's section 5. One file has one owner
  at a time. Each lane registers its new files in `_CoqProject` in the
  commit that adds them, and coordinates merge conflicts there with the
  master.
- **Library and applications.**
  - `library/` results are general, over `R : realType` or a weaker
    structure when that is enough; combinatorial results are over finite
    types with no field.
  - No model appears in `library/`: not the SK model, perceptrons, SAT
    and its clauses, sign matrices, matching matrices and their cells,
    odd cuts or the parity system. Before the release, a lane other than
    its author reviews each new library file for this.
  - A general result enters the library only if a proof of this phase or
    of the planned phase 14 uses it.
  - Before adding a lemma, search MathComp, MathComp-Analysis and the
    library for it, and use the weakest suitable structure. Each general
    module ends with an example that does not depend on an application.
- **Upstream (D6).** No upstream pull request or other external
  submission or contact, for MathComp or MathComp-Analysis. Agents push
  only their branch to the hub. Internal API checks, design notes and
  examples remain allowed; an upstream submission package is not a
  deliverable.
- **Provenance.** Every new file's header cites the manuscript (title
  and family number), its section or lemma, the collection revision
  1581d4cbd, and any Lean module whose argument the file follows, after
  the marker `Lean:`. It calls the file a Rocq formalization of the
  credited argument. Nothing is copied from the Lean code. The header
  states each departure:
  - the minimal unsatisfiable core instead of Hall's theorem;
  - T12's comparable-size hypothesis and its constant, larger than the
    manuscript's;
  - the route of T10;
  - the shared witnesses, the weighted laws and lambda > 0 of T11.
- **Sources.** The TeX of the collection is the mathematical source; the
  Lean sources may be read for routes and conventions. If a manuscript
  step fails, the lane stops and reports to the master, who reports to
  the user.
- **No unproved step.** No commit contains `Admitted`, `Axiom` or
  `Parameter`. During the work, a missing result may be an explicit
  hypothesis of a lemma; it is removed when the result lands.
- **Quotas.** Lanes commit in small, self-contained steps. If an account
  is throttled, the master reassigns the next item rather than wait. If
  lane A is throttled, T11 moves to the first free lane: lane B after T9,
  or lane C once its step 0 work is done.
- **Documentation.** Every new file has the documentation header and its
  README rows, with the actual hypotheses.
- **Building.** Build with `JOBS=3`, and run `make check` before every
  commit.
- **Requests** between lanes go through `requests/`, which the master
  deletes at the end.
- **No journals.** The repository gets no journals or progress files.
  The handoffs and the master's table live in
  `/srv/ellipsoid-fitting/runtime/`.

Phase 13 is done when the following hold:
- T9, T10, T11 and T12 prove their frozen statements on `main`;
- their check files verify the frozen statements, and their axioms are
  among the seven of their expected lists;
- the checker requires all 28 theorem axiom reports and the two
  auxiliary outputs;
- every entry of the acceptance inventory is proved with its full
  accepted proposition, and `check/LibraryStatements.v` covers every
  entry. An accepted statement of an optional item that is not proved at
  the release is withdrawn, with the user's agreement;
- the definitions used by the frozen statements and the accepted packets
  are protected in `check/Phase13Definitions.v`;
- the PSD main statement is accepted and frozen, unless the user deferred
  that acceptance;
- the commit messages record the mutation tests;
- the ten new check files and expected lists are pinned to P;
- `make check` passes;
- the README rows cover every new file;
- `main` is tagged `phase13` at the checked pin commit.

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
- On the VM, this toolchain exists only in the pinned Docker image. The
  host's opam switches are older; never use them. Run every `make` and
  `rocq` command through the wrapper, with the name of the clone, from that
  clone:
  `/srv/ellipsoid-fitting/environment/proof-shell.sh agent2 make check ROCQ_SWITCH= JOBS=4`.
  It mounts that clone writable and the rest of `/srv/ellipsoid-fitting/`
  read-only, with 4 CPUs and 12 GiB.
- On a 16-vCPU machine shared by three agents, use `JOBS=4`. On a Mac with
  16 cores and `JOBS=12`, a full build took 13 minutes; expect longer here.
- `make build` recompiles only what changed and what depends on it.
- Each agent has its own clone and its own build. Never share `.vo` files.
- `.mcp.json` starts `rocq-mcp-evolve` in the switch `rocq-analysis`. On
  the VM, `/srv/ellipsoid-fitting/environment/start-agent.sh` starts each
  client in its clone with only one server, `rocq-evolve`, which runs in
  the image on that clone; it ignores `.mcp.json` and the servers of the
  earlier project. One agent owns one server session. A proof found
  interactively counts only once it is saved in the `.v` file and
  `make check` passes.

## Writing

Write plainly: short sentences, no em-dashes, no marketing, no emoji. Say
what was checked and how, and never claim more than the checks show.
