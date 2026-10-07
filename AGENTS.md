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

Phases 1 to 3 below are done (`main` 3998195). The current work is
phase 4, described after them.

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
