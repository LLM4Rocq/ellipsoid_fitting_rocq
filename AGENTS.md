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

Phases 1 to 4 below are done (`main` d3bb5fb, tag `phase4`). The current
work is phase 5, described after phase 4.

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
