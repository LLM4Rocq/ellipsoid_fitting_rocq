# Ellipsoid fitting in Rocq

This repository contains a Rocq proof of the three main results of *The sharp
SAT/UNSAT phase transition in random ellipsoid fitting* (Misiakiewicz and Wen,
[arXiv:2608.10184v1](https://arxiv.org/abs/2608.10184v1)).

Let x_1, ..., x_n be independent standard Gaussian points of R^d, with n = n(d)
growing with d.

1. **thm:main.** Let p(n, d) be the probability that some positive
   semidefinite matrix S satisfies x_i^T S x_i = d for every i. If
   limsup n/d^2 < 1/4, then p(n, d) tends to 1. If liminf n/d^2 > 1/4, then
   p(n, d) tends to 0.
2. **thm:conditioned.** For every alpha < 1/4 there are constants
   0 < lambda_- <= lambda_+, depending only on alpha, with the following
   property. If limsup n/d^2 <= alpha, then with probability tending to 1
   some S fits every point, has trace d, and satisfies
   lambda_- I <= S <= lambda_+ I.
3. **cor:alternative.** Let E be the event that some real weights y_i with
   sum y_i = 0 make sum y_i x_i x_i^T positive definite. If
   limsup n/d^2 < 1/4, then P(E) tends to 0. If liminf n/d^2 > 1/4, then
   P(E) tends to 1.

Each result also states that the events it measures are measurable.

`extension/` goes beyond Gaussian points (see below). Its main result is
the optimal condition-number theorem, proved at fourth moment 3 in phase 8
and at every fourth moment kappa > 1 in phase 11: for i.i.d. points whose
law is a finite or countable mixture of product laws with fourth moment
kappa, an exact fit of condition number at most C exists with probability
tending to one below a threshold alpha(C, kappa) of n/d^2 and to zero
above it, for every C > 1, and the optimal condition number of the sample
converges to the inverse C_star(alpha, kappa) of C -> alpha(C, kappa). It
rests on Theorem 1.2 of Koehler
and Sohn, which extends the first result to points with independent
subgaussian coordinates (phase 5), and on its extension to finite mixtures
of product laws (phase 6), which phase 8 extends to countable mixtures.
Exact fitting is also proved for two dependent laws, the paired law and
the latent-sign law (phases 6 and 7), and phase 8 proves identities that
show the persistent dependence of the latent-sign law. Phase 9 adds four
complements: robustness in total variation, the failure of the
tensorization of the variance for the latent-sign law, a continuous
latent mixture that no countable mixture of product laws approximates,
and the endpoint expansions of the condition-number curve. Phase 10 makes
the optimal condition-number theorem robust to perturbations of order
o(d^-2) in total variation, and bounds the tensorization constant of the
latent-sign law by an explicit exponential. Phase 11 extends the optimal
condition-number theorem, with its robust form, to every fourth moment
kappa > 1.

`applications/` (phase 12) formalizes, over an arbitrary `R : realType`,
seven theorems of manuscripts of the OpenAI math collection whose proofs
reuse the library (see below).

## Status

- **Proved.** The kernel accepts `ellipsoid_fitting_main : main_statement`
  (`theories/MainTheorem.v`). `make check` builds the proof, compares
  the axioms of this theorem with `check/assumptions.expected`, and checks
  that the statement and its definitions are unchanged.
- **Reviewed.** On 5 October 2026 Marc Lelarge compared the formal
  statement and its definitions with the paper and found no problem. The
  kernel checks that the statement is proved; this review is the check that
  it says what the paper says.
- **Axioms.** The theorem uses eight classical axioms and nothing else:
  excluded middle (`Classical_Prop.classic`), propositional extensionality
  and dependent functional extensionality (`boolp`, and Stdlib's
  `FunctionalExtensionality`), constructive indefinite description
  (`boolp`), Hilbert's epsilon (`Epsilon.epsilon_statement`), and the two
  decision axioms behind Stdlib's real numbers
  (`ClassicalDedekindReals.sig_forall_dec` and `sig_not_dec`).
  `check/assumptions.expected` gives their exact types. Nothing from the
  paper is assumed.
- **The optimal condition number, proved.** The main result of the
  extension, from phase 8: `condition_theorem : condition_theorem_statement`
  (`extension/ConditionTheorem.v`). For i.i.d. points whose law is a finite
  or countable mixture of product laws, with coordinates of mean 0,
  variance 1 and subgaussian norm at most K in every component and
  unconditional fourth moment 3, and n/d^2 -> alpha > 0: for every C > 1,
  the probability that the sample has an exact fit of condition number at
  most C tends to 1 if alpha < alpha_C and to 0 if alpha > alpha_C, with
  alpha_C given by the semicircle law; and for 0 < alpha < 1/4, the
  optimal condition number of an exact fit tends in probability to
  C_star(alpha), the inverse of C -> alpha_C. The class contains dependent
  laws, the number of components may grow with d, and C_star is the
  optimum for the data, not only a bound.
- **At every fourth moment, proved.** Phase 11 extends this theorem to
  every fourth moment kappa > 1:
  `condition_kappa_theorem : condition_kappa_theorem_statement`
  (`extension/ConditionKappaTheorem.v`), for the same mixtures with
  unconditional fourth moment kappa in place of 3. With m and v the first
  and second upper moments of the semicircle law on [-sqrt 2, sqrt 2] and
  J(w) = v(w) + w m(w), the threshold is the curve
  alpha(C, kappa) = J(ell) - J(u), where -sqrt 2 < ell < u < sqrt 2 are
  the two clipping points of the optimal profile of a variational problem
  over the semicircle law. For every C > 1, the probability of an exact
  fit of condition number at most C tends to 1 if alpha < alpha(C, kappa)
  and to 0 if alpha > alpha(C, kappa) (the threshold (20)); for
  0 < alpha < alpha*(kappa), the optimal condition number tends in
  probability to C_star(alpha, kappa), the inverse of C -> alpha(C, kappa)
  (the limit (21)). Both hold for finite and countable mixtures.
  `condition_kappa_curve_theorem : condition_kappa_curve_statement`
  (`extension/ConditionKappaCurveTheorem.v`) proves the properties of the
  curve: u is the only zero in [0, sqrt 2] of an explicit function F,
  alpha(C, kappa) is the value of the variational problem and 1/(3 pi)
  times the integral of (2 - z^2)^(3/2) over [ell, u], and
  C -> alpha(C, kappa) is continuous and strictly increasing on (1, oo),
  from 0 to alpha*(kappa), with the inverse C_star(alpha, kappa).
  `condition_kappa_robust_theorem : condition_kappa_robust_theorem_statement`
  (`extension/ConditionKappaRobustTheorem.v`) proves (20) and (21) for
  i.i.d. points of arbitrary laws within o(d^-2) in total variation of a
  finite or countable family of fourth moment kappa. At kappa = 3 the
  curve and its inverse are alpha_C and C_star(alpha), and the statements
  of phase 11 imply those of phases 8 and 10.
- **Seven theorems of the OpenAI math collection (phase 12), proved.**
  `applications/` proves, over an arbitrary `R : realType` and from the
  library, the frozen statements of seven targets, which the user accepted
  at commits `fc76edf` and `0d5afba`: `matrix_series_theorem` (T1, the
  moment bound E tr (sum_j g_j H_j)^(2q) <= (2q - 1)!! opnorm(S)^(q-1) tr S
  of a Gaussian matrix series and its rectangular corollary),
  `tensor_packing_theorem` (T2, tensor packing in finite dimensions, with
  C = 30000), `goe_edge_theorem` (T3, E lambda_max(W) <= 2 for the GOE,
  with the tails exp (- d t^2 / 4)), `sk_gap_theorem` (T4, the spectral gap
  (1 - 2 beta)/2 of the heat-bath dynamics of the Sherrington-Kirkpatrick
  model for beta < 1/2, on measurable good-disorder events of probability
  tending to one, uniformly in the scale s in [0, 1] and in the field, with
  the covariance bound), `psd_splitting_theorem` (T5, the orthogonal
  splitting of positive semidefinite matrices), `perceptron_sign_theorem`
  (T6, the sign/Gaussian comparison |E_sign p_N - E_Gauss p_N| <= C M
  N^(-3/2) for the pressure of the Ising perceptron) and
  `sat_variance_theorem` (T7, Var(V_n) = O_k(n^(1 + 2/k)) for the capped
  satisfiable prefix of random k-SAT). Each uses only the three axioms of
  `boolp` (`check/MatrixSeriesAssumptions.v` to
  `check/SatVarianceAssumptions.v`). Each file is a Rocq formalization of
  a credited argument; `applications/README.md` lists the manuscripts and
  the main results.
- **Countable mixtures.** `countable_theorem : countable_theorem_statement`
  (`extension/CountableTheorem.v`) is a generality result: the conclusions
  of the finite-mixture theorem below, with its constants, for mixtures
  with countably many components.
- **Persistent dependence.** `latent_scope_theorem : latent_scope_statement`
  (`extension/LatentScopeTheorem.v`) proves identities for one point of the
  latent-sign law (below): its coordinates have the uniform law, the
  features h(x_j) of two coordinates have covariance s^2 / 81 in every
  dimension, and (|x_1| + ... + |x_d|) / sqrt d has variance
  1/4 + (d - 1) s^2 / 768. The theorem asserts these identities only.
  Their consequence, since this function is convex and 1-Lipschitz: for a
  fixed s > 0, these laws do not satisfy dimension-free Gaussian
  concentration for convex 1-Lipschitz functions, although exact fitting
  holds for them.
- **The statements of phase 8.** `CountableMixtureDefinitions.v`,
  `CountableMixtureStatement.v`, `ConditionDefinitions.v`,
  `ConditionStatement.v` and `LatentSignScope.v` (in `extension/`) were
  accepted by the user and are frozen at commit `5442e84`. The three
  theorems use the same seven axioms as the theorems below
  (`check/CountableAssumptions.v`, `check/ConditionAssumptions.v`,
  `check/LatentScopeAssumptions.v`). `extension/README.md`, section (g),
  describes them. The ordinary arguments of the notes are now formalized;
  their novelty is not confirmed.
- **The complements of phase 9.** Four theorems, on statements that the
  user accepted and that are frozen at commit `1c05ffc`
  (`RobustDefinitions.v`, `RobustStatement.v`, `LatentTensorization.v`,
  `ContinuousLatent.v`, `ConditionEndpoints.v`, in `extension/`):
  `robust_theorem` (`extension/RobustTheorem.v`): the conclusions of the
  countable-mixture theorem hold for i.i.d. points of arbitrary laws within
  o(d^-2) in total variation of an admissible family, and the
  contamination by a point at 0 with probability lambda / n, at total
  variation distance at most lambda / n, shows that o(d^-2) cannot be
  relaxed to O(d^-2) in general; `latent_tensor_theorem`
  (`extension/LatentTensorTheorem.v`): every constant of the coordinate
  tensorization of the variance for the latent-sign law is at least
  1 + (d - 1) s^2 / 9, and for a fixed s > 0 it grows exponentially in d;
  `continuous_latent_theorem` (`extension/ContinuousLatentTheorem.v`): a
  mixture over a continuous parameter of product laws whose components
  satisfy (M2) and (M3) is at total variation distance one from every
  countable mixture of product laws in dimension d >= 2;
  `condition_endpoints_theorem` (`extension/ConditionEndpointsTheorem.v`):
  the expansions of alpha_C near C = 1 and as C -> oo, and of C_star near
  alpha = 0 and alpha = 1/4. The four theorems use the same seven axioms
  as the theorems above (`check/RobustAssumptions.v`,
  `check/LatentTensorAssumptions.v`, `check/ContinuousLatentAssumptions.v`,
  `check/ConditionEndpointsAssumptions.v`). `extension/README.md`, section
  (h), describes them; as for phase 8, the arguments are ordinary and their
  novelty is not confirmed.
- **The complements of phase 10.** Two theorems, on statements that the
  user accepted and that are frozen at commit `b26eb1e`
  (`ConditionRobustStatement.v`, `LatentTensorUpper.v`):
  `robust_condition_theorem` (`extension/ConditionRobustTheorem.v`): the
  threshold alpha_C and the limit C_star(alpha) of the optimal
  condition-number theorem hold for i.i.d. points of arbitrary laws within
  o(d^-2) in total variation of a countable family of fourth moment 3;
  `latent_tensor_upper_theorem` (`extension/LatentTensorUpperTheorem.v`):
  the latent-sign law satisfies the coordinate tensorization of the
  variance with the constant 2 ((1 + s) / (1 - 3 s / 7))^d, so that, with
  the lower bounds of phase 9, the best constant lies between two
  exponentials in d for every fixed s > 0. Both use the same seven axioms
  as the theorems above (`check/ConditionRobustAssumptions.v`,
  `check/LatentTensorUpperAssumptions.v`). Phase 10 also proves reusable
  identities (the law of a sample of a countable mixture, a probability
  for the continuous latent law) and corrects the documentation of phase 9.
  `extension/README.md`, section (i), describes them.
- **The statements of phase 11.** `ConditionKappaDefinitions.v`,
  `ConditionKappaCurveStatement.v`, `ConditionKappaStatement.v` and
  `ConditionKappaRobustStatement.v` (in `extension/`) were accepted by the
  user and are frozen at commit `c5f41c4`. The three theorems use the same
  seven axioms as the theorems above
  (`check/ConditionKappaCurveAssumptions.v`,
  `check/ConditionKappaAssumptions.v`,
  `check/ConditionKappaRobustAssumptions.v`). `extension/README.md`,
  section (j), describes them. The ordinary arguments of the math plan are
  now formalized; their novelty is not confirmed.
- **The universality theorem, proved.** `extension/` states Theorem 1.2 of
  Koehler and Sohn, *Universality and sharp thresholds for ellipsoid
  fitting* ([arXiv:2608.27372v1](https://arxiv.org/abs/2608.27372v1)): for
  points with independent coordinates of mean 0, variance 1, fourth moment
  kappa > 1 and subgaussian norm at most K, the same phase transition at a
  threshold alpha*(kappa), a well-conditioned positive definite fit below
  it, and above it the limit e*(alpha, kappa) > 0 of the optimal squared
  fitting error. The kernel accepts
  `universality_theorem : universality_statement`
  (`extension/UniversalityTheorem.v`). The statement
  (`extension/UniversalityStatement.v`) and its definitions
  (`extension/UniversalityDefinitions.v`) were reviewed against the paper
  and accepted before any proof, and are frozen: `make check` checks that
  their code is unchanged since commit `3c6afa1`, which added them to
  `main`. `make check` checks that the axioms of the theorem are among
  the eight classical axioms of the first theorem
  (`check/universality_assumptions.expected`): it uses seven of them, all
  but excluded middle (`Classical_Prop.classic`).
- **Its proof.** Phase 5 of `AGENTS.md` is its plan,
  and `extension/README.md` the feasibility study behind it. It follows
  the paper. Above the threshold (`extension/Unsat/`), the least squares
  value of the quadratic features of the points concentrates around its
  value for Gaussian data, by the Lindeberg argument with a barrier (the
  paper's Theorem 2.9 and Corollary 2.13, with its Lemma 2.12 to remove
  the ridge); the Gaussian model (`extension/Gaussian/`, Proposition 1.4)
  computes that value by the convex Gaussian min-max theorem and Wigner's
  semicircle law. Below the threshold (`extension/Sat/`), the same
  Lindeberg argument and the Gaussian fit of Lemma 5.17 give an
  approximate fit (Proposition 2.1), and the small-residual interpolation
  (Theorem 1.9, from Theorem 2.3 and Propositions 3.1, 3.3 and 3.4)
  corrects it into an exact, well-conditioned fit. The general tools are
  in `library/`.
- **Finite mixtures of product laws, proved.** The main
  result of phase 6 extends Theorem 1.2 to i.i.d. points whose law is, at
  each dimension d, a finite mixture of product laws, with a number of
  components that may grow with d, under three assumptions (M1)-(M3):
  in every component the coordinates are independent, of mean 0, variance
  1 and subgaussian norm at most K, and every coordinate has the same
  unconditional fourth moment kappa > 1 under the mixture. Both phases
  hold, with the threshold alpha*(kappa) and the error e*(alpha, kappa) of
  Theorem 1.2, and so does the small-residual interpolation (Theorem 1.9).
  The kernel accepts `mixture_theorem : mixture_theorem_statement`
  (`extension/MixtureTheorem.v`). No matching theorem was found in a
  targeted literature search; priority is not confirmed. The theorem
  contains the universality theorem: with one component, its statement implies
  `universality_statement` (`extension/Mixture/OneComponent.v`).
- **Exact fitting for two dependent laws.** `paired_theorem : paired_statement`
  (`extension/PairedTheorem.v`): exact fitting for the paired law, whose
  coordinates come in dependent pairs with density
  (1 + eps h(x) h(y)) / 12 on [-sqrt 3, sqrt 3]^2, h the rescaled Legendre
  polynomial P_4, over the whole range -1 <= eps <= 7/3, with constants
  uniform in eps (the threshold is alpha*(9/5)). Phase 7 adds
  `latent_sign_theorem : latent_sign_statement`
  (`extension/LatentSignTheorem.v`): exact fitting for the latent-sign law
  (1/2) lambda_s^(x)d + (1/2) lambda_-s^(x)d, lambda_a = (1 + a h) mu, in
  which one hidden sign couples all the coordinates of a point, for every
  s in [0, 1], possibly depending on d, with constants uniform in s (the
  threshold is again alpha*(9/5)).
- **The statements of phases 6 and 7.** `extension/MixtureDefinitions.v`,
  `MixtureStatement.v`, `PairedDefinitions.v` and `PairedStatement.v`, and
  then `LatentSignDefinitions.v` and `LatentSignStatement.v`, were
  accepted by the user and are frozen: `make check` checks that their code
  is unchanged since commits `eef4694` and `d4de51d`. The three theorems
  use the same seven axioms as the universality theorem
  (`check/MixtureAssumptions.v`, `check/PairedAssumptions.v`,
  `check/LatentSignAssumptions.v`). `extension/README.md`, section (f),
  describes the definitions, the statements and the proofs.
## What to read

The proof is checked by the kernel, so only the statement needs to be read.
It consists of:

- `theories/MainStatement.v`: the statement, with a comment that reads it.
- `theories/PaperMainDefinitions.v`: the definitions it uses (quadratic
  forms, positive semidefinite matrices, the three events, the probability,
  the limsup and liminf conditions).
- `theories/GaussianProbabilityProductDefinitions.v`, and the modules it
  imports (`GaussianProbabilityDefinitions.v`, `GaussianDefinitions.v`,
  `AnalysisIntegralDefinitions.v`): the law of n*d independent standard
  normal coordinates.

The reals are Stdlib's `R`, used through MathComp's structures. Vectors and
matrices are MathComp's.

The statement of the universality theorem is
`extension/UniversalityStatement.v`, with a comment that reads it, and
`extension/UniversalityTheorem.v` proves it. Its
definitions, in `extension/UniversalityDefinitions.v`, reuse those of
`theories/PaperMainDefinitions.v` that do not depend on the law of the
points, and take the law of independent coordinates from the library
(`tuple_prod`, `library/probability/lindeberg.v`).

The statement of the finite-mixture theorem is
`extension/MixtureStatement.v`, over the definitions of
`extension/MixtureDefinitions.v` (the assumptions (M1)-(M3), the
probability of a mixture sample as an average over the labels of the
points, the interpolation property); those of its corollaries are
`extension/PairedStatement.v` and `extension/LatentSignStatement.v`, over
`extension/PairedDefinitions.v` and `extension/LatentSignDefinitions.v`.
Each has a comment that reads it.

## Building

Tested with:

| Package | Version |
|---|---|
| OCaml | 5.3.0 |
| Rocq (`rocq-core`) | 9.1.1 |
| Rocq Stdlib (`rocq-stdlib`) | 9.0.0 |
| Hierarchy Builder | 1.10.3 |
| MathComp | 2.6.0 |
| MathComp finmap | 2.2.4 |
| MathComp-Analysis, with `reals-stdlib` and `analysis-stdlib` | 1.16.0 |

To install them in a new opam switch:

```sh
opam switch create ellipsoid-fitting ocaml-base-compiler.5.3.0
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add coq-released https://coq.inria.fr/opam/released
opam install --deps-only ./rocq-ellipsoid-fitting.opam
```

Then, from the repository root:

```sh
make check ROCQ_SWITCH=ellipsoid-fitting JOBS=8   # the switch created above
make check ROCQ_SWITCH= JOBS=8                    # the rocq on your PATH
```

On 5 October 2026 a full build took 13 minutes with `JOBS=12` on a 16-core
Mac (104 minutes of processor time). Compiling prints eleven warnings, all
at the two `HB.instance` commands of the frozen module
`theories/GaussianProbabilityProductDefinitions.v` (ten
`redundant-canonical-projection` and one `HB: no new instance is
generated`), whose code cannot change. The other modules print none.

## Layout

- `theories/`: 588 modules under the logical root `EllipsoidFitting`. The
  statement (`MainStatement.v`), the theorem (`MainTheorem.v`), the five
  definition modules of the statement, the top of the proof
  (`PaperMainResults.v`, `PaperMainFinalAssembly.v`,
  `PaperMainConditionedLimit.v`) and `Asymptotics.v` are at the top; the
  others are in 33 folders by topic (`Gaussian`, `Gordon`, `Matrix`, `Head`,
  ...), and `theories/A/B.v` is the module `EllipsoidFitting.A.B`. The
  14 subfolders of `Gaussian/` divide its modules further:
  `theories/Gaussian/C/D.v` is the module `EllipsoidFitting.Gaussian.C.D`.
- `extension/`: the universality theorem, the finite-mixture theorem and
  its corollaries, under the logical root `EllipsoidUniversality` and at
  Stdlib's `R` like `theories/`. At the top: the statements and their
  definitions, and the theorems `UniversalityTheorem.v`
  (`universality_theorem`), `MixtureTheorem.v` (`mixture_theorem`),
  `PairedTheorem.v` (`paired_theorem`), `LatentSignTheorem.v`
  (`latent_sign_theorem`), `CountableTheorem.v` (`countable_theorem`),
  `ConditionTheorem.v` (`condition_theorem`), `LatentScopeTheorem.v`
  (`latent_scope_theorem`), and those of phase 9: `RobustTheorem.v`
  (`robust_theorem`), `LatentTensorTheorem.v` (`latent_tensor_theorem`),
  `ContinuousLatentTheorem.v` (`continuous_latent_theorem`) and
  `ConditionEndpointsTheorem.v` (`condition_endpoints_theorem`), and
  those of phase 10: `ConditionRobustTheorem.v`
  (`robust_condition_theorem`) and `LatentTensorUpperTheorem.v`
  (`latent_tensor_upper_theorem`), and those of phase 11:
  `ConditionKappaCurveTheorem.v` (`condition_kappa_curve_theorem`),
  `ConditionKappaTheorem.v` (`condition_kappa_theorem`) and
  `ConditionKappaRobustTheorem.v` (`condition_kappa_robust_theorem`). The
  folders of the proofs:
  `Model/` (the law of the sample and the measurability of the events),
  `Features/` (the quadratic features of the points, and those of a
  mixture), `Unsat/` (the unsatisfiable phase), `Gaussian/` (the Gaussian
  model), `Sat/` (the satisfiable phase), `Mixture/` (component laws,
  samples whose coordinate laws vary with the point, the interpolation and
  the assembly for mixtures), `Paired/` (the uniform law, the paired
  law and the latent-sign law as mixtures, the scope of the latter and its
  conditional laws), `Countable/` (the truncation of a countable mixture,
  the transfer of the theorem, robustness in total variation and the
  continuous latent mixture), `Condition/` (the condition-number
  theorem, the endpoints of its curve and its robustness) and
  `ConditionKappa/` (the condition-number theorem at every fourth moment
  kappa > 1: the curve, the Gaussian limit, the Gaussian witness and gap,
  the two halves of the threshold, and the countable and robust versions).
  `extension/README.md` holds the feasibility study of phase 5 and, in its
  sections (f) to (j), the description of phases 6 to 11.
- `library/`: the library `GaussianAnalysis`, 96 files of general results
  over an arbitrary `R : realType`: Gaussian measures, Gaussian comparison
  and concentration, real matrices and probability; the Fourier analysis
  of anti-concentration (characteristic functions written without complex
  numbers, Levy concentration functions and Esseen's inequality, the
  Brascamp-Lieb inequality, the vector small-ball estimate of Koehler and
  Sohn, the Fourier inversion theorem); and the tools of the universality
  theorem: self-concordant barriers, least squares with a barrier and the
  Lindeberg method for it, Moreau's decomposition and the convex Gaussian
  min-max theorem, subgaussian and subexponential variables (Hoeffding,
  Bernstein, Hanson-Wright), the Efron-Stein inequality, the GOE and
  Wigner's semicircle law, restricted isometry, nuclear norms and
  coverings; the tools of phase 6: laws given by a density, finite
  mixtures of probabilities, and the regularity of a mixture of feature
  laws; and those of phase 8: countable mixtures of probabilities and
  sums over label tuples, the cone of symmetric matrices of bounded
  condition number (its distance by Hoffman-Wielandt and its support
  function by Moreau), the clip energy of a symmetric law, the uniform
  semicircle law for families of linear statistics of the GOE, and the
  convex Gaussian min-max theorem on cones; and those of phase 9: the total
  variation distance and its bound for products, and the atoms of a finite
  measure; and those of phase 11: the maximizer of a trace-penalized
  quadratic on a closed convex set of matrices, and the problem over
  clipped profiles of a symmetric law, with its dual form. The proofs use
  the library at Stdlib's `R`: in
  `theories/`, `Gaussian/Law/LibraryBridge` identifies the library's
  Gaussian measure with the product law of the statement,
  `Analysis/RealsBridge` rewrites Stdlib's real functions into MathComp's,
  and 23 other modules of `theories/` require library files directly, as
  do the modules of `extension/`.
  `library/README.md` gives its conventions, its main results and their
  users. Phase 5 added the directories `convex/` and `random_matrix/`,
  phase 13 `analysis/` (real sequences) and `combinatorics/` (finite
  combinatorics with no field).
- `applications/`: Rocq formalizations of theorems of manuscripts of the
  OpenAI math collection (`openai/math` at revision 1581d4cbd) whose proofs
  reuse the library, under the logical root `GaussianApplications` and over
  an arbitrary `R : realType` like `library/` (phases 12 and 13). Each
  file cites the manuscript, the lemma it formalizes and the Lean module of
  the collection whose argument it follows, if any. The statement files are
  at the top, the proofs in folders by target (`SKGap/`, `Perceptron/`,
  `RandomSAT/`, and `PsdRank/` for the PSD rank theorem of phase 14).
  `applications/README.md` gives its rules, its targets and its main
  results.
- `check/Assumptions.v`: prints the axioms of the main theorem.
  `check/assumptions.expected` is the expected output.
  `check/UniversalityAssumptions.v` checks that `universality_theorem`
  proves the frozen statement and prints its axioms;
  `check/universality_assumptions.expected` is the expected output.
  `check/MixtureAssumptions.v`, `check/PairedAssumptions.v` and
  `check/LatentSignAssumptions.v` do the same for `mixture_theorem`,
  `paired_theorem` and `latent_sign_theorem`, with the expected lists
  `check/mixture_assumptions.expected`, `check/paired_assumptions.expected`
  and `check/latent_sign_assumptions.expected`; and
  `check/CountableAssumptions.v`, `check/ConditionAssumptions.v` and
  `check/LatentScopeAssumptions.v` for the three theorems of phase 8, with
  `check/countable_assumptions.expected`,
  `check/condition_assumptions.expected` and
  `check/latent_scope_assumptions.expected`; and
  `check/RobustAssumptions.v`, `check/LatentTensorAssumptions.v`,
  `check/ContinuousLatentAssumptions.v` and
  `check/ConditionEndpointsAssumptions.v` for the four theorems of phase 9,
  `check/ConditionRobustAssumptions.v` and
  `check/LatentTensorUpperAssumptions.v` for the two theorems of phase 10,
  and `check/ConditionKappaCurveAssumptions.v`,
  `check/ConditionKappaAssumptions.v` and
  `check/ConditionKappaRobustAssumptions.v` for the three theorems of
  phase 11, and `check/MatrixSeriesAssumptions.v`,
  `check/TensorPackingAssumptions.v`, `check/GoeEdgeAssumptions.v`,
  `check/SKGapAssumptions.v`, `check/PsdSplittingAssumptions.v`,
  `check/PerceptronSignAssumptions.v` and `check/SatVarianceAssumptions.v`
  for the seven theorems of `applications/` (phase 12), with the expected
  lists of the same names (`check/matrix_series_assumptions.expected` and
  so on).
  `check/ApplicationsDefinitions.v` states a characterization of each
  library definition that the frozen statements of `applications/` unfold
  to (`mxdot`, `frobenius`, `opnorm`, `psdmx`, `goe_mx`, the measurable
  structure of matrices, and `gauss` through its values on boxes, which
  determine it); `make check` compiles it.
  `check/Phase13Definitions.v` does the same for phase 13: it states a
  characterization of each project definition that the frozen statements
  of phase 13 and its accepted general statements unfold to, written out
  down to the definitions of MathComp and proved by computation, so that a
  definition that no longer computes to that text fails. Each freeze
  extends it; freeze 1 covers `unif_mean`, `unif_var`, `binomial_mean`,
  `linear_op`, `monotone_op` and `meet_avg`. `make check` compiles it into
  `build/phase13_definitions.txt`, a required output.
- `scripts/check_sources.py`: checks that the statement, the theorem and the
  five definition modules of the statement have the same code as at the
  commit in `check/frozen-baseline`, the statement of the universality
  theorem and its definitions the same code as at commit `3c6afa1`, the
  four statement files of phase 6 the same code as at commit `eef4694`,
  the two of phase 7 the same code as at commit `d4de51d`, the five
  of phase 8 the same code as at commit `5442e84`, the five of phase 9
  the same code as at commit `1c05ffc`, the two of phase 10 the same
  code as at commit `b26eb1e`, the four of phase 11 the same code as
  at commit `c5f41c4`, the three accepted statement files of
  `applications/` of batch 1 of phase 12 the same code as at commit
  `fc76edf`, as the section `lambda_max` of
  `library/matrix/lambda_max.v` with its Require commands, and the seven
  statement and definitions files of batch 2 the same code as at commit
  `0d5afba`, and the three statement files of batch 1 of phase 13 the same
  code as at commit `46e45c8`, at which the user accepted the statements of
  phase 13 (comments may differ); that `check/ApplicationsDefinitions.v`
  has its fixed code, and `check/Phase13Definitions.v` the code of its
  last freeze, the code of each earlier freeze being a prefix of it; that
  each entry of the acceptance inventory, the general statements of the
  library accepted in phase 13 with their full propositions as `Print`
  shows them at the acceptance commit, names a definition of its file at
  that commit; that the
  axiom-check files of phases 5 and 6 and their expected lists are
  byte-identical to commit `c3e555e`, those of phases 7 and 8 to commit
  `a89ed1e`, those of phase 9 to commit `e4c46e1`, those of phase 10 to
  commit `eda8a06`, those of phase 11 to commit `d29b278`, and those of
  phase 12 to commit `495929a` (commit P); that the
  Require
  commands of
  `library/probability/lindeberg.v` and its section `tuple_prod`, on which
  the frozen statements depend, have the same code as at commit `c3e555e`;
  that no module of `theories/`,
  `library/`, `extension/` or `applications/` contains `Admitted`, `Axiom`,
  `Parameter` or `Conjecture`; that no module of `library/` or
  `applications/` requires a module of `theories/` or `extension/`,
  Stdlib's reals, or MathComp's bridge to them (`Rstruct`,
  `Rstruct_topology`), and no module of `library/` a module of
  `applications/`; and that it is given exactly the report of each theorem
  of its table (24), by path and in order, every report exists and is
  complete, and the axioms of each theorem are among its expected ones,
  each expected list being part of the first. `make check` deletes the
  reports before it regenerates them, then runs it.
- `scripts/export_from_ellipsoid_rocq.py`: the script that copied the proof
  (see below).
- `scripts/unused.py`: lists the declarations of `theories/` that the main
  theorem does not use, from the `.glob` files of a build, and can delete
  them. Its docstring says how it decides. On the current tree it lists
  nothing.
- `scripts/stale_citations.py`: lists the names that the comments of
  `theories/`, `library/`, `extension/` and `applications/` cite but that
  no declaration defines, from the `.glob` files of a build and of the
  installed libraries. The rest of a comment line after the marker `Lean:`
  is not checked: it cites the Lean sources of the collection. `make
  citations` runs it, and `make check` fails on a stale citation
  (`CITATIONS=no` skips it).

## Where the proof comes from

The proof was developed in
[LLM4Rocq/ellipsoid_rocq](https://github.com/LLM4Rocq/ellipsoid_rocq), in its
directory `analysis/`, and completed on 2 October 2026 (commit `212a249`).
Commit `29df54e` of this repository copies it from commit `9556cdd` of that
repository.

- The 647 modules copied are the dependency closure of `PaperMainResults`
  (the proof) and `PaperMainDefinitions` (the definitions of the statement).
  The only change is the logical root, `Tablet` replaced by
  `EllipsoidFitting`. The export script reproduces commit `29df54e`, not the
  current tree. To verify that commit against a checkout of the source
  repository, run in a checkout of commit `29df54e` of this repository:

  ```sh
  python3 scripts/export_from_ellipsoid_rocq.py ../ellipsoid_rocq 9556cdd --check
  ```

- Since then, what the main theorem does not use has been deleted twice:
  17 modules and 714 declarations of the other modules at the tag
  `phase1`, then 23 modules and 212 declarations of the other modules once
  the proof used the library. `scripts/unused.py` finds them from the
  `.glob` files of a build, and the proof builds without them. Some
  special-purpose proofs were replaced by results of the library, and the
  modules were renamed and grouped in folders.
  Deleted code stays in the history: a general result can be recovered
  from commit `29df54e`, where the modules have their original names, for
  example with `git show 29df54e:theories/OperatorSpaces.v`.
- `MainStatement.v` is the statement of
  `analysis/challenges/paper_main_results/Challenge.v` in the source
  repository, copied verbatim, as a definition instead of an admitted
  theorem. It is also, verbatim, the statement of `paper_main_results` in
  `PaperMainResults.v`.
- `MainTheorem.v` and `check/` replace the source repository's policy module
  `PaperMainPolicy` and its checking scripts.
- Not copied: the 153 other modules of `analysis/`, the challenge files,
  reports and journals, and the older Coquelicot development in `theories/`.

## Planned work

Of the three steps of the plan of `AGENTS.md`, the first and the third are
done, and the second is done in part.

1. `library/` states and proves the general results that the proof needed,
   over an arbitrary `R : realType`, in the style of MathComp-Analysis and
   independently of the paper: the standard Gaussian measure on `'rV[R]_n`
   and its integration by parts, Gaussian interpolation and the comparison
   inequalities of Kahane, Slepian, Sudakov-Fernique and Gordon, escape
   through a mesh, Gaussian concentration and the Poincare inequality, the
   spectral theorem for real symmetric matrices, operator norms and nets,
   Paley-Zygmund and the Lindeberg replacement method.
2. The proof of the paper uses these results at Stdlib's `R` in its
   modules on the comparison inequalities, the spectral theorem, the
   operator norms, the nets, the Paley-Zygmund inequality and the Lindeberg
   method; in its modules on the Gaussian integral on the line, whose
   kernel is the density of the normal law of MathComp-Analysis up to a
   constant (`Gaussian/Line/Kernel`, `Gaussian/Line/Mass`,
   `Gaussian/Line/Moments`, `Gaussian/Line/Expectation`,
   `Gaussian/Line/PolynomialIntegrability`, `Gaussian/Line/QuadraticMGF`);
   and, through `Gaussian/Law/LibraryBridge`, in its modules on the
   iterated Gaussian expectation: the coordinate Stein identities, the
   exchange and the rotation of coordinates, the integrability at every
   level of a continuous function of polynomial growth and the continuity
   of its marginals (`Gaussian/Iterated/Stein`,
   `Gaussian/Iterated/BlockRotation`, `Gaussian/Iterated/PolynomialGrowth`).
   What it no longer needed is deleted: `theories/` had 632 modules and
   102,415 lines at the tag `phase1`, and has 588 modules and 86,410 lines
   now. The library had 37 files and 21,005 lines at the end of phase 4,
   72 files and 48,032 lines after phase 5, 75 files and 48,991 lines
   after phase 6, 78 files and 51,203 lines after phase 8, 80 files and
   51,666 lines after phase 9, 80 files and 51,796 lines after phase 10,
   82 files and 53,142 lines after phase 11, and has 94 files and 58,525
   lines after phase 12.
3. The comments no longer describe how the modules were produced, and the
   modules are renamed and grouped in folders.

What remains:

- No human has reviewed the statements of the library yet. The table of
  main results in `library/README.md` is the place to start; the most
  general results are candidates for MathComp-Analysis.
- About 195 modules of `theories/`, those on the Gaussian measure, real
  analysis and matrix norms, still prove general facts in the special form
  that the paper needs, with lists of coordinates and Stdlib's `R`,
  although the library now states them in general: the interpolation
  between two covariances (`Gaussian/Covariance/Definitions` and five
  more; the `Projection` modules use it to compare quadratic Gaussian
  features with their Gaussian replacement, which the library does not
  state in that form), matrix norms (`Matrix/OperatorNorm`,
  `Matrix/FrobeniusNorm` and six more), real analysis in one variable and
  for functions of lists (`Analysis/CoordinateTopology`,
  `Analysis/TaylorRemainder` and ten more), and the machinery of the
  paper's Gibbs laws, soft min-max and cumulants. The facts about the
  iterated expectation that carry no continuity hypothesis (its linearity,
  monotonicity and the identities between its levels) are proved from its
  recursive definition and have no counterpart in the library.

The statement keeps its meaning throughout: `make check` checks after each
step that its code and the code of its definitions are unchanged.

Phase 5 of `AGENTS.md` proved the universality theorem of `extension/`
in three stages: the unsatisfiable phase at fourth moment 3 (tag
`stage1`), then the Gaussian model and the unsatisfiable phase for every
fourth moment (tag `stage2`), then the satisfiable phase (tag `phase5`).
Its general results are in `library/`. Phase 6 proved the finite-mixture
theorem and its corollary for the paired law (tag `phase6`). Phase 7
proved the corollary for the latent-sign law, hardened the checks and
generalized two library results (tag `phase7`). Phase 8 proved the three
extensions of the mixture theorem: countable mixtures, the optimal
condition number at fourth moment 3, and the scope of the latent-sign law
(tag `phase8`). Phase 9 proved four complements of these extensions,
robustness in total variation, the tensorization bounds of the
latent-sign law, the continuous latent mixture and the endpoint expansions
of the condition-number curve, and the follow-ups of the review of the
phase 8 release (tag `phase9`). Phase 10 proved the robustness of the
optimal condition number and a finite tensorization constant, with
reusable identities and the corrections of the review of the phase 9
release (tag `phase10`). Phase 11 proved the optimal condition number
at every fourth moment kappa > 1, for finite and countable mixtures and
their perturbations in total variation, with the properties of its curve
(tag `phase11`). Phase 12 formalized in `applications/` seven theorems of
manuscripts of the OpenAI math collection whose proofs reuse the library,
with twelve new library files (tag `phase12`).
