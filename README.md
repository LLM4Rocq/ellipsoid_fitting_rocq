# Ellipsoid fitting in Rocq

This repository holds Rocq proofs, checked by the Rocq kernel, of theorems on
fitting an ellipsoid to n random points x_1, ..., x_n of R^d. The base is the
sharp threshold of Misiakiewicz and Wen for independent standard Gaussian
points, `ellipsoid_fitting_main` in `theories/MainTheorem.v`. The probability
that some positive semidefinite matrix S satisfies x_i^T S x_i = d for every i
tends to 1 if limsup n/d^2 < 1/4, and to 0 if liminf n/d^2 > 1/4. The main
result beyond Gaussian points is the optimal condition number,
`condition_kappa_theorem` in `extension/ConditionKappaTheorem.v`. Take i.i.d.
points whose law is a finite or countable mixture of product laws, with
coordinates of mean 0, variance 1 and subgaussian norm at most K in every
component and unconditional fourth moment kappa > 1. For every C > 1, an exact
fit of condition number at most C exists with probability tending to one if
n/d^2 tends to some alpha with 0 < alpha < alpha(C, kappa), and to zero if
alpha > alpha(C, kappa). For 0 < alpha < alpha*(kappa), the optimal condition
number of the sample tends in probability to C_star(alpha, kappa), the inverse
of C -> alpha(C, kappa). This theorem rests on Theorem 1.2 of Koehler and Sohn,
which extends the Gaussian threshold to independent subgaussian coordinates,
and on its extension to mixtures. The repository also holds proofs of thirteen
theorems from manuscripts of the OpenAI math collection, and the library
GaussianAnalysis on which these proofs build.

## What is proved

The statement files below, with the definitions they import, are what a reader
has to trust; each has a header comment that describes it. `make check` checks
that the code of each, comments aside, is unchanged since a commit that the
checker names, that each theorem has its statement as its type, and that its
axioms are among those of its expected list. Every list is a subset of
[check/assumptions.expected](check/assumptions.expected), the eight classical
axioms of the Gaussian theorem: nothing from the papers is assumed. The symbols
are defined in the header of each statement file, except for S1 to S7, whose
short headers leave them to their code and to the definitions they import.

| Result | Statement | Theorem | Axiom check |
|---|---|---|---|
| **Gaussian points.** Misiakiewicz and Wen ([arXiv:2608.10184v1](https://arxiv.org/abs/2608.10184v1)): the threshold 1/4 for a positive semidefinite fit (thm:main), well-conditioned fits of trace d below it (thm:conditioned) and the balanced positive definite alternative (cor:alternative) | [theories/MainStatement.v](theories/MainStatement.v) | `ellipsoid_fitting_main`, [MainTheorem.v](theories/MainTheorem.v) | [Assumptions.v](check/Assumptions.v) |
| **Beyond Gaussian points.** Koehler and Sohn ([arXiv:2608.27372v1](https://arxiv.org/abs/2608.27372v1)), Theorem 1.2: for independent coordinates of mean 0, variance 1, fourth moment kappa > 1 and subgaussian norm at most K, the threshold alpha*(kappa), well-conditioned fits below it and the limit e*(alpha, kappa) of the fitting error above it | [extension/UniversalityStatement.v](extension/UniversalityStatement.v) | `universality_theorem`, [UniversalityTheorem.v](extension/UniversalityTheorem.v) | [UniversalityAssumptions.v](check/UniversalityAssumptions.v) |
| The same conclusions for finite mixtures of product laws, with a number of components that may grow with d | [extension/MixtureStatement.v](extension/MixtureStatement.v) | `mixture_theorem`, [MixtureTheorem.v](extension/MixtureTheorem.v) | [MixtureAssumptions.v](check/MixtureAssumptions.v) |
| The same for countable mixtures of product laws | [extension/CountableMixtureStatement.v](extension/CountableMixtureStatement.v) | `countable_theorem`, [CountableTheorem.v](extension/CountableTheorem.v) | [CountableAssumptions.v](check/CountableAssumptions.v) |
| The same for laws within o(d^-2) in total variation of such a family; o(d^-2) cannot be relaxed to O(d^-2) in general | [extension/RobustStatement.v](extension/RobustStatement.v) | `robust_theorem`, [RobustTheorem.v](extension/RobustTheorem.v) | [RobustAssumptions.v](check/RobustAssumptions.v) |
| The optimal condition number at fourth moment kappa > 1: the threshold alpha(C, kappa) and the limit C_star(alpha, kappa), for finite and countable mixtures | [extension/ConditionKappaStatement.v](extension/ConditionKappaStatement.v) | `condition_kappa_theorem`, [ConditionKappaTheorem.v](extension/ConditionKappaTheorem.v) | [ConditionKappaAssumptions.v](check/ConditionKappaAssumptions.v) |
| The curve alpha(C, kappa): the value of a variational problem over the semicircle law, continuous and increasing from 0 to alpha*(kappa), with the inverse C_star(alpha, kappa) | [extension/ConditionKappaCurveStatement.v](extension/ConditionKappaCurveStatement.v) | `condition_kappa_curve_theorem`, [ConditionKappaCurveTheorem.v](extension/ConditionKappaCurveTheorem.v) | [ConditionKappaCurveAssumptions.v](check/ConditionKappaCurveAssumptions.v) |
| The same threshold and limit for laws within o(d^-2) in total variation of a finite or countable family of fourth moment kappa | [extension/ConditionKappaRobustStatement.v](extension/ConditionKappaRobustStatement.v) | `condition_kappa_robust_theorem`, [ConditionKappaRobustTheorem.v](extension/ConditionKappaRobustTheorem.v) | [ConditionKappaRobustAssumptions.v](check/ConditionKappaRobustAssumptions.v) |
| The case kappa = 3, where the curve alpha_C is given by the semicircle law | [extension/ConditionStatement.v](extension/ConditionStatement.v) | `condition_theorem`, [ConditionTheorem.v](extension/ConditionTheorem.v) | [ConditionAssumptions.v](check/ConditionAssumptions.v) |
| The robust form at kappa = 3 | [extension/ConditionRobustStatement.v](extension/ConditionRobustStatement.v) | `robust_condition_theorem`, [ConditionRobustTheorem.v](extension/ConditionRobustTheorem.v) | [ConditionRobustAssumptions.v](check/ConditionRobustAssumptions.v) |
| The expansions of alpha_C near C = 1 and as C -> oo, and of C_star near alpha = 0 and alpha = 1/4 | [extension/ConditionEndpoints.v](extension/ConditionEndpoints.v) | `condition_endpoints_theorem`, [ConditionEndpointsTheorem.v](extension/ConditionEndpointsTheorem.v) | [ConditionEndpointsAssumptions.v](check/ConditionEndpointsAssumptions.v) |
| Exact fitting for the paired law, whose coordinates come in dependent pairs, for -1 <= eps <= 7/3 | [extension/PairedStatement.v](extension/PairedStatement.v) | `paired_theorem`, [PairedTheorem.v](extension/PairedTheorem.v) | [PairedAssumptions.v](check/PairedAssumptions.v) |
| Exact fitting for the latent-sign law, in which one hidden sign couples all the coordinates of a point | [extension/LatentSignStatement.v](extension/LatentSignStatement.v) | `latent_sign_theorem`, [LatentSignTheorem.v](extension/LatentSignTheorem.v) | [LatentSignAssumptions.v](check/LatentSignAssumptions.v) |
| Identities showing that the dependence of the latent-sign law persists in every dimension | [extension/LatentSignScope.v](extension/LatentSignScope.v) | `latent_scope_theorem`, [LatentScopeTheorem.v](extension/LatentScopeTheorem.v) | [LatentScopeAssumptions.v](check/LatentScopeAssumptions.v) |
| Every constant of the coordinate tensorization of the variance for the latent-sign law is at least 1 + (d - 1) s^2 / 9 | [extension/LatentTensorization.v](extension/LatentTensorization.v) | `latent_tensor_theorem`, [LatentTensorTheorem.v](extension/LatentTensorTheorem.v) | [LatentTensorAssumptions.v](check/LatentTensorAssumptions.v) |
| The latent-sign law satisfies this tensorization with the constant 2 ((1 + s) / (1 - 3 s / 7))^d | [extension/LatentTensorUpper.v](extension/LatentTensorUpper.v) | `latent_tensor_upper_theorem`, [LatentTensorUpperTheorem.v](extension/LatentTensorUpperTheorem.v) | [LatentTensorUpperAssumptions.v](check/LatentTensorUpperAssumptions.v) |
| A continuous latent mixture at total variation distance one from every countable mixture of product laws, for d >= 2 | [extension/ContinuousLatent.v](extension/ContinuousLatent.v) | `continuous_latent_theorem`, [ContinuousLatentTheorem.v](extension/ContinuousLatentTheorem.v) | [ContinuousLatentAssumptions.v](check/ContinuousLatentAssumptions.v) |
| **Translated samples.** S1: for i.i.d. N(m_d, I_d) points with norm(m_d) = o(sqrt d), the threshold alpha_C and the limit C_star(alpha) of centered Gaussian points | [extension/ShiftedConditionStatement.v](extension/ShiftedConditionStatement.v) | `shifted_condition_theorem`, [Shifted/ConditionTheorem.v](extension/Shifted/ConditionTheorem.v) | [ShiftedConditionAssumptions.v](check/ShiftedConditionAssumptions.v) |
| S2: for arbitrary shifts m_d and n/d^2 -> alpha with 0 < alpha < 1/4, with probability tending to one, a positive definite fit and an optimal condition number between c (1 + norm(m_d) / sqrt d) and C (1 + norm(m_d) / sqrt d), where the constants c and C depend only on alpha; the lower bound holds at every alpha > 0, on one event for all shifts | [extension/ShiftedGaussianStatement.v](extension/ShiftedGaussianStatement.v) | `shifted_gaussian_theorem`, [Shifted/GaussianTheorem.v](extension/Shifted/GaussianTheorem.v) | [ShiftedGaussianAssumptions.v](check/ShiftedGaussianAssumptions.v) |
| S3: above 1/4, one event excludes every quadric with nonzero positive semidefinite quadratic part, whatever its linear and constant terms | [extension/ShiftedQuadricStatement.v](extension/ShiftedQuadricStatement.v) | `shifted_quadric_theorem`, [Shifted/QuadricTheorem.v](extension/Shifted/QuadricTheorem.v) | [ShiftedQuadricAssumptions.v](check/ShiftedQuadricAssumptions.v) |
| S4: for n/d^2 -> alpha with alpha > 0 and arbitrary shifts, the optimal fitting error of the translated sample, and its infimum over all translations, tend in probability to e*(alpha, 3) | [extension/ShiftedErrorStatement.v](extension/ShiftedErrorStatement.v) | `shifted_error_theorem`, [Shifted/ErrorTheorem.v](extension/Shifted/ErrorTheorem.v) | [ShiftedErrorAssumptions.v](check/ShiftedErrorAssumptions.v) |
| S5: the same exclusion of quadrics above alpha*(kappa) for mixtures of product laws whose point law is centrally symmetric | [extension/ShiftedMixtureUnsatStatement.v](extension/ShiftedMixtureUnsatStatement.v) | `shifted_mixture_unsat_theorem`, [Shifted/MixtureUnsatTheorem.v](extension/Shifted/MixtureUnsatTheorem.v) | [ShiftedMixtureUnsatAssumptions.v](check/ShiftedMixtureUnsatAssumptions.v) |
| S6: positive definite fits below alpha*(kappa) for mixtures of product laws with shifts supported on o(d) coordinates, with no symmetry assumption | [extension/ShiftedMixtureSatStatement.v](extension/ShiftedMixtureSatStatement.v) | `shifted_mixture_sat_theorem`, [Shifted/MixtureSatTheorem.v](extension/Shifted/MixtureSatTheorem.v) | [ShiftedMixtureSatAssumptions.v](check/ShiftedMixtureSatAssumptions.v) |
| S7: the mixtures of the translates by m_d and -m_d of a centrally symmetric law have the centered-fitting statistics of the translate by m_d | [extension/ShiftedSignStatement.v](extension/ShiftedSignStatement.v) | `shifted_sign_theorem`, [Shifted/SignTheorem.v](extension/Shifted/SignTheorem.v) | [ShiftedSignAssumptions.v](check/ShiftedSignAssumptions.v) |
| **Applications.** T1: for symmetric H_1, ..., H_r, S = sum_j H_j^2 and q >= 1, the moment bound E tr (sum_j g_j H_j)^(2q) <= (2q - 1)!! opnorm(S)^(q-1) tr S of a Gaussian matrix series | [applications/MatrixSeriesStatement.v](applications/MatrixSeriesStatement.v) | `matrix_series_theorem`, [MatrixSeriesTheorem.v](applications/MatrixSeriesTheorem.v) | [MatrixSeriesAssumptions.v](check/MatrixSeriesAssumptions.v) |
| T2: tensor packing in finite dimensions, with a universal constant C (30000 in the proof) | [applications/TensorPackingStatement.v](applications/TensorPackingStatement.v) | `tensor_packing_theorem`, [TensorPackingTheorem.v](applications/TensorPackingTheorem.v) | [TensorPackingAssumptions.v](check/TensorPackingAssumptions.v) |
| T3: E lambda_max(W) <= 2 for the GOE, with the tails exp(-d t^2 / 4) | [applications/GoeEdgeStatement.v](applications/GoeEdgeStatement.v) | `goe_edge_theorem`, [GoeEdgeTheorem.v](applications/GoeEdgeTheorem.v) | [GoeEdgeAssumptions.v](check/GoeEdgeAssumptions.v) |
| T4: for 0 <= beta < 1/2, a spectral gap of at least (1 - 2 beta)/2 for the heat-bath dynamics of the Sherrington-Kirkpatrick model, on measurable good-disorder events of probability tending to one | [applications/SKGapStatement.v](applications/SKGapStatement.v) | `sk_gap_theorem`, [SKGapTheorem.v](applications/SKGapTheorem.v) | [SKGapAssumptions.v](check/SKGapAssumptions.v) |
| T5: the orthogonal splitting of positive semidefinite matrices | [applications/PsdSplittingStatement.v](applications/PsdSplittingStatement.v) | `psd_splitting_theorem`, [PsdSplittingTheorem.v](applications/PsdSplittingTheorem.v) | [PsdSplittingAssumptions.v](check/PsdSplittingAssumptions.v) |
| T6: for potentials f of class C^3 with f, f', f'' and f''' bounded, the sign/Gaussian comparison of the pressure of the Ising perceptron, with error at most C M N^(-3/2) | [applications/PerceptronSignStatement.v](applications/PerceptronSignStatement.v) | `perceptron_sign_theorem`, [PerceptronSignTheorem.v](applications/PerceptronSignTheorem.v) | [PerceptronSignAssumptions.v](check/PerceptronSignAssumptions.v) |
| T7: for every k >= 3, Var(V_n) = O_k(n^(1 + 2/k)) for the capped satisfiable prefix of random k-SAT | [applications/SatVarianceStatement.v](applications/SatVarianceStatement.v) | `sat_variance_theorem`, [SatVarianceTheorem.v](applications/SatVarianceTheorem.v) | [SatVarianceAssumptions.v](check/SatVarianceAssumptions.v) |
| T9: for every k >= 3, a satisfiability threshold for random k-SAT | [applications/SatThresholdStatement.v](applications/SatThresholdStatement.v) | `sat_threshold_theorem`, [SatThresholdTheorem.v](applications/SatThresholdTheorem.v) | [SatThresholdAssumptions.v](check/SatThresholdAssumptions.v) |
| T10: the normalization of the factors of a PSD factorization | [applications/PsdNormalizationStatement.v](applications/PsdNormalizationStatement.v) | `psd_normalization_theorem`, [PsdNormalizationTheorem.v](applications/PsdNormalizationTheorem.v) | [PsdNormalizationAssumptions.v](check/PsdNormalizationAssumptions.v) |
| T11: the product smoothing of matrix squares, with shared witnesses | [applications/ProductSmoothingStatement.v](applications/ProductSmoothingStatement.v) | `product_smoothing_theorem`, [ProductSmoothingTheorem.v](applications/ProductSmoothingTheorem.v) | [ProductSmoothingAssumptions.v](check/ProductSmoothingAssumptions.v) |
| T12: a real sequence with approximate minimum inequalities for comparable sizes and an approximate neighbor step, u(s + 1) >= u(s) - A s^(-beta), has a finite-size lower bound, and converges if it is bounded | [applications/MinSuperadditiveStatement.v](applications/MinSuperadditiveStatement.v) | `min_superadditive_theorem`, [MinSuperadditiveTheorem.v](applications/MinSuperadditiveTheorem.v) | [MinSuperadditiveAssumptions.v](check/MinSuperadditiveAssumptions.v) |
| T13: for some K > 0 and every 0 < rho < 1, every PSD factorization of size r of the shifted matching matrix A_n(rho) has 2^n <= r^K for every even n large enough | [applications/PsdRankStatement.v](applications/PsdRankStatement.v) | `psd_rank_theorem`, [PsdRankTheorem.v](applications/PsdRankTheorem.v) | [PsdRankAssumptions.v](check/PsdRankAssumptions.v) |
| T14: the same bound for A_n(0), for the slack matrix T_n(0) and for exact semidefinite lifts of the perfect matching polytope | [applications/PsdLiftStatement.v](applications/PsdLiftStatement.v) | `psd_lift_theorem`, [PsdLiftTheorem.v](applications/PsdLiftTheorem.v) | [PsdLiftAssumptions.v](check/PsdLiftAssumptions.v) |

## How to read the proofs

- [theories/](theories/) (logical root `EllipsoidFitting`, 588 `.v` files): the
  Gaussian theorem, with its statement and definitions at the top.
- [extension/](extension/) (`EllipsoidUniversality`, 177 `.v` files): the
  results beyond Gaussian points; see its [README](extension/README.md).
- [applications/](applications/) (`GaussianApplications`, 57 `.v` files): T1 to
  T14 except T8, which was deferred; see its [README](applications/README.md).
- [library/](library/) (`GaussianAnalysis`, 128 `.v` files): general results
  over any `R : realType`; 75 of its statements were reviewed and accepted.
- [check/](check/): the axiom and identity checks of the 37 theorems and the
  regression tests of the checker, `scripts/check_sources.py`.

## Building and checking

Tested with OCaml 5.3.0, Rocq 9.1.1 (`rocq-core`), Rocq Stdlib 9.0.0, Hierarchy
Builder 1.10.3, MathComp 2.6.0, MathComp finmap 2.2.4 and MathComp-Analysis
1.16.0 (with `reals-stdlib` and `analysis-stdlib`). In a new opam switch:

```sh
opam switch create ellipsoid-fitting ocaml-base-compiler.5.3.0
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add coq-released https://coq.inria.fr/opam/released
opam install --deps-only ./rocq-ellipsoid-fitting.opam
make build ROCQ_SWITCH=ellipsoid-fitting JOBS=3
```

`ROCQ_SWITCH=` uses the `rocq` on your PATH; without it, the Makefile uses the
switch `rocq-analysis`. With 12 GiB of memory, use `JOBS=3`. The package has no
install step: the modules are used from the clone. Without Rocq, in a clone
with its full history, `python3 -I -B scripts/check_sources.py --before-build`
applies the checker's rules to the sources: no `Admitted` or `Axiom`, the
statement files unchanged, the pinned files intact.

A bare `make` runs `make check`, which applies these rules, builds, then
compiles the check files and compares their outputs with the expected ones. It
runs in the pinned Docker image `ellipsoid-rocq:2026-10-01` (image id
`sha256:d28a2af774271dc1c3592aa423b064ae134a16bc22220ff5faf897b7aa9468fb`),
which is not public. Elsewhere it is expected to fail: the checker requires
OCaml 5.3.0, findlib 1.9.8 and a rebuilt exporter plugin identical to the one
that wrote the references of `check/identity/`. It last passed on 25 October
2026, on commit `5893184e` (run `d8bb8f380183817de780a550701eabc6`); the later
commits change only documentation and metadata, whose content the checker does
not read. The GitHub workflow [build.yml](.github/workflows/build.yml) is
disabled: its public image has OCaml 4.14.2 and findlib 1.9.6, and its last
run, on 25 October 2026, stopped on a stack overflow during the build.

## Documents

- [The website](https://llm4rocq.github.io/ellipsoid-fitting-web/) (sources in
  `LLM4Rocq/ellipsoid-fitting-web`): the results, a guide to GaussianAnalysis
  with a dated phase 12 browser, how the proofs were made and PDFs of the notes.
- [doc/README.md](doc/README.md): an index of `doc/`.
- [doc/details.md](doc/details.md): the former long README, kept as a record,
  with the description of each check; its header names its out-of-date parts.
- [doc/history/agent-rules.md](doc/history/agent-rules.md): the rules given to
  the AI agents who worked on the repository, formerly `AGENTS.md`. The new
  [AGENTS.md](AGENTS.md) says how a change is checked and overrides them.
- [doc/shifted-gaussian.tex](doc/shifted-gaussian.tex), with
  [doc/statements.bib](doc/statements.bib): the note *Centered ellipsoid
  fitting for non-centered Gaussian data*, the informal proof of S1 to S7.

## Status, citing and license

AI agents, including Claude and Codex, contributed to the formalization, review
and documentation under the direction of Marc Lelarge (Inria), who maintains
this research artifact. Issue reports are welcome; responses may be delayed. The
MIT license ([LICENSE](LICENSE), [NOTICE](NOTICE)) covers the code and the
documents. Cite this work with [CITATION.cff](CITATION.cff). The tag `shifted`
(24 October 2026, commit `305747af`) is the mathematical release, `shifted-docs`
(27 October 2026) the documentation release, whose GitHub release has the PDF of
the note: git does not track PDFs. [CHANGELOG.md](CHANGELOG.md) lists the tags.