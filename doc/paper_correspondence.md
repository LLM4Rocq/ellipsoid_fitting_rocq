# Correspondence between the paper and the formal proof

This document compares the Rocq proof in `theories/` with the informal proof
of the paper, result by result. Correctness is not in question: the kernel
checks the proof, and the statement and its definitions were reviewed
against the paper. The document records where the formal proof follows the
paper's route and where it deviates, and how. It also lists which results
the paper cites without proof, which hypotheses the formal lemmas add, and
which arguments are specific to Gaussian data, for planning an extension of
the theorem.

## What was compared

- **Paper.** T. Misiakiewicz and G. G. Wen, *The sharp SAT/UNSAT phase
  transition in random ellipsoid fitting*, arXiv:2608.10184v1. The LaTeX
  source (`manuscript.tex`, 2368 lines) was downloaded from
  https://arxiv.org/e-print/2608.10184v1 on 6 October 2026. Read: sections
  1.2, 2, 3 and 4. Results are numbered as in the compiled paper (one
  counter per section, shared by theorems, propositions, lemmas,
  corollaries and remarks) and named by their LaTeX labels. Line numbers
  ("l.") refer to `manuscript.tex`.
- **Formal proof.** Commit `2a06058` of `main`
  (2a06058f777734e056d14425342df549e58cb328, "End phase 3: remove the
  coordination files, update the READMEs"), the state after phase 3,
  reviewed on the branch `review/paper`. Module names are those after
  phase 3.
- **Method.** The commit was built with `make build` in the project's
  toolchain (Rocq 9.1.1, MathComp 2.6.0, MathComp-Analysis 1.16.0). From the
  `.glob` files of that build, an adaptation of `scripts/unused.py` computed
  the dependency graph below the two theorems that `PaperMainResults.v`
  uses, `PaperMainFinalAssembly.paper_main_results_from_conditioned` and
  `PaperMainConditionedLimit.paper_main_conditioned_limit`: for each
  declaration, the declarations that its statement and proof name. The
  adaptation (not in the repository) differs from `scripts/unused.py` in
  three points: it reads the modules in folders and in `library/`, it starts
  from these two theorems, and it outputs the graph. The graph has 5,681
  declarations in 625 modules: 602 of `theories/` and 23 of the 25 files of
  `library/` (530 declarations). Each formal counterpart below was found
  in that graph, and its statement was read. The reading was done on the
  state just before phase 3 (commit `2b85d8e`); a script checked that the
  182 declarations cited here have the same statements in `2a06058`. For
  the main results the proof was read or skimmed as well. Some proofs were read only through their module
  headers and statements: the walk counting of the feature edge
  (`SquareFree.Walk*` modules), the measurability modules, and the
  interpolation machinery below Lemma 3.9 (`Multirow.*`, `Row.*`, `Joint.*`
  modules). Constants are those of the formal statements and
  definitions; where a number was computed from them, the text says so.

## How to read the table

- One row per theorem, proposition, lemma and corollary of the paper, in
  the paper's order (39 rows). Remarks 3.6, 3.7 and 4.7 are discussed after
  the table. Unlabelled steps of the paper (the padding of section 3, the
  bound eq:b-bound, the spectral split of section 4, ...) are discussed in
  sections (b) and (c).
- Formal names are `Module.name`. `Module` is the logical path below the
  root `EllipsoidFitting`: `theories/Hybrid/Bulk.v` is `Hybrid.Bulk`.
  Library names start with `GaussianAnalysis`. Unless a sentence says
  otherwise, every name is a declaration that the two theorems used by
  `PaperMainResults.v` depend on.
- Relation, comparing the formal counterpart with the paper's result:
  - **same**: the same statement, up to constants, normalization and
    explicit thresholds on d, proved by the same argument;
  - **weaker**: the formal statement says less (fewer cases, a worse
    constant or rate, an extra hypothesis), and that suffices where the
    formal proof uses it;
  - **stronger**: the formal statement says more (fewer hypotheses, or a
    non-asymptotic bound);
  - **replaced**: the formal proof reaches the same point of the argument
    by another argument; the statement may coincide up to constants;
  - **absent**: the formal proof does not need the result.
- Notation: d is the dimension, n (formally N) the number of points,
  W_i = (x_i x_i^T - I)/sqrt(d), Q_x Q_x^* the Gram matrix of the quadratic
  features (formally the raw feature Gram matrix), K_k the cone of PSD
  matrices with condition number at most k, S_F the Frobenius unit sphere.

## Table

| Paper result | Formal counterpart | Relation | Note |
|---|---|---|---|
| Theorem 1.2 `thm:main` (sec. 1.2) | `PaperMainFinalAssembly.paper_main_results_from_conditioned`, `Asymptotics.paper_main_sat_from_conditioned`, `Unsat.Limit.paper_main_unsat_supercritical_limit` | same | Part (a) is derived from thm:conditioned, as the paper derives it from thm:sat. The formal statement also asserts that the event is measurable for every n and d (`Measurability.Fit.pm_fit_event_measurable`). |
| Theorem 1.3 `thm:conditioned` (sec. 1.2) | `PaperMainConditionedLimit.paper_main_conditioned_limit`, `PaperMainConditionedLimit.paper_main_conditioned_fixed_limit`, `Conditioned.FromLower.paper_main_conditioned_from_lower` | same | Constants lambda_+ = 1/lambda_- = 2 kappa + 1, where kappa = 2 k0^2 and k0 = O((1/4 - beta)^-1) for a density beta chosen in (alpha*, 1/4). The paper has 4 kappa_1^2 = 16 kappa_0^2. Both are O((1/4 - alpha*)^-2), as in Remark 3.6. Measurability is added. |
| Corollary 1.4 `cor:alternative` (sec. 1.2) | `Balanced.Probability.paper_main_balanced_from_sat`, `Balanced.Limit.paper_main_balanced_supercritical_limit`, `Gaussian.Spanning.paper_main_gaussian_spanning_ae` | same | Below 1/4 only the exclusion half of lem:homogeneous (ii) is used; it needs no spanning. Above 1/4 the existence half needs the sample to span R^d; the formal proof proves that this holds almost surely when n >= d, which the paper asserts. Measurability is added. |
| Lemma 2.1 `lem:psd-width` (sec. 2.1) | `Gaussian.PsdWidth.paper_main_gaussian_psd_projection_second_moment`, `Gaussian.PsdWidth.paper_main_gaussian_psd_width_bounds` | same | E \|Z_+\|_F^2 = D_d/2 by Moreau's decomposition and Z = -Z in law, as in the paper. The width bounds come from the Gaussian Poincare inequality instead of the cited Proposition 10.2 of Amelunxen, Lotz, McCoy and Tropp (see (a)). The clause w = d/2 + O(1) is not stated separately. |
| Lemma 2.2 `lem:widthcone` (sec. 2.1) | `Gaussian.ConditionWidthBound.paper_main_gaussian_condition_width_lower`, `Gaussian.ConditionWidthBound.paper_main_gaussian_condition_width_large` | stronger | Non-asymptotic: w(K_k cap S_F) >= (1/2 - s) d - 3 - 864/d for every d and s > 0, with k = (20 + s)/s. Same candidate (Z_+ + s sqrt(d) I)/norm as the paper, with the cutoff \|Z\|_op <= 20 sqrt(d). No semicircle law, no operator-norm limit, no uniform integrability (route R1). |
| Lemma 2.3 `lem:gordon` (sec. 2.2) | `GaussianAnalysis.comparison.gordon.gordon`, `GaussianAnalysis.comparison.escape.auxT_bilT_minmax`, `Gordon.Width.paper_main_gordon_finite_width_margin` | replaced | Only an expectation bound for finite families: E min_y max_t z_y^T A v_t >= E max_t <h, v_t> - sqrt(N), proved by Kahane's comparison applied to a soft min-max. No tail bound, no gamma_0, no compact index set. The probability bound needed later comes from the concentration of the data functional (route R2). |
| Lemma 2.4 `lem:escape` (sec. 2.2) | `GaussianAnalysis.comparison.escape.gordon_escape`, `Gaussian.EscapeTail.paper_main_gaussian_escape_sqrt_tail` | weaker | Proved, where the paper cites Gordon (1988): P(inf_T \|A x\| <= sqrt(N - 1) - w(T) - u) <= exp(-u^2/2). The threshold sqrt(N - 1) <= E\|g_N\| gives a smaller event than the paper's, and it is what eq:gap-mean uses. T may be any nonempty set of unit vectors, not only a compact one. |
| Lemma 2.5 `lem:gauss-rect` (sec. 2.2) | `Gaussian.OperatorTail.paper_main_gaussian_operator_tail`, `Gaussian.FeatureTail.paper_main_gaussian_operator_exponential_tail` | weaker | Proved by nets, where the paper cites Vershynin: P(\|A\|_op > 2B) <= 2 exp(20 ln 2 (N + M) - B^2/2) for standard entries, in place of sigma (sqrt(N) + sqrt(M) + t). Enough for the O(sqrt(n)) bounds that are used. |
| Lemma 2.6 `lem:squarefree-edge` (sec. 2.3) | `SquareFree.EdgeUpperLimit.paper_main_squarefree_upper_bound`, `SquareFree.LowerProbability.paper_main_squarefree_lower_probability`, `SquareFree.Coercivity.paper_main_squarefree_coercivity_generic` | weaker | Bounds, not limits: V V^T <= 106 d^2 I when N <= d^2, and the raw feature Gram matrix is >= (d^2/128) I only when 4 N <= d^2, that is density at most 1/4 (the paper: any compact subset of (0, 1/2)). Proved by moment methods instead of citing Kogan, Nandy and Huang (see (a) and route R3). |
| Lemma 2.7 `lem:diagonal-feature-block` (sec. 2.3) | `DiagonalBlock.Limit.paper_main_diag_block_tends_to_zero`, `DiagonalBlock.Moment.paper_main_diag_trace_moment` | replaced | D^T D and D D^T are <= 3 N I outside an event of probability O(1/d) when N >= c d^2. A fourth trace moment and Markov's inequality replace truncation and matrix Bernstein. No upper bound on the density is needed. |
| Proposition 2.8 `prop:feature-edge` (sec. 2.3) | `Fixed.LowerProbability.paper_main_fixed_lower_probability`, `Feature.UpperProbability.paper_main_feature_upper_edge`, `Gaussian.PublicFeature.paper_main_public_gaussian_feature_exceptional_event` | weaker | (d^2/128) I <= Q Q^* holds at N = floor(beta d^2) with beta < 1/4, and Q Q^* <= 109 d^2 I for densities in [c, 1]. Each holds for one sequence N(d), not uniformly over a compact set of densities. The Gaussian map is bounded by C(rho) sqrt(N), C(rho) = 4 sqrt(20 ln 2 (1 + 2/rho) + 1), with probability at least 1 - 2 exp(-N/2). |
| Corollary 2.9 `cor:feature-sat` (sec. 2.3) | `Feature.SpectralBridge.paper_main_raw_feature_coercive`, `Feature.SpectralBridge.paper_main_raw_feature_operator` | weaker | W W^* >= (d/128) I and \|W^* y\|_F <= sqrt(109) sqrt(d) \|y\|, only for densities below 1/4 (the paper: below 1/2). That is the range the satisfiable phase uses. |
| Lemma 2.10 `lem:data` (sec. 2.4) | `Gaussian.DataRadius.paper_main_data_radius_good`, `Data.CoherenceLimit.paper_main_data_coherence_log_good`, `Head.DataLog.paper_main_head_data_log_probability`, `Data.SampleTail.paper_main_data_coordinate_tail` | weaker | Radius 2 sqrt(d), coherence 73 ln d and sparse norms L d (ln d)^2 as in the paper, under N <= C d^2 only. The coordinate bound x_ia^2 <= C log d (eq:coord-max) is not proved; the proof uses \|x_ia\| < d^(1/4) instead (route R4). |
| Lemma 2.11 `lem:hw` (sec. 2.4) | `Gaussian.QuadraticTail.paper_main_gaussian_quadratic_tail`, `Gaussian.Residual.paper_main_gaussian_residual_tail` | same | Proved for Gaussian x, where the paper cites Rudelson and Vershynin: P(\|x^T B x - Tr B\| >= u) <= 2 exp(-u^2/(4 \|B\|_F^2 + 4 b u)) for b >= \|B\|_op, which gives the paper's form with c = 1/8. Used only for the residuals r_i of prop:heads. |
| Lemma 2.12 `lem:homogeneous` (sec. 2.5) | `Geometry.Homogeneous.paper_main_homogeneous_kernel`, `Geometry.Homogeneous.paper_main_homogeneous_witness`, `Geometry.Separation.paper_main_homogeneous_existence`, `Geometry.Exclusion.paper_main_fit_balanced_exclusive` | same | The paper's nearest-point argument, written as the minimization of \|D_X(S)\|^2 over {S >= 0, Tr S = 1}. The exclusion half is proved without the spanning hypothesis, and the cases d = 0 and n = 0 are treated. |
| Theorem 3.1 `thm:sat` (sec. 3) | `Conditioned.FromLower.paper_main_conditioned_from_lower`, `Conditioned.SpectralReduction.paper_main_subcritical_spectral_reduction`, `Head.SubcriticalFit.paper_main_head_subcritical_fit_exception`, `Cone.HeadTailFit.paper_main_cone_head_tail_conditioned_fit` | same | Same conclusion at N = floor(beta d^2), beta < 1/4, with the constants (2 kappa + 1)^(+-1), kappa = 2 k0^2 (the paper: (4 kappa_1^2)^(+-1)). Same assembly: convex separation, head-tail decomposition, prop:heads, prop:lowinf, tiny-tail case; the steps differ in detail (routes R5 and R6). |
| Lemma 3.2 `lem:convex-separation` (sec. 3.1) | `Cone.Kernel.paper_main_cone_kernel_exists_support`, `Conditioned.SupportFit.paper_main_box_support_conditioned_fit` | weaker | Only the direction that is used: if every unit y has positive support on K_k cap S_F, some point of K_k cap S_F is orthogonal to every W_i. The compact convex set is the image of the trace-one slice of the cone, not of the box B. The characterization of the interior is not proved; the paper does not use it. |
| Proposition 3.3 `prop:heads` (sec. 3.1, proof sec. 3.2) | `Head.RegularProbability.paper_main_head_width_coercive_probability_uniform`, `Head.WidthRegular.paper_main_head_width_regular_event_fixed`, `Head.WidthRegular.paper_main_head_width_regular_transfer` | weaker | For every eps > 0, every head of at most K d ln d rows has section width >= (1/2 - eps) d, for the cone K_k with k = 2 k0^2. The paper has a loss o(d) and k = 2 kappa_0. The coercivity of the Gram matrix is a hypothesis on the sample, and the measurable maximizer is replaced by an approximate one over a finite net (route R5). |
| Proposition 3.4 `prop:lowinf` (sec. 3.1, proof secs. 3.3-3.5) | `Head.SubcriticalProbability.paper_main_head_subcritical_probability`, `Head.SubcriticalFixed.paper_main_head_subcritical_fixed_event`, `Head.SubcriticalFixed.paper_main_head_list_positive` | weaker | Only positivity of the tail score is exported; the margin c_* d stays inside the proof. Three hypotheses on the sample are added: no coordinate reaches d^(1/4), the feature operator bound L sqrt(d), and section width at least (1/2 - g/16) d for every head of the same size, g = 1/2 - sqrt(alpha). |
| Lemma 3.5 `lem:regularity` (sec. 3.1) | `Head.TailDecompositionLog.paper_main_head_tail_regularity`, `Head.TailDecomposition.head_tail_decomposition_explicit` | same | Same peeling, with the explicit constant C_theta = 16/(theta^2 ln 2). |
| Lemma 3.8 `lem:head-correction-bounds` (sec. 3.2) | `Geometry.HeadSpectral.paper_main_head_correction_bounds_cone`, `Geometry.HeadEntries.paper_main_head_correction_bounds`, `Head.CorrectionScale.paper_main_head_correction_eventual` | weaker | Same exact correction a_J = Q_J^-1 r_J. Coarser rates: residual threshold of order d^(-1/4), \|E_J\|_F of order d^(-7/32), \|E_J\|_op of order d^(-5/8). The corrected matrices lie in K_(2 k0^2), not K_(2 kappa_0), because only the spectral box of P is used. \|E_J\|_F is bounded with the lower feature edge alone. |
| Lemma 3.9 `lem:interpolation` (sec. 3.4) | `Soft.Comparison.paper_main_soft_public_comparison`, `Multirow.IntegratedBound.paper_multirow_integrated_bound_results` | weaker | Same path sqrt(t) W + sqrt(1 - t) G and same bound 4 R_(N,d) M_3/(3 d^(3/2)), but proved only for the soft min-max of Lemma 3.12, with M_3 = 10 b^3 (beta + gamma)^2 theta/sqrt(d) inserted, b a bound on the operator norm of the matrices. There is no statement for a general C^3 function F. |
| Lemma 3.10 `lem:chaos-ibp` (sec. 3.4) | `Quadratic.TimeStein.quadratic_gaussian_time_stein`, `Joint.SteinIdentities.joint_gaussian_stein_cancellation`, `Chaos.SecondContractionBounds.chaos_projective_bound` | weaker | Same identity and same remainder bound 4 \|x\|^2 \|D^3 F\|_(pi,op), for the soft min-max only. The second-order Gaussian integration by parts that the paper states without proof is proved (`Gaussian.VectorStein.gaussian_vector_second_stein`). |
| Lemma 3.11 `lem:max-radius` (sec. 3.4) | `Radius.ExpectationBound.gaussian_expected_maximum_radius` | same | Same bound d + 2 sqrt(d log N) + 2 log N and same proof (moment generating function of the chi-square, log-sum-exp, Jensen). |
| Lemma 3.12 `lem:soft` (sec. 3.4) | `Soft.Extrema.soft_minimax_bounds`, `Tensor.ProjectiveSum.matrix_nested_projective_sum_low_influence`, `Soft.MatrixProjectiveBound.soft_matrix_projective_sum_bound` | same | Same sandwich bounds and the same three terms of the third derivative, with the explicit constant C = 10. |
| Lemma 3.13 `lem:gaussian-soft-head` (sec. 3.5) | `Soft.FeatureMargin.paper_main_public_goe_soft_margin`, `Gordon.SoftMargin.paper_main_gordon_soft_width_margin`, `Head.SectionApproxWidth.paper_main_head_section_net_width` | replaced | Only the mean bound eq:PhiG-mean, proved directly from Gordon's inequality in expectation on the two finite nets: E_G Phi >= sqrt(2/d) (w(net) - sqrt(N)) - ln r/beta. The high-probability bound eq:net-margin-G, the bound on \|G^*\| (eq:Gstar-bound) and the Cauchy-Schwarz step have no counterpart (route R2). |
| Corollary 3.14 `cor:chaos-soft-head` (sec. 3.5) | `Head.SoftTail.paper_main_head_soft_expectation`, `Soft.ConeMargin.paper_main_data_soft_cone_margin` | same | An explicit lower bound on E_W Phi for a fixed head. The formal scores are the paper's divided by sqrt(d), so the formal inverse temperatures A d sqrt(d) are the paper's beta = gamma = L d. |
| Lemma 3.15 `lem:clipped-soft-heads` (sec. 3.5) | `Data.SoftConcentration.paper_main_data_soft_clipped_lower_margin`, `Head.SubcriticalTail.paper_main_head_subcritical_clipped_tail`, `Head.SubcriticalFamily.paper_main_head_subcritical_family_event` | weaker | Every coordinate is clipped at d^(1/4), instead of the radius at 2 sqrt(d). The clipped functional is 2 k d^(-1/4)-Lipschitz, so one head fails with probability exp(-c d^(3/2)) instead of exp(-c d^2). That still beats the exp(C d (ln d)^2) heads (route R4). |
| Theorem 4.1 `thm:unsat` (sec. 4) | `Unsat.Limit.paper_main_unsat_supercritical_limit`, `Unsat.Limit.paper_main_unsat_fixed_density_limit`, `Unsat.Limit.paper_main_unsat_fixed_density_limit_from_events` | same | Same statement, with measurability. P(fit) is bounded by P(the upper feature edge fails) + P(F_d), where F_d is a union over a net of orientations. The steps of section 4.1 are replaced (routes R8 to R12). |
| Lemma 4.2 `lem:homogeneous-witness` (sec. 4.1) | `Pinching.Loss.paper_main_fit_unit_witness` | weaker | Only "a fit gives a unit witness", the direction that thm:unsat uses. It needs no spanning hypothesis, so the unsatisfiable phase never uses that the sample spans R^d. |
| Proposition 4.3 `prop:translated-univ` (sec. 4.1) | `Hybrid.FiniteMean.paper_main_hybrid_finite_mean_comparison`, `Unsat.FiniteTail.paper_main_unsat_ordered_tail` | replaced | No comparison of expected ground states over closed sets. The formal proof compares expected soft minima over a finite prior, with error 2 eta + C(beta, eta) eps \|B\|_F where eps bounds \|B\|_op, and reaches infima only after concentration (routes R8 to R10). |
| Proposition 4.4 `prop:hybrid-gap` (sec. 4.1, proof sec. 4.3) | `Hybrid.Assembly.paper_main_hybrid_gap_event`, `Hybrid.Assembly.paper_main_hybrid_gap_event_joint` | stronger | H only symmetric (the paper: PSD), no upper bound \|H\|_F^2 + \|B\|_F^2 <= 4, any gamma > 1/4 with \|N - gamma d^2\| <= eta d^2, bulk dimension up to d - r. Probability at least 1 - exp(-c d^2), from the paper's three cases. |
| Proposition 4.5 `prop:true-net-gap` (sec. 4.1, proof sec. 4.4) | `Unsat.Orientation.paper_main_unsat_orientation_constants`, `Orientation.Exception.paper_main_orientation_exception`, `Orientation.Union.paper_main_orientation_union_fit` | replaced | For each orientation of a fixed net, one event of probability at most exp(-N e^2/32) contains every sample with an admissible candidate of risk at most 16 L tau. The union bound runs over orientations only, with entropy O(d), not over heads and offsets with entropy O(d^(3/2)) (route R9). |
| Lemma 4.6 `lem:transport` (sec. 4.1) | `Projection.Pinching.paper_main_pinching_perturbation`, `Pinching.Loss.paper_main_pinching_cutoff_bulk`, `Orientation.Witness.paper_main_orientation_fit_witness` | replaced | The witness is pinched by the projector U of the net member: A = U S U + (I - U) S (I - U), with \|S - A\|_F <= 4 \|U - P\|_F \|S\|_F. No rotation O and no principal angles (route R9). |
| Proposition 4.8 `prop:finite-prior-free-entropy` (sec. 4.2) | `Hybrid.FiniteMean.paper_main_hybrid_finite_mean_comparison`, `Loss.Replacement.paper_main_loss_array_comparison`, `Loss.ReplicaComparison.paper_main_loss_product_comparison` | replaced | The paper sketches a modification of Bandeira and Maillard (Theorem 4.6 of their paper). The formal proof is complete and has its own route: rows are replaced one at a time, the soft-min increment is expanded in replica averages of products of loss factors, and each is compared by Gaussian interpolation. Error 2 eta + C(beta, eta) eps \|B\|_F, uniform in N, the offsets and the prior (route R10). |
| Lemma 4.9 `lem:ground-state-transfer` (sec. 4.2) | `Orientation.Prior.paper_main_orientation_prior`, `Loss.QuadraticPrior.paper_main_quadratic_prior_positive`, `Orientation.BlocksLoss.paper_main_orientation_candidate_bound_rotate` | replaced | The delta-net, its entropy and the Lipschitz step are used sample by sample after concentration, on the data side only, with beta fixed. There is no comparison of expected ground states. |
| Lemma 4.10 `lem:head-smallball` (sec. 4.3) | `Head.SmallBallUniform.paper_main_head_small_ball_uniform_poly`, `Head.SmallBallPZ.paper_main_head_small_ball_probability` | replaced | Same statement with a_0^2 = 1/4864 and delta_0 = 1/1216, for n >= 306432 (r + 1)^3. Proved with a net, a Markov truncation and binomial tails instead of the VC inequality, and with E Y^4 <= 19 sigma^4 computed instead of hypercontractivity (route R11). |
| Lemma 4.11 `lem:projected-bulk-escape` (sec. 4.3) | `Hybrid.Bulk.paper_main_hybrid_bulk_event`, `Projected.BulkConditional.paper_main_projected_psd_conditional_tail`, `Hybrid.Assembly.paper_main_hybrid_operator_event` | stronger | Holds for every fixed head, without the small-ball condition. The distance from R(B)_J to the range of the head features replaces \|P_J R(B)_J\| (a complement basis and Bessel's inequality), so no full column rank is needed (route R11). |
| Lemma 4.12 `lem:conditional-true-mean-gap` (sec. 4.4) | `Hybrid.FiniteMean.paper_main_hybrid_finite_goe_mean`, `Loss.ExpectedGap.paper_main_loss_expected_gap`, `Unsat.FiniteTail.paper_main_unsat_ordered_tail` | replaced | Nothing is conditioned on the head. E Z_goe >= e (1 - exp(-c d^2)) holds for the mean over heads and bulks together, and E Z_data >= E Z_goe - (2 eta + C eps \|B\|_F) (route R9). |

Count by relation: same 12, weaker 14, stronger 3, replaced 10, absent 0.

**Remarks.** Remarks 3.6, 3.7 and 4.7 have no formal statement. Their
claims hold in the formal proof as follows.
- Remark 3.6 (condition number O((1/4 - alpha)^-2)): the formal constants
  of Theorem 1.3 have the same order.
- Remark 3.7 (where 1/4 enters the satisfiable phase): 1/4 enters only
  through 1/2 - sqrt(alpha) > 0 (`Soft.ParameterChoice.paper_main_soft_subcritical_gap`).
  The remark also says that the feature map stays well conditioned up to
  density 1/2. The formal proof does not prove that: its lower feature edge
  stops at 1/4 (Lemma 2.6).
- Remark 4.7 (where 1/4 enters the unsatisfiable phase): the hypothesis
  gamma > 1/4 is used only in the hybrid gap (`Hybrid.Density.paper_main_hybrid_density_margin_gamma`)
  and passed down from there; gamma < 1/2 is used only to get N <= d^2 for
  the upper feature edge.

## (a) Results the paper cites without proof

The formal proof assumes nothing from the paper or the literature: every
cited result is either proved, replaced by a weaker statement that it
proves, or avoided.

| Cited result | Where the paper uses it | What the formal proof does |
|---|---|---|
| Kogan, Nandy and Huang, extreme eigenvalues of polynomial-scaling kernel matrices, Thm 1.2(2a) | Lemma 2.6 | Its own moment method, with non-sharp constants (route R3). Upper edge: trace moments of the off-diagonal square-free Gram matrix, counted by closed walks with Gaussian moments (`SquareFree.EdgeUpper.paper_main_squarefree_offdiag_trace_le`). Lower edge: the non-backtracking recursion of their Lemma 5.1 (`SquareFree.EdgeLower.pmlo_knh`), a Chebyshev step (`SquareFree.EdgeLower.pmlo_cheb_box`), non-backtracking trace moments (`SquareFree.WalkNBMoment.pmnct_moment_le`) and column-norm concentration for the remainders (`Column.RemainderProbability.paper_main_column_remainder_probability`). The resulting box -(49/24) I <= T_1 - s I, with s about sqrt(2 n/d^2), is a little worse than their sharp constant 2. With 49/24 the final scalar step (63/64 + s^2 - (49/24) s > 0) works for s < 0.78, about density 0.3 (our computation), and the formal statement assumes 4 n <= d^2. |
| Tropp, matrix Bernstein, Thm 6.6.1 | Lemma 2.7 | Not used. A fourth trace moment (`DiagonalBlock.Moment.paper_main_diag_trace_moment`) and Markov's inequality. |
| Vershynin, norms of rectangular Gaussian matrices, Thm 7.3.1 | Lemma 2.5, used in Prop. 2.8, Lemma 2.10, eq:Gstar-bound, Lemma 4.11 | A net bound with worse constants (`Gaussian.OperatorTail.paper_main_gaussian_operator_tail`). eq:Gstar-bound is not needed (route R2). The library also proves the sharp mean and tail of the operator norm, but the proof of the paper does not use them. |
| Rudelson and Vershynin, Hanson-Wright inequality | Lemma 2.11, in prop:heads | Its own proof for Gaussian vectors: orthogonal diagonalization, rotation invariance and a chi-square Chernoff bound (`Gaussian.QuadraticTail.paper_main_gaussian_quadratic_tail`, `Gaussian.OrthogonalTail.paper_main_gaussian_orthogonal_square_two_sided_tail`). |
| Gordon (1985), comparison theorem for min-max of finite Gaussian arrays, in probability; Thrampoulidis, Oymak and Hassibi for background | Lemma 2.3 | The expectation form for finite families, proved in the library from Kahane's comparison inequality applied to a soft min-max (`GaussianAnalysis.comparison.gordon.gordon`, `GaussianAnalysis.gaussian.gauss_interpolation.gauss_comparison`). It has no equal-variance hypothesis. The probability form is never proved (route R2). |
| Gordon (1988), escape through a mesh | Lemma 2.4, in Lemma 4.11 | Proved: the expectation bound in the library (`GaussianAnalysis.comparison.escape.gordon_escape`), then Gaussian concentration; threshold sqrt(N - 1) (`Gaussian.EscapeTail.paper_main_gaussian_escape_sqrt_tail`). |
| eq:chi-mean, sqrt(s - 1) <= E\|g_s\| <= sqrt(s) | Lemmas 2.3, 2.4, 4.11 | Proved (`Gaussian.Norm.paper_main_gaussian_norm_expectation`, `Gaussian.NormConcentration.paper_main_gaussian_norm_mean_lower`); the Gamma-function formula is not. |
| Boucheron, Lugosi and Massart, Gaussian concentration, Thm 5.6 | Lemmas 2.3, 3.15, eq:radius | Proved in the library by the Herbst argument (`GaussianAnalysis.comparison.gauss_concentration.gauss_concentration`); tails by Chernoff (`Gaussian.LipschitzConcentration.paper_main_gaussian_lipschitz_lower_tail`). |
| Boucheron, Lugosi and Massart, McDiarmid's inequality, Thm 6.2 | Prop. 4.5 | Its own bounded-difference inequality, on full rows, by Hoeffding's lemma and induction over rows (`Loss.ConcentrationRow.paper_main_concentration_rows`, `Loss.ConcentrationTail.paper_main_concentration_lower_tail`). For rows that change the function by at most 1/N, it gives exp(-N t^2/2) where McDiarmid gives exp(-2 N t^2): an exponent 4 times smaller, which is enough. |
| Amelunxen, Lotz, McCoy and Tropp, Prop. 10.2 (width versus statistical dimension) | Lemma 2.1 | Its argument written out for the PSD cone, with the Gaussian Poincare inequality of the library (`Gaussian.WidthVariance.paper_main_gaussian_mean_positive_square_lower`, `GaussianAnalysis.comparison.gauss_concentration.gauss_poincare_lipschitz`). |
| Anderson, Guionnet and Zeitouni, Thm 2.1.22 (\|Z\|_op/sqrt(d) -> sqrt(2)), and the semicircle law | Lemma 2.2 | Not used. A net bound \|Z\|_op <= 20 sqrt(d) with probability at least 1 - 2 exp(-10 d) (`Gaussian.SymmetricOperatorTail.paper_main_symmetric_gaussian_operator_good_set`), the lower bound E\|Z_+\|_F >= d/2 - 1 from Lemma 2.1, and E (Tr Z)^2 = d (route R1). |
| Bandeira and Maillard, Lemma 3.6 | Lemma 2.2 (the paper reproves it) | Not used. |
| Bandeira and Maillard, free-entropy universality, Thm 4.6 and sec. 4 | Prop. 4.8 (only sketched) | Not used. A complete proof by another route (route R10). |
| Aliprantis and Border, measurable maximum theorem, Thm 18.19; the measurable minimum theorem for eq:net-selector | Prop. 3.3, sec. 3.5 | Not used. The maximizer P(Z) is the first maximizer over a fixed finite net (`Cone.ApproxSelector.paper_main_cone_selector_gaussian`), and the events are shown measurable through countable nets (`Head.SectionMeasurable.paper_main_head_section_support_measurable`). Nets of a fixed head are chosen classically, and probabilities are integrated over the head by a Fubini bound on sections (routes R5 and R7). |
| Second-order Gaussian integration by parts, E[(x_a x_b - delta_ab) f] = E[d_a d_b f] (stated without reference) | Lemma 3.10 | Proved, for f with polynomial growth (`Gaussian.VectorStein.gaussian_vector_second_stein`, from `GaussianAnalysis.gaussian.gauss_ibp.gauss_ibp2`). |
| Weyl's inequality | Lemma 3.8 | Replaced by addition in the Loewner order (`Geometry.HeadCorrection.paper_main_head_condition_transfer`). |
| Packing bounds for nets, (1 + 2/rho)^N and the like | sec. 3.5, Prop. 4.5, Lemma 4.9 | Grid nets with log-cardinality (4 + 4/eps) ln 2 times the dimension (`Gordon.Entropy.paper_main_gordon_entropy_net`, `Loss.JointNet.paper_main_loss_joint_net`). |
| Szarek, nets of the Grassmannian | Prop. 4.5 | Its own net of orthogonal frames, with log-cardinality (4 + 8 r/tau) ln 2 (r + 1)(d + 1) (`Orientation.Net.paper_main_orientation_net`). It is worse than Szarek's bound and enough only because the head rank is bounded (route R8). |
| The principal-angle identity | Lemma 4.6 | Not needed (pinching, route R9). |
| Gaussian hypercontractivity, \|Y\|_4 <= 3 \|Y\|_2 for degree two | Lemma 4.10 | Not used: E Y^4 <= 19 sigma^4 is computed from the moments of x^2 - 1 after a rotation (`Head.SmallBallFourth.paper_main_head_small_ball_moments`). |
| Paley-Zygmund inequality | Lemma 4.10 | The library's `GaussianAnalysis.probability.moments.paley_zygmund`. |
| Sauer's lemma and the VC inequality (Devroye, Gyorfi and Lugosi, Thm 12.5) | Lemma 4.10 | Not used: a net of the parameters, a Markov truncation and binomial tails (route R11). |
| Rotation invariance of the standard Gaussian (used implicitly) | eq:decompose, Lemma 4.11 | Proved in the library (`GaussianAnalysis.comparison.gauss_law.gauss_orthogonal_law`) and used through `Projected.BulkLaw.paper_main_projected_law` and `Orientation.Rotation.paper_main_orientation_rotate_law`. |
| Spectral theorem and spectral projectors (used implicitly) | eq:split-def, sgn(M_u) in thm:sat | The library's real spectral theorem (`GaussianAnalysis.matrix.real_spectral.symmetric_spectral`). sgn(M_u) is avoided (route R6). |
| Almost sure spanning of the sample for n >= d (stated) | Lemma 2.12, cor:alternative, thm:unsat | Proved where it is needed, for cor:alternative (`Gaussian.Spanning.paper_main_gaussian_spanning_ae`). thm:unsat does not need it. |

## (b) Changes of route

- **R1. Widths of cones (sec. 2.1, Lemmas 2.1 and 2.2).** The projection
  onto the PSD cone is built as a nearest point, with Moreau's
  decomposition, without the spectral theorem
  (`Cone.Projection.paper_main_psd_projection`,
  `Cone.Projection.paper_main_psd_moreau`). Lemma 2.1 uses the
  Poincare inequality in place of the cited Proposition 10.2 of Amelunxen,
  Lotz, McCoy and Tropp. Lemma 2.2 keeps the paper's
  candidate, but bounds its value pointwise on and off the event
  |Z|_op <= 20 sqrt(d) (`Gaussian.ConditionWidth.paper_main_gaussian_condition_point_bound`)
  and integrates, so no limit in probability, no semicircle law and no
  uniform integrability are used. The result is non-asymptotic.
- **R2. Gordon's inequality in expectation (secs. 2.2, 3.3, 3.5).** The
  paper proves a tail bound for the min-max over the whole sphere and a
  compact set (Lemma 2.3), applies it at t = eta d (eq:gordon-tail-margin),
  restricts to nets on the event |G^*| <= C_G sqrt(d), and passes to
  expectations by Cauchy-Schwarz (Lemma 3.13). The formal proof applies
  Gordon's inequality in expectation directly to the finite nets of dual
  vectors and of the head section, then the log-sum-exp bound
  (`Gordon.SoftMargin.paper_main_gordon_soft_width_margin`). The
  net loss is eps sqrt(D), also in expectation
  (`Head.SectionApproxWidth.paper_main_head_section_net_width`).
  Probability enters only after the comparison with the data, through the
  concentration of the clipped data functional (R4).
- **R3. Feature edge (sec. 2.3).** Both edges are proved by moment
  methods (see (a)). The lower edge holds only up to density 1/4, the
  upper edge for densities in [c, 1], with explicit but non-sharp
  constants (d^2/128 and 109 d^2) and explicit polynomial rates, for each
  sequence N(d) separately; the paper's compactness argument over K is not
  needed. The lower edge uses the upper edge and the coordinate clipping
  inside its column-norm events (`Column.ConcentrationFrame.paper_main_column_frame`),
  which the paper's lower edge does not. The bound |E_J|_F^2 = a^T Q_J a
  is replaced by a^T r <= |r|^2/mu, so the head correction needs only the
  lower edge (`Geometry.HeadCoefficients.paper_main_head_correction_energy`).
- **R4. Clipping (secs. 2.4, 3.5).** The paper clips the radius at 2 sqrt(d),
  bounds the clipping error with nuclear norms and chi-square tails, and
  gets e^(-c d^2) per head. The formal proof clips every coordinate at
  d^(1/4) (`Data.Clipped.paper_main_data_clipped_feature`). Each
  clipped score is then 2 k d^(-1/4)-Lipschitz in all coordinates
  (`Data.ClippedSoft.paper_main_data_clipped_soft_lipschitz`), the
  mean changes by at most V/a + 2 a N d exp(-sqrt(d)/2)
  (`Gaussian.ClippingTransfer.paper_main_gaussian_clipping_mean_loss`),
  and one head fails with probability exp(-c d^(3/2)). The union over the
  exp(C d (ln d)^2) heads still goes to 0
  (`Clipping.Rates.paper_main_clipped_head_union_rate`). The event
  that some coordinate reaches d^(1/4), of probability at most
  2 N d exp(-sqrt(d)/2), is added to the exceptional set
  (`Clipping.Limits.paper_main_coordinate_clipping_tends_to_zero`).
- **R5. Head sections (sec. 3.2, Prop. 3.3, Lemma 3.8).** The exact
  correction of the paper is kept, with four differences. The Borel
  maximizer P(Z) is replaced by the first maximizer over a fixed finite
  eps-net of K_k0 cap S_F, which is measurable and loses eps |Z|_F
  (`Cone.ApproxSelectorResidual.paper_main_cone_selector_residual`);
  hence a loss eps d in Prop. 3.3 instead of o(d). The residuals r_i are
  bounded at the coarse threshold sqrt(4 + 4 k0) d^(-1/4), with the
  Gaussian Hanson-Wright inequality and a rate 2 exp(-sqrt(d)/2) per row
  (`Clipping.ResidualRates.paper_main_residual_exponential_rate`), and the
  Markov step uses tau = d^(-4)
  (`Gaussian.ConditionalException.paper_main_conditional_exception_reverse_markov`).
  The integration over Z uses 2v <= v^2/a + a with a = d^2 instead of
  Cauchy-Schwarz (`Head.WidthExpectation.paper_main_head_width_expectation_transfer`).
  The Weyl step uses only the box (k0 sqrt(d))^-1 I <= P <= k0/sqrt(d) I
  (`Geometry.HeadSpectral.paper_main_head_spectral_box`), whose
  ratio is k0^2, so the corrected matrices lie in K_(2 k0^2).
- **R6. Assembly of thm:sat (sec. 3.1).** The convex separation is done
  on the trace-one slice of the cone, made compact by adding the Loewner
  witness as a coordinate (`Cone.KernelSlice.paper_main_cone_kernel_slice_compact`,
  `Cone.Kernel.paper_main_cone_kernel_variational`). Section
  matrices are rescaled into [I, k I] and the box is [1/2, k + 1/2]
  (`Cone.HeadTailFit.paper_main_condition_box`), which gives the
  constants (2 k + 1)^(+-1). In the tiny-tail case the perturbation is
  delta M_u/|M_u|_F instead of delta_0 sgn(M_u), so no spectral sign
  function is needed (`Head.TailSupport.paper_main_support_perturbation`).
  The spread case uses only that the tail score is positive.
- **R7. Low-influence tail (secs. 3.4 and 3.5).** The interpolation of
  Lemma 3.9 keeps the paper's path and constants but is proved for the
  soft min-max only. The head is fixed, its nets are chosen classically,
  the tail probability is bounded under the law of the tail rows, and the
  bound is integrated over the head by a section bound
  (`Head.SubcriticalConditional.paper_main_head_selection_section_bound`).
  The bad event is the exact min-max over the whole capped dual set and
  section (`Head.CompactEvent.paper_main_head_compact_value`), so
  the passages from nets to sets (eq:net-to-all) and from soft to hard
  extrema (eq:soft-to-hard) happen inside the event bound. Heads are
  counted as ordered lists with repetitions, at most (N + 1)^K
  (`Head.FamilyCount.paper_main_head_families_exp`).
- **R8. Constant spectral cutoff (sec. 4.1, eq:epsd, eq:split-def).** The
  paper splits a witness at eps_d = d^(-1/4), so the head has rank at most
  sqrt(d) and the bulk has Tr B^3 -> 0, which makes the universality error
  o(1). The formal proof splits at a constant eps0 = eps/2
  (`Orientation.Spectral.paper_main_orientation_spectral_decomposition`),
  so the head rank is at most a constant rmax >= 1/eps0^2
  (`Orientation.Family.paper_main_orientation_rank_bound`), and the
  bulk satisfies only |B|_op <= eps. The universality error
  2 eta + 2 C eps is then made small by choosing eps after C = C(beta, eta)
  (`Unsat.SupercriticalParameters.paper_main_unsat_cutoff_parameters`), not by
  letting d grow. No Schatten-3 bound appears. The bounded rank is also
  what makes the orientation net of R9 small enough.
- **R9. Nets, pinching and finite priors (secs. 4.1 and 4.4).** The paper
  takes a union over a net I_d of tuples (r, U, H, b) with entropy
  O(d^(3/2)), rounds a witness to the net by a rotation O close to the
  identity (Lemma 4.6), conditions on the head coordinates of U, and
  applies Prop. 4.3 and McDiarmid's inequality for each tuple. The formal
  proof takes a net of orientations only, with entropy O(d)
  (`Orientation.Family.paper_main_orientation_family_uniform`). A
  witness is pinched by the projector of the nearest orientation (Lemma
  4.6 row). For each orientation, the whole sample is rotated, which keeps
  its Gaussian law (`Orientation.Rotation.paper_main_orientation_rotate_law`),
  and one joint delta-net of all admissible (H, b, B), fixed before the
  data (`Orientation.Prior.paper_main_orientation_prior`), enters a
  soft minimum at a fixed inverse temperature. The entropy of that prior,
  of order d^2, is paid as ln s/(beta N), a small constant, instead of in a
  union bound. Nothing is conditioned on the head: the hybrid mean is
  taken over heads and bulks together
  (`Hybrid.FiniteMean.paper_main_hybrid_finite_goe_mean`), and the
  head small-ball failure enters only through exp(-c d^2) in that mean.
- **R10. Bulk universality (sec. 4.2).** In place of the free-entropy
  interpolation of Bandeira and Maillard: (1) whole rows are replaced one
  at a time (`Loss.Replacement.paper_main_loss_array_comparison`);
  (2) for one row, the change of the soft minimum is -ln A/beta, with A a
  Gibbs average of exp(-beta loss) (`Loss.Gibbs.paper_main_gibbs_row_increment`);
  (3) -ln A is approximated uniformly by a polynomial in 1 - A, whose
  powers are averages over Gibbs replicas of products of loss factors
  (`Loss.Replica.paper_main_loss_row_poly_uniform`); (4) each
  product, evaluated at the quadratic forms y^T B_j y - Tr B_j of one
  Gaussian row, is compared with the same product at Gaussian linear forms
  of the same covariance, along the path sqrt(t) Q + sqrt(1 - t) L, with
  first-order Gaussian integration by parts
  (`Projection.Comparison.paper_main_projection_smooth_comparison`).
  The error is 2 eta + C(beta, eta) eps |B|_F with eps = max |B_j|_op,
  for every N, all dimensions, all offsets and every finite prior. Only
  two bounded derivatives of the test function are used. The paper's own
  second-chaos Lindeberg principle (Lemma 3.9) is not used here, nor is the
  library's Lindeberg file (`library/probability/lindeberg.v`).
- **R11. Hybrid gap (sec. 4.3).** Lemma 4.10 is proved with a net of the
  parameters (H, b), a Markov truncation of |g g^T - I|_F and binomial
  tails over the rows (`Head.SmallBallUniform.paper_main_head_small_ball_uniform`),
  instead of Sauer's lemma and the VC inequality; it needs
  n >= 306432 (r + 1)^3, where the paper needs r^2 log n = o(n). The fourth
  moment is computed. Lemma 4.11 does not use the projection P_J: for a
  fixed head, an orthonormal basis of the complement of the head range
  (`Projected.BulkComplement.paper_main_projected_complement_mx`)
  and Bessel's inequality bound the residual from below for every head
  coefficient, so the small-ball event is not needed in the bulk bound.
  Deletion sets are counted with exp(k (1 + ln(n/k))) instead of
  exp(n H_2(delta)). One event on head and bulk together is bounded; the
  conditional form eq:hybrid-conditional is not stated.
- **R12. Concentration in the unsatisfiable phase (sec. 4.4).** McDiarmid's
  inequality, applied by the paper to the bulk rows conditionally on the
  head, is replaced by the formal bounded-difference inequality applied to
  full rows (head and bulk), with oscillation 1/N per row:
  P(Z_data <= E Z_data - t) <= exp(-N t^2/2)
  (`Hybrid.FiniteTail.paper_main_hybrid_finite_data_lower_tail`).

## (c) Hypotheses that the formal lemmas add

Each item says whether the paper's use satisfies the hypothesis. In every
case it does; none of these is a gap in the paper's argument, but several
are steps the paper does not write.

- **Integrability and regularity (Lebesgue integral).** Expectations are
  Lebesgue integrals, so integrability is absolute and must be proved for
  every integrand. As the header of `GaussianDefinitions.v` explains, an
  identity that integrates the highest derivative of f, such as Stein's
  identity E[f'] = E[x f], then needs the integrability of that integrand
  as a hypothesis: f(x) = sin(exp(x^2)) is bounded with a continuous
  derivative, but f'(x) exp(-x^2/2) is not absolutely integrable. The
  formal proof meets this with polynomial bounds. It works with "regular"
  functions, continuous with a polynomial bound
  (`Data.FeatureMomentsCoordinates.pmdf_regular`), and transports
  their iterated Gaussian expectations to the product law
  (`Data.FeatureMoments.pmdf_actual`). The second-order Stein
  identity of Lemma 3.10 assumes differentiability, a continuous second
  derivative and polynomial bounds on f and its first two derivatives
  (`Gaussian.VectorStein.gaussian_vector_second_stein`). The comparison of
  section 4.2 assumes test functions with two bounded continuous
  derivatives, and the concentration inequalities assume continuous
  bounded functions. The paper's uses satisfy all of these: polynomials,
  the soft min-max (smooth, with bounded derivatives), and the bounded
  smooth loss 1 - exp(-t^2). The paper covers them in one sentence (l.1274)
  or not at all.
- **Measurability.** Every event and every statistic must be measurable,
  including infima and suprema over uncountable sets: the fit event, the
  width of a data-dependent section, the min-max of section 3.5, the
  infimum over (J, v, c) in Lemma 4.11. The formal proof shows it through
  countable nets, rational approximation and continuity
  (`Measurability.Fit.pm_fit_event_measurable`,
  `Head.SectionWidthLaw.paper_main_head_section_width_measurable`,
  `Projected.BulkConditional.paper_main_projected_bad_measurable`).
  The paper discusses only the measurable selection of section 3.5.
  Satisfied.
- **Finite index sets.** Gordon's inequality is proved for finite families
  only, and the nets of section 3.5 must lie inside the sets they
  approximate. The paper uses compact sets. Satisfied, since nets exist.
- **Nonemptiness.** Head sections, priors and capped dual sets must be
  nonempty. The paper uses the convention that an infimum over an empty
  set is +infinity and omits empty C_U(H); the formal proof takes the
  support of an empty set to be 0 and derives nonemptiness of sections
  from positive width. Satisfied.
- **Explicit ranges of d.** The paper says "for all large d". The formal
  thresholds are explicit and sometimes very large: d >= 2^9600 for the
  rate of the upper feature edge
  (`SquareFree.EdgeUpperLimit.paper_main_squarefree_offdiag_rate`),
  d0 of order 10^15 for the hybrid gap near gamma = 1/4 (computed from the
  formal threshold), d > 1734/eps for
  Lemma 2.2, d >= rmax^2 + 1 for the head rank. These do not matter for
  the asymptotic statement.
- **Density windows.** The lower feature edge needs 4 N <= d^2 and
  d^2 <= c_1 N; the upper edge needs N <= d^2 and a density eventually at
  least c > 0; the hybrid gap needs |N - gamma d^2| <= eta d^2. The
  padded and trimmed counts N = floor(beta d^2), with beta in (0, 1/4) or
  (1/4, 1/2), satisfy them.
- **Head size.** r <= sqrt(d) + 1, r <= rmax, and n >= 306432 (r + 1)^3
  for the head small ball. Satisfied for large d.
- **Matrices.** Coefficient matrices must be symmetric for the Stein
  identities; operator-norm bounds are stated as bounds on bilinear forms
  (`Cone.ConditionOperator.paper_main_cone_opnorm_le`); the cone
  K_k is written in Loewner form, lam I <= S <= k lam I for some lam > 0.
  Satisfied.
- **Choice.** Several exceptional events are chosen for each d separately,
  with Hilbert's epsilon or classical choice
  (`Head.DataLog.paper_main_head_data_log_probability`); no
  measurability in d is needed. These axioms are among the eight of
  `check/assumptions.expected`.
- **Feature bounds as hypotheses.** The satisfiable assembly takes the two
  feature edges as hypotheses outside vanishing events
  (`Conditioned.SpectralReduction.paper_main_subcritical_spectral_reduction`),
  and the tail argument takes the operator bound L sqrt(d) and the
  coordinate bound d^(1/4) as hypotheses on the sample. They are
  discharged at N = floor(beta d^2).

## (d) Formal results near the top of the tree with no paper counterpart

Depth is the distance from the two theorems in the dependency graph; size
is the number of declarations each one uses, directly or not.

| Formal result | Depth | Size | What it does |
|---|---|---|---|
| `Measurability.Fit.pm_fit_event_measurable`, `Measurability.Conditioned.pm_conditioned_event_measurable`, `Measurability.Balanced.pm_balanced_pd_event_measurable` | 1 | 76 to 86 | Measurability of the three events, asserted by the formal statement. Each event is a countable union or intersection of sets defined by polynomial inequalities over rational matrices or weights; a cluster-point argument gives the set equality. |
| `Gaussian.Spanning.paper_main_gaussian_spanning_ae` | 4 | 39 | The sample spans R^d almost surely when n >= d: the determinant of the first d points is a nonzero polynomial, and its zero set is null for the Gaussian law. |
| `Fixed.Density.paper_main_conditioned_from_fixed`, `Fixed.Density.paper_main_unsat_from_fixed`, `Sampling.paper_main_drop_points_law` | 1 to 5 | 14 to 41 | The padding and trimming of the paper (one sentence each), as statements on probabilities: the law of a sample after deleting points is the law of the smaller sample. |
| `Orientation.Rotation.paper_main_orientation_rotate_law` | 5 | 228 | Rotating every point by an orthogonal matrix keeps the product Gaussian law. The paper uses it without comment in eq:decompose. |
| `Feature.UpperProbability.paper_main_feature_upper_event_measurable`, `Hybrid.FiniteArray.paper_main_hybrid_finite_data_regular` | 5 | 341 to 379 | Measurability of the exceptional events and regularity (continuity, polynomial bounds) of the soft losses, needed to state and integrate them. |
| `Loss.ExpectedGap.paper_main_loss_expected_gap` | 6 | 281 | E F >= e (1 - p) when F >= 0 and F >= e outside an event of probability p: the step from a high-probability bound to a mean. |
| `Loss.ConcentrationSoftMin.paper_main_softmin_lower_tail` | 6 | 399 | The bounded-difference inequality for the soft minimum, uniform in the prior; it replaces the cited McDiarmid inequality. |
| `Head.SubcriticalEvent.paper_main_head_subcritical_bad_measurable`, `Head.SectionWidthLaw.paper_main_head_section_width_measurable` | 11 to 13 | 640 to 693 | Measurability of the bad event of section 3.5 and of the section width as a function of the head (the width is a Tonelli integral). |
| `Head.SubcriticalConditional.paper_main_head_selection_section_bound`, `Head.Law.paper_main_split_coordinates_section_bound` | 11 to 12 | 16 to 63 | The formal form of "condition on the head": a bound on every section of a measurable joint event bounds the event. |
| `Gaussian.LawBridge.gaussian_iterated_expectation_gauss` | 15 | 137 | The bridge that lets the library's Gaussian measure on row vectors act on the list-based law of the frozen definitions. |

The largest formal subtrees without a paper proof are re-proofs of results
the paper cites, listed in (a): the moment method for the feature edge
(about 1,300 declarations below `Column.RemainderProbability.paper_main_column_remainder_probability`
and 860 below `SquareFree.LowerProbabilityTrace.paper_main_squarefree_trace_rate`),
and the universality of section 4.2 (about 1,000 declarations below
`Hybrid.FiniteMean.paper_main_hybrid_finite_mean_comparison`).

## (e) Gaussian-specific and distribution-free parts

The paper is written for Gaussian data, and so is the formal proof. Three
kinds of Gaussian use must be told apart: the law of the data x_i, the law
of the Gaussian surrogate (GOE rows, the hybrid bulk), and the auxiliary
Gaussian Z that defines widths. The surrogate and Z are Gaussian by
construction and would stay Gaussian for non-Gaussian data, although the
covariance of the surrogate would have to match that of the data (first
row of the last table below).

**Distribution-free** (deterministic, or using only that the rows are
independent and identically distributed):
- convex duality: the Gordan-Stiemke alternative of Lemma 2.12 and the
  separation of Lemma 3.2 (`Geometry.*`, `Cone.Kernel*`,
  `Conditioned.SupportFit`);
- cone geometry: the PSD projection and Moreau's decomposition, the
  condition cones (`Cone.Projection`, `Cone.Condition*`);
- the spectral theorem and operator norms (`GaussianAnalysis.matrix.real_spectral`,
  `GaussianAnalysis.matrix.opnorm`), the spectral split and pinching
  (`Orientation.Spectral`, `Projection.Pinching`,
  `Pinching.*`);
- nets and counting (`GaussianAnalysis.matrix.nets`, `Gordon.Entropy`,
  `Orientation.Net`, `Head.FamilyCount`, the walk counting
  of the feature edge);
- the head-tail decomposition (Lemma 3.5) and the algebra of the exact
  correction (Lemma 3.8, `Geometry.Head*`);
- the soft extrema and their third derivatives in the projective norm
  (Lemma 3.12, `Soft.Extrema`, `Tensor.*`, `Chaos.CubicMassBounds`), the contraction bound of
  Lemma 3.10 (pointwise in x);
- the bounded-difference inequality, row replacement, the replica
  expansion (`Loss.Concentration*`, `Loss.Replacement`,
  `Loss.Gibbs`, `Loss.Replica`), Paley-Zygmund and the
  counting of the head small ball, the risk bounds of the hybrid gap
  (`Hybrid.Loss`, `Hybrid.Residual`). These are stated for
  the iterated Gaussian expectation but use only the product structure.
- almost sure spanning, which needs only a law with a density.

**Gaussian law of the surrogate or of the auxiliary Z only** (these
arguments would survive non-Gaussian data, up to the covariance of the
surrogate): the widths of Lemmas 2.1 and 2.2; Gordon's
inequality and escape through a mesh (library `comparison/gordon.v`,
`comparison/escape.v`); the norms of Gaussian matrices (Lemma 2.5); the
Stein identity for the GOE rows (`Joint.SectionStein.joint_goe_section_stein`);
the rotation invariance of the hybrid bulk array
(`Projected.BulkLaw.paper_main_projected_law`).

**Gaussian law of the data**, by component:

| Component | Paper | What is Gaussian | Formal modules |
|---|---|---|---|
| Chaos-to-GOE transfer, satisfiable phase | Lemmas 3.9, 3.10 | Second-order Stein identity for x; the GOE surrogate matches the covariance of the chaos rows. For independent coordinates with fourth moment m_4, Var(x^T A x) = 2 \|A\|_F^2 + (m_4 - 3) sum_a A_aa^2, so the GOE surrogate is the right one only when m_4 = 3. | `Gaussian.VectorStein`, `Quadratic.EntryStein`, `Quadratic.TimeStein`, `Multirow.*`, `Soft.Comparison` |
| Concentration of the clipped functional | Lemma 3.15 | Dimension-free Gaussian concentration of a Lipschitz function of all n d coordinates. The soft min-max is not convex, so Talagrand's convex-distance inequality would not replace it directly. | `Data.SoftConcentration`, `Gaussian.LipschitzConcentration` |
| Data estimates | Lemma 2.10, eq:radius | Chi-square and linear Gaussian tails (sub-Gaussian tails would do); the coherence bound uses the law of <x_i, x_j> given x_i, that is rotation invariance. | `Gaussian.DataRadius*`, `Data.CoherenceLimit`, `Data.SampleTail`, `Head.DataLog` |
| Residuals of the head correction | Lemma 2.11 in Prop. 3.3 | The Hanson-Wright proof uses diagonalization and rotation invariance. By our reading of the proof, the Markov step costs a factor N d^4, so a one-row tail o(d^(-6)) at the threshold d^(-1/4) suffices, and a high moment bound on x^T P x - Tr P would do. | `Gaussian.QuadraticTail`, `Gaussian.Residual*` |
| Feature edge | Lemmas 2.6, 2.7 | Exact Gaussian moments of monomials, including the vanishing of odd moments, and explicit fourth and eighth moments. The paper cites Kogan, Nandy and Huang, whose theorem covers centered coordinates with moment growth; the formal proof is more Gaussian-specific here, and a non-Gaussian version would have to redo the walk count for odd multiplicities. | `SquareFree.Walk*`, `Column.*`, `DiagonalBlock.*` |
| Orientations and head/bulk independence | eq:decompose, secs. 4.1, 4.4 | Rotation invariance of the sample: it reduces every orientation to fixed coordinates and makes the head and bulk parts of a point independent standard Gaussians. This is the main obstacle in the unsatisfiable phase for non-Gaussian data. | `Orientation.Rotation`, `Head.Law` |
| Bulk universality | Props. 4.3, 4.8 | First-order Gaussian integration by parts for the bulk vector and Gaussian fourth moments of quadratic forms (the surrogate covariance 2 <A, B> again needs m_4 = 3). It is the only use of the data law in that comparison. | `Projection.*`, `Loss.ReplicaComparison` |
| Head small ball | Lemma 4.10 | E Y^2 = 2 \|H\|_F^2 + b^2 and E Y^4 <= 19 sigma^4 by rotation and explicit moments, and E \|g g^T - I\|_F^2 = r (r + 1). Any law with a small-ball bound for quadratic forms would do. | `Head.SmallBall*` |

## (f) Possible errors and gaps

In the paper (none affects the conclusion):
- l.2061, eq:head-dominating-bound: the bulk term is written
  C_0 sqrt(n) |B|_F^2; Lemma 4.11 gives C_0 sqrt(n) |B|_F, which is what
  the proof uses at l.2229 (eq:case-head) and what the formal proof uses.
  A typo.
- The set I of large residuals is defined with |u_i| >= 1 at l.1751 and
  with |u_i| > 1 at l.2044 and l.2239. Harmless.
- Lemma 2.1 is stated for d >= 1, but sqrt(D_d/2 - 1) is not defined for
  d = 1 (D_1/2 - 1 = -1/2). The formal statement holds for every d because
  Stdlib's sqrt is 0 on negative numbers.
- Lemma 4.12 claims P(E_U^c) <= exp(-c d^2) uniformly for 0 <= r <= k_d,
  but Lemma 4.10 is stated for 1 <= r <= k_d; the case r = 0 is handled
  only inside the proof of Prop. 4.4 ("after decreasing a_0").
- Prop. 4.3 is stated along one sequence n = n(m), but Lemma 4.12 applies
  it uniformly over r <= k_d, so several values of n occur for one m.
  Uniformity follows by taking the worst n for each m; the paper does not
  say so.
- Prop. 4.8 is only sketched, as a modification of a theorem of Bandeira
  and Maillard that the paper does not reproduce. The formal proof gives a
  complete proof of a statement with the same role (R10).
- The paper does not discuss the measurability of the infima and suprema
  over uncountable sets (E_C, E_(U,H,b), the events of Props. 4.4 and 4.5,
  the widths of data-dependent sections). They are measurable, and the
  formal proof proves the instances it uses.
- Typos: eq:Ri-bound has unbalanced bars; eq:radial-weight writes
  M_3(F({Z_i(t)})) although M_3(F) is a supremum; l.273 calls Lemma 3.9 a
  proposition.
- The rate e^(-c d^2) claimed for the tail events (l.868, l.1368, eq:conc)
  is correct for the paper's radial clipping; the formal proof uses
  another clipping and a weaker rate (R4). Not an error.

In the formal proof: no gap was found; the kernel checks it. Cleanup items
only:
- Module headers that still describe declarations deleted because the
  main theorem does not use them: `Projected.BulkEscape` (it names
  `paper_main_projected_escape_zero` and `paper_main_projected_psd_escape`,
  which no longer exist), `Gaussian.PsdWidthLimit` (announces the
  limit 1/2 and contains only the dimension formula),
  `Gordon.CompactMinmax` and `Gaussian.GordonTail` (describe
  a set-index min-max statistic that they no longer define). Section
  comments without declarations below them remain at the end of
  `Hybrid.FiniteMean` ("4. The data mean") and
  `Hybrid.FiniteTail`, and in `Loss.ConcentrationTail`
  ("1. Product-law forms."). The header of `Orientation.Spectral`
  still names "the checked M119 decomposition" and "the M121
  decomposition", labels from the source repository.
- The proof of the paper does not use these library theorems:
  `gordon_escape_tail`, `gauss_opnorm_mean` and `gauss_opnorm_tail` of
  `library/comparison/escape.v` (the forms of Lemmas 2.4 and 2.5 with the
  paper's sharp thresholds), `sudakov_fernique` of
  `library/comparison/slepian.v`, and `lindeberg_replacement` of
  `library/probability/lindeberg.v`. The formal proof uses weaker forms
  proved in `theories/` instead (R10, rows of Lemmas 2.4 and 2.5).
