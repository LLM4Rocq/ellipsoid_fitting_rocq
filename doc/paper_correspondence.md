# Correspondence between the paper and the formal proof

This document compares the Rocq proof in `theories/` with the informal proof
of the paper, result by result. Correctness is not in question: the kernel
checks the proof, and the statement and its definitions were reviewed
against the paper. The document records where the formal proof follows the
paper's route and where it deviates, and how. It also lists which results
the paper cites without proof, which hypotheses the formal lemmas add, which
formal results have no counterpart in the paper, and which arguments are
specific to Gaussian data, for planning an extension of the theorem.

It reconciles two comparisons that were made independently, by agent 3
(lane C) and by agent 2 (lane B), into one table with two relation columns.
Where the two comparisons disagreed, the disagreement was decided by
checking the formal statement and the paper, and the evidence is in the
note of the row.

## What was compared

- **Paper.** T. Misiakiewicz and G. G. Wen, *The sharp SAT/UNSAT phase
  transition in random ellipsoid fitting*, arXiv:2608.10184v1. The LaTeX
  source `manuscript.tex` (2368 lines,
  `/srv/ellipsoid-fitting/papers/2608.10184v1/manuscript.tex`) was
  downloaded from https://arxiv.org/e-print/2608.10184v1 on 6 October 2026.
  Read: sections 1.2, 2, 3 and 4. Results are numbered as in the compiled
  paper (one counter per section, shared by theorems, propositions, lemmas,
  corollaries and remarks) and named by their LaTeX labels. Line numbers
  ("l.") refer to `manuscript.tex`.
- **Formal proof.** Commit `3736fa2` of `main`
  (3736fa2639a422a1f608ac964c2faea30a3dc09f, "Merge branch review/b"), the
  merge of the two comparisons. Module names are the logical names of
  `_CoqProject` after phase 3: `theories/Hybrid/Bulk.v` is `Hybrid.Bulk`,
  `library/comparison/escape.v` is `GaussianAnalysis.comparison.escape`,
  written `library:comparison.escape` below. Line numbers of a formal
  declaration, written `(File.v:line)` after its name, are the lines of the
  `.v` file at this commit. The two comparisons read the statements at the
  end of phase 3 (agent 3 on commit `2b85d8e`, checked against `2a06058`;
  agent 2 on `2a06058`). A script compared the statements of the 247 module-qualified
  declarations cited below between `2a06058` and `3736fa2`: 240 are
  identical, six library lemmas changed only the keyword `Theorem` to
  `Lemma`, and `library:gaussian.gauss_ibp.gauss_ibp2` now asks the
  measurability of the integrand instead of its continuity. Every name
  cited below exists at `3736fa2`.
- **Method of agent 3.** The commit was built with `make build` in the
  project's toolchain (Rocq 9.1.1, MathComp 2.6.0, MathComp-Analysis
  1.16.0). From the `.glob` files of that build, an adaptation of
  `scripts/unused.py` computed the dependency graph below the two theorems
  that `PaperMainResults.v` uses,
  `PaperMainFinalAssembly.paper_main_results_from_conditioned` and
  `PaperMainConditionedLimit.paper_main_conditioned_limit`: for each
  declaration, the declarations that its statement and proof name. The
  adaptation (not in the repository) reads the modules in folders and in
  `library/`, starts from these two theorems, and outputs the graph. The
  graph has 5,642 declarations in 624 modules: 602 of `theories/` and 22 of
  the 25 files of `library/` (514 declarations); outside it are
  `probability/lindeberg.v`, `comparison/gauss_shift.v` and
  `gaussian/gauss_moments.v`. For the main results the proof was read or
  skimmed as well. Some proofs were read only through their module headers
  and statements: the walk counting of the feature edge (`SquareFree.Walk*`
  modules), the measurability modules, and the interpolation machinery
  below Lemma 3.9 (`Multirow.*`, `Row.*`, `Joint.*` modules).
- **Method of agent 2.** The same build, and the block graph of
  `scripts/unused.py` (`Analysis.reach`) from the `.glob` files: a
  declaration is in the tree when its block (`Definition`, `Lemma`,
  `Theorem`, ... with its proof) is reachable from a block of the frozen
  files. At `2a06058`: 605 modules of `theories/` in `_CoqProject`, 5164
  declaration blocks, 5156 of them in the tree, in every one of the 605
  modules; the 8 blocks outside it are the function-level bridge lemmas
  `RleF`, `RltF`, `INRF`, `RmaxF`, `RminF`, `RinvF`, `RdistF`, `lnF` of
  `Analysis.RealsBridge`. The longest chain from the statement to a used
  declaration has 44 steps. The used blocks of `theories/` reference 109
  declarations of 16 library files directly (`matrix.euclidean` 20,
  `matrix.opnorm` 17, `matrix.real_spectral` 9, `matrix.nets` 4,
  `gaussian.gauss` 5, `gaussian.gauss_ibp` 5, `gaussian.measurable_matrix`
  5, `comparison.escape` 14, `comparison.chi_square` 6,
  `comparison.gauss_concentration` 4, `comparison.gauss_law` 4,
  `comparison.gordon` 4, `comparison.slepian` 4, `comparison.gauss_linear`
  3, `comparison.gauss_smoothing` 1, `probability.moments` 4); the nine
  other library files (`gauss_interpolation`, `gauss_moments`,
  `partial_derivative`, `normal_integral`, `normal_mgf`, `normal_linear`,
  `gauss_rotation`, `gauss_shift`, `probability.lindeberg`) are not
  referenced from `theories/`, which is compatible with agent 3's count of
  22 reachable files, since that count follows references inside the
  library. Every statement was checked on the proof skeleton of its module
  (the `.v` file with proofs removed); claims that rest on reading rather
  than on the build are marked "(read)".
- **Reconciliation.** The two tables cover the same 39 results and agreed
  on 27 rows. They disagreed on the relation of 12 rows (Lemmas 2.2, 2.4,
  2.7, 2.10, 3.2, 3.8, 3.10, 4.2, 4.10, 4.11 and Propositions 3.3, 3.4),
  and for Lemma 3.10 they named disjoint formal counterparts. The
  disagreements came from different grading, not different facts: agent 3
  graded worse constants, rates, missing directions and added sample
  hypotheses as weaker, and a different argument as replaced; agent 2
  graded a statement with the same conclusion as same whatever the
  constants, and used replaced when the object changed. The table below
  separates the two aspects into a statement relation and an argument
  relation, defined in the next section. Every disputed row was decided by
  printing the formal statements with `About` in a build of `3736fa2`
  (`make build`, exit code 0; 56 declarations, query file not in the
  repository) and reading the paper's lines; the note of the row records
  the evidence and the verdict, marked "Adjudication". The three rows that
  agent 3 graded "replaced, weaker" (Lemmas 2.3, 3.13 and 4.12) resolve to
  statement weaker and argument replaced. The facts of agent 3's notes were
  also verified by agent 1 (section 1 of
  `/srv/ellipsoid-fitting/reviews/review-of-agent3-by-agent1.md`), whose
  correction about Lemma 2.5 is carried in section (e).

## How to read the table

- One row per theorem, proposition, lemma and corollary of the paper, in
  the paper's order (39 rows): 1.2 to 1.4, 2.1 to 2.12, 3.1 to 3.5 and 3.8
  to 3.15, 4.1 to 4.6 and 4.8 to 4.12 (3.6, 3.7 and 4.7 are remarks, and
  the conjecture shares the counter). Remarks 3.6, 3.7 and 4.7 are
  discussed after the table. Unlabelled steps of the paper (the padding of
  section 3, the bound eq:b-bound, the spectral split of section 4, ...)
  are discussed in sections (b) and (c).
- Formal names are `Module.name`, with the file and line of the
  declaration at `3736fa2`. Unless a sentence says otherwise, every name is
  a declaration that the two theorems used by `PaperMainResults.v` depend
  on.
- **Statement relation**, comparing the formal statement with the paper's
  statement:
  - **same**: equivalent to the paper's statement up to notation. Explicit
    values for constants that the paper writes as C, c or kappa(a), and
    explicit thresholds where the paper writes "for all large d", count as
    notation.
  - **weaker**: implied by the paper's statement but not conversely: worse
    constants or rates, a missing direction or case, a special case (one
    function in place of a class of functions, one sequence in place of a
    compact range of densities), or an added hypothesis on the sample.
  - **stronger**: implies the paper's statement and says more: fewer
    hypotheses, a wider range of parameters, an extra conclusion, or an
    explicit bound for every d where the paper's statement is only
    asymptotic. Measurability conclusions, which the paper takes for
    granted, do not count.
  - **absent**: not needed by the formal proof.
  
  When the formal proof replaces the paper's argument, the counterpart may
  concern another object (a finite prior in place of a closed set, a
  pinched witness in place of a rotated one, orientations in place of
  tuples); the statement relation then compares what the formal statement
  gives at that point of the proof with what the paper's result gives
  there.
- **Argument relation**, comparing the formal proof with the paper's proof:
  - **paper's route**: the formal proof follows the proof the paper gives:
    the same construction, decomposition and intermediate claims, possibly
    with other constants or thresholds, and possibly with other proofs of
    individual steps.
  - **replaced**: the formal proof reaches the statement, or the point of
    the argument where the paper uses it, by another argument.
  
  For a result that the paper cites without proof (Lemmas 2.4, 2.5, 2.6
  and 2.11) or only sketches (Proposition 4.8), the argument relation
  compares the formal proof with the proof of the cited source: paper's
  route when the formal proof is that proof, replaced otherwise. The note
  says what the formal proof does.
- Notation: d is the dimension, n (formally N) the number of points,
  W_i = (x_i x_i^T - I)/sqrt(d), Q_x Q_x^* the Gram matrix of the quadratic
  features (formally the raw feature Gram matrix), K_k the cone of PSD
  matrices with condition number at most k (in Loewner form: lam I <= S <=
  k lam I for some lam > 0), S_F the Frobenius unit sphere, D_d = d(d+1)/2.

## Table

| Paper result | Formal counterparts | Statement | Argument | Note |
|---|---|---|---|---|
| Theorem 1.2 `thm:main` (sec. 1.2, l.141) | `PaperMainFinalAssembly.paper_main_results_from_conditioned` (PaperMainFinalAssembly.v:15), `PaperMainResults.paper_main_results` (PaperMainResults.v:15), `MainStatement.main_statement` (MainStatement.v:45), `Asymptotics.paper_main_sat_from_conditioned` (Asymptotics.v:104), `Unsat.Limit.paper_main_unsat_supercritical_limit` (Limit.v:259) | same | paper's route | Both phases. Part (a) is derived from thm:conditioned, as the paper derives it from thm:sat (l.741). The formal statement also asserts that the fit event is measurable for every n and d (`Measurability.Fit.pm_fit_event_measurable`, Fit.v:372). The density conditions are written out (`PaperMainDefinitions.paper_main_limsup_lt`, `paper_main_liminf_gt`, PaperMainDefinitions.v:140, 148). |
| Theorem 1.3 `thm:conditioned` (sec. 1.2, l.151) | `PaperMainConditionedLimit.paper_main_conditioned_limit` (PaperMainConditionedLimit.v:26), `paper_main_conditioned_fixed_limit` (PaperMainConditionedLimit.v:14), `Fixed.Density.paper_main_conditioned_from_fixed` (Density.v:173), `Conditioned.FromLower.paper_main_conditioned_from_lower` (FromLower.v:33), `paper_main_conditioned_from_lower_exists` (FromLower.v:82) | same | paper's route | Constants lambda_+ = 1/lambda_- = 2 kappa + 1 with kappa = 2 k0^2 and k0 = O((1/4 - beta)^-1) for a density beta chosen in (alpha*, 1/4) (`Conditioned.SpectralReduction.paper_main_subcritical_raw_spectral_reduction`, SpectralReduction.v:91). The paper has 4 kappa_1^2 = 16 kappa_0^2 with kappa_1 = 2 kappa_0 (l.748, l.778). Both are O((1/4 - alpha*)^-2), as in Remark 3.6; neither constant is computed. Measurability is added. |
| Corollary 1.4 `cor:alternative` (sec. 1.2, l.164) | `Balanced.Probability.paper_main_balanced_from_sat` (Probability.v:61), `Balanced.Limit.paper_main_balanced_supercritical_limit` (Limit.v:29), `Balanced.Supercritical.paper_main_balanced_from_unsat` (Supercritical.v:127), `Gaussian.Spanning.AlmostSure.paper_main_gaussian_spanning_ae` (Spanning.v:85), `Measurability.Balanced.pm_balanced_pd_event_measurable` (Balanced.v:385) | same | paper's route | Below 1/4 only the exclusion half of lem:homogeneous (ii) is used (`Geometry.Exclusion`); it needs no spanning. Above 1/4 the existence half (`Geometry.Separation.paper_main_fit_alternative`, Separation.v:381) needs the sample to span R^d; the formal proof proves that this holds almost surely when n >= d, which the paper asserts (l.173). Measurability is added. |
| Lemma 2.1 `lem:psd-width` (sec. 2.1, l.350) | `Gaussian.Width.Psd.paper_main_gaussian_psd_projection_second_moment` (PsdWidth.v:81), `paper_main_gaussian_psd_width_bounds` (PsdWidth.v:211), `Cone.Projection.paper_main_psd_moreau` (Projection.v:229) | same | paper's route | E \|Z_+\|_F^2 = D_d/2 and sqrt(D_d/2 - 1) <= w <= sqrt(D_d/2) exactly as l.353 and l.357, by Moreau's decomposition and Z = -Z in law, as in the paper. The width bounds come from the Gaussian Poincare inequality (`Gaussian.Width.SignedSupport.paper_main_gaussian_positive_square_lower`, WidthVariance.v:73; library `library:comparison.gauss_concentration.gauss_poincare_lipschitz`, gauss_concentration.v:1124) applied to the positive part of the support function (`Cone.ProjectionSupport.paper_main_psd_sphere_support_max`, ProjectionSupport.v:114), instead of the cited Proposition 10.2 of Amelunxen, Lotz, McCoy and Tropp (l.365; see (a)). The clause w = d/2 + O(1) is not stated separately. |
| Lemma 2.2 `lem:widthcone` (sec. 2.1, l.379) | `Gaussian.Width.ConditionBound.paper_main_gaussian_condition_width_lower` (ConditionWidthBound.v:83), `paper_main_gaussian_condition_width_large` (ConditionWidthBound.v:115), `Cone.Condition.paper_main_cone_shift_scaled` (Condition.v:220) | stronger | paper's route | **Adjudication** (agent 3: stronger; agent 2: same). The paper (l.380-384): for every a < 1/2 there is kappa(a) with w(K_kappa cap S_F) >= a d for all large d. `_large` (v:115): for every eps > 0 there are kappa >= 1 and K such that (1/2 - eps) d <= w(K_kappa cap S_F) for d > K, which is the paper's statement. `_lower` (v:83): for every s > 0 and every d, w(K_kappa cap S_F) >= (1/2 - s) d - 3 - 864/d with kappa = (20 + s)/s: an explicit kappa(a) and a bound for every d, which implies the paper's statement and is not implied by it. Verdict: stronger. The argument keeps the paper's candidate (Z_+ + s sqrt(d) I)/norm (l.387-389); the semicircle law, the operator-norm limit and the uniform integrability of l.390-411 are replaced by the pointwise bound on and off the event \|Z\|_op <= 20 sqrt(d), of probability at least 1 - 2 exp(-10 d) (`Gaussian.Symmetric.OperatorTail.paper_main_symmetric_gaussian_operator_good_set`, SymmetricOperatorTail.v:20; `Gaussian.Width.Condition.paper_main_gaussian_condition_point_bound`, ConditionWidth.v:151), the lower bound E \|Z_+\|_F >= d/2 - 1 of Lemma 2.1 and E (Tr Z)^2 = d (route R1). |
| Lemma 2.3 `lem:gordon` (sec. 2.2, l.424) | `Gordon.Width.paper_main_gordon_finite_width_margin` (Width.v:114), `Gordon.SoftMargin.paper_main_gordon_soft_width_margin` (SoftMargin.v:57), `Gordon.Processes.paper_main_gordon_process_comparison` (Processes.v:177), `Gaussian.Lipschitz.LowerMargin.paper_main_gaussian_lipschitz_lower_margin` (GordonTail.v:33); library `library:comparison.escape.auxT_bilT_minmax` (escape.v:409), `library:comparison.gordon.gordon` (gordon.v:648) | weaker | replaced | The paper (l.425-431): a tail bound 2 exp(-t^2/4) for the min over the unit sphere and the sup over a compact T. Formal: only an expectation bound for finite families of unit vectors, E min_y max_t z_y^T A v_t >= E max_t <h, v_t> - sqrt(N) (Width.v:114, with sqrt(N) in place of E\|g_N\|), proved by Kahane's comparison applied to a soft min-max (library `gordon`, through its bilinear instance `auxT_bilT_minmax`, the only entry point the tree references, from `Gordon.Processes`), its soft version with the entropy loss ln r/beta (SoftMargin.v:57), and nets to pass from finite families to sets (`Gordon.Nets.paper_main_gordon_net_width_error`, Nets.v:76). No tail bound, no gamma_0, no compact index set. The Lipschitz lower tail exp(-u^2/(2 L^2)) of GordonTail.v:33 is available, but the probability bound needed later comes from the concentration of the clipped data functional (route R2). Agent 3 graded "replaced, weaker": statement weaker, argument replaced. |
| Lemma 2.4 `lem:escape` (sec. 2.2, l.478) | `Gaussian.Lipschitz.EscapeTail.paper_main_gaussian_escape_sqrt_tail` (EscapeTail.v:18), `Gordon.EscapeExpectation.paper_main_gordon_escape_expectation` (EscapeExpectation.v:115); library `library:comparison.escape.gordon_escape` (escape.v:603) | weaker | paper's route | **Adjudication** (agent 3: weaker; agent 2: same). The paper (l.479-485, citing Gordon 1988): P(inf_T \|A x\| <= E\|g_s\| - w(T) - t) <= exp(-t^2/2) for a compact T. EscapeTail.v:18: for N > 0, T any nonempty set of unit vectors of R^M and u > 0, P(inf_T \|A x\| <= sqrt(N - 1) - w(T) - u) <= exp(-u^2/2). Since sqrt(N - 1) <= E\|g_N\| (eq:chi-mean, l.491), the formal event is smaller than the paper's: the formal bound follows from the paper's and not conversely, and compactness is not needed (the paper's statement for the closure of T gives the formal one). Verdict: weaker; it is what eq:gap-mean uses. The library's `gordon_escape` (escape.v:603) is the expectation form with the exact mean, E inf_T \|A x\| >= E\|g_N\| - w(T), from Gordon's comparison and nets, and `gordon_escape_tail` (escape.v:684) is the paper's statement verbatim; the tree uses the expectation form and the concentration of row 2.3, and does not reference `gordon_escape_tail`. Argument: the proof of the cited source (Gordon's comparison inequality, then Gaussian concentration). |
| Lemma 2.5 `lem:gauss-rect` (sec. 2.2, l.495) | `Gaussian.Tail.Operator.paper_main_gaussian_operator_tail` (OperatorTail.v:74), `Gaussian.Symmetric.FeatureTail.paper_main_gaussian_operator_exponential_tail` (FeatureTail.v:45); library `library:comparison.escape.gauss_opnorm_tail` (escape.v:847, not referenced by the tree) | weaker | replaced | Proved by nets, where the paper cites Vershynin (l.495-499): P(\|A\|_op > 2 B) <= 2 exp(20 ln 2 (N + M) - B^2/2) for standard entries (OperatorTail.v:74), that is \|A\|_op <= 2 sqrt(2 (20 ln 2 (N + M) + t)) outside probability 2 exp(-t), in place of sigma (sqrt(N) + sqrt(M) + t). Enough for the O(sqrt(n)) bounds that are used. The library also proves the sharp mean E\|G\|_op <= E\|g\| + E\|h\| and its tail (`gauss_opnorm_mean`, escape.v:778; `gauss_opnorm_tail`, escape.v:847) by Sudakov-Fernique, but no used block references them. Argument: a net argument in place of the comparison argument of the cited theorem. |
| Lemma 2.6 `lem:squarefree-edge` (sec. 2.3, l.521) | `SquareFree.EdgeUpperLimit.paper_main_squarefree_upper_bound` (EdgeUpperLimit.v:361), `paper_main_squarefree_upper_event_tends_to_zero` (EdgeUpperLimit.v:303), `SquareFree.LowerProbability.paper_main_squarefree_lower_probability` (LowerProbability.v:36), `SquareFree.Coercivity.paper_main_squarefree_coercivity` (Coercivity.v:141), `paper_main_squarefree_coercivity_generic` (Coercivity.v:118) | weaker | replaced | Bounds, not the limits (1 -+ sqrt(2 rho_*))^2 of l.525-529: V V^T <= 106 d^2 I with probability tending to one for 0 < N <= d^2 (EdgeUpperLimit.v:361), and the lower edge only through the full raw Gram matrix, Q Q^* >= (d^2/128) I, under 4 N <= d^2 and d^2 <= c_1 N (LowerProbability.v:36-39), that is for densities in [c, 1/4] (the paper: any compact K subset (0, 1/2)). Both are self-contained: proved by moment methods instead of citing Kogan, Nandy and Huang (l.543; see (a) and route R3). |
| Lemma 2.7 `lem:diagonal-feature-block` (sec. 2.3, l.564) | `Feature.DiagonalLimit.paper_main_diag_block_tends_to_zero` (Limit.v:209), `paper_main_diag_trace_event_bound` (Limit.v:63), `paper_main_diag_trace_event_markov` (Limit.v:85), `Feature.DiagonalMoment.paper_main_diag_trace_moment` (Moment.v:868) | stronger | replaced | **Adjudication** (agent 3: replaced; agent 2: same). The paper (l.566-570): under the assumptions of Lemma 2.6 (n/p^2 in a compact K subset (0, 1/2)), P(\|D\|_op^2 <= C_K n) -> 1 uniformly over K, by truncation and matrix Bernstein (l.574-575, l.585). Formal: D^T D <= 3 N I and D D^T <= 3 N I outside the event tr((D^T D - 2 N I)^4) > N^4 (Limit.v:63, 36-40), whose probability is at most (N (2^21 d^4 + 16 d) + 3 N (N - 1) d (4 d + 52)^2)/N^4 (Limit.v:85, from the fourth trace moment Moment.v:868 and Markov's inequality), hence tends to 0 for every sequence N(d) whose density is eventually at least c > 0 (Limit.v:209). This implies the paper's statement: along n/p^2 in K the density is at least min K, the bound is explicit and uniform in n >= c d^2, and the constant is 3. No upper bound on the density and no compactness is needed. Verdict: stronger. Argument replaced: a fourth trace moment and Markov's inequality in place of truncation and matrix Bernstein; no truncation. |
| Proposition 2.8 `prop:feature-edge` (sec. 2.3, l.594) | lower edge as Lemma 2.6 and `Fixed.LowerProbability.paper_main_fixed_lower_probability` (LowerProbability.v:40); upper edge `Feature.UpperProbability.paper_main_feature_upper_edge` (UpperProbability.v:54), `paper_main_feature_upper_event_bound` (UpperProbability.v:23), `Feature.GramBlocks.paper_main_feature_gram_blocks` (GramBlocks.v:118); Gaussian map `Gaussian.Symmetric.PublicFeature.paper_main_public_gaussian_feature_exceptional_event` (PublicFeature.v:40), `Gaussian.Symmetric.ForwardConstant.paper_main_gaussian_forward_threshold` (Forward.v:27) | weaker | paper's route | (d^2/128) I <= Q Q^* at N = floor(beta d^2) with beta < 1/4 (LowerProbability.v:40), and Q Q^* <= (3 N + 106 d^2) I <= 109 d^2 I for N <= d^2 with probability tending to one (UpperProbability.v:23, 54), as l.597 for every density at most 1. Each holds for one sequence N(d), not uniformly over a compact set of densities, and the lower edge only for n/p^2 <= 1/4 (row 2.6). The Gaussian map is bounded by C(rho) sqrt(N), C(rho) = 4 sqrt(20 ln 2 (1 + 2/rho) + 1), with probability at least 1 - 2 exp(-N/2) (PublicFeature.v:40 at t = N/2, Forward.v:27), with the net constant of row 2.5. Argument: the paper's combination of Lemmas 2.5, 2.6 and 2.7 (l.600-616), with Q Q^* = D D^T + V V^T (GramBlocks.v:118, the paper's l.519). |
| Corollary 2.9 `cor:feature-sat` (sec. 2.3, l.624) | `Feature.SpectralBridge.paper_main_raw_feature_coercive` (SpectralBridge.v:57), `paper_main_raw_feature_upper` (SpectralBridge.v:75), `paper_main_raw_feature_operator` (SpectralBridge.v:91), `Conditioned.SpectralReduction.paper_main_subcritical_raw_spectral_reduction` (SpectralReduction.v:91) | weaker | paper's route | The normalization W_i = Q_i/sqrt(d) gives W W^* >= (d/128) I and \|W^* y\|_F <= sqrt(109) sqrt(d) \|y\| from the raw bounds (SpectralBridge.v:57, 75, 91), that is c d I <= W W^* <= C d I with c = 1/128 and C = 109, only for densities below 1/4 (the paper: below 1/2, l.624-634). That is the range the satisfiable phase uses. |
| Lemma 2.10 `lem:data` (sec. 2.4, l.636) | radius `Gaussian.Sample.Radius.paper_main_data_radius_good` (DataRadius.v:217), `paper_main_data_radius_probability` (DataRadius.v:128); coordinates `Data.SampleTail.paper_main_data_coordinate_tail` (SampleTail.v:109); coherence `Data.CoherenceLimit.paper_main_data_coherence_log_good` (CoherenceLimit.v:104), `paper_main_data_coherence_log_tail` (CoherenceLimit.v:45); sparse norms `Head.DataLog.paper_main_head_data_log_event` (DataLog.v:28), `paper_main_head_data_log_probability` (DataLog.v:77) | stronger | paper's route | **Adjudication** (agent 3: weaker; agent 2: same). The paper (l.637-650): for c_1 d^2 <= n <= C_1 d^2, with probability tending to one, max \|x_i\|_2 <= 2 sqrt(d) (eq:radius), max x_ia^2 <= C log d (eq:coord-max), max \|<W_i, W_j>\| <= C log d (eq:coherence) and max over \|J\| <= K_d of \|X_J\|_op^2 <= C d (log d)^2 (eq:sparse-norms). Formal: \|x_i\|^2 <= 4 d for all i outside an event of probability at most N exp(-d/2) (DataRadius.v:217, 128); P(some \|x_ia\| >= u) <= 2 N d exp(-u^2/2) for every u > 0 (SampleTail.v:109); on the radius event, \|<W_i, W_j>\| <= 73 ln d for all i <> j outside an event of probability at most 2 N^2/d^8 (CoherenceLimit.v:104, 45); for N <= C d^2, X_J X_J^T <= L d (ln d)^2 I for every head of at most K d ln d rows outside an event of probability at most 2/d (DataLog.v:28, by the net bound of row 2.5 applied to the data, `Data.HeadOperatorUniform`). The coordinate tail at u = sqrt(C ln d) gives eq:coord-max with probability at least 1 - 2 N d^(1 - C/2) -> 1 for C > 6; the tree does not state it in this form and uses the tail at u = d^(1/4) instead (`Clipping.Limits.paper_main_coordinate_clipping_tends_to_zero`, Limits.v:75; route R4). The four formal statements imply the paper's lemma, with explicit tails, and the lower bound c_1 d^2 <= n is not needed; the hypothesis N <= C d^2 of DataLog.v:28 is the paper's own upper bound. Verdict: stronger. Argument: the paper's (Gaussian tails, union bounds, the net bound for the sparse norms). |
| Lemma 2.11 `lem:hw` (sec. 2.4, l.660) | `Gaussian.Orthogonal.HansonWright.paper_main_gaussian_quadratic_tail` (QuadraticTail.v:57), `Gaussian.Sample.ResidualTail.paper_main_gaussian_residual_tail` (Residual.v:84), `Gaussian.Orthogonal.Tail.paper_main_gaussian_orthogonal_square_two_sided_tail` (OrthogonalTail.v:36); library `library:comparison.chi_square.gauss_centered_chi2_abs_tail` (chi_square.v:351) | same | replaced | Gaussian case, as the paper's statement (l.661): P(\|x^T B x - Tr B\| >= u) <= 2 exp(-u^2/(4 \|B\|_F^2 + 4 b u)) for b >= \|B\|_op, which is the paper's form with c = 1/8. Proved by orthogonal diagonalization, rotation invariance and a chi-square Chernoff bound, not by the cited Rudelson and Vershynin (l.660). Used only for the residuals r_i of prop:heads. |
| Lemma 2.12 `lem:homogeneous` (sec. 2.5, l.677) | (i) `Geometry.Homogeneous.paper_main_homogeneous_kernel` (Homogeneous.v:132), `paper_main_homogeneous_witness` (Homogeneous.v:162); (ii) `Geometry.Separation.paper_main_homogeneous_alternative` (Separation.v:368), `paper_main_homogeneous_existence` (Separation.v:332), `paper_main_fit_alternative` (Separation.v:381), `Geometry.Exclusion.paper_main_fit_balanced_exclusive` (Exclusion.v:58) | same | paper's route | (i): for d > 0 and a spanning sample, a fit exists iff some nonzero S >= 0 has all x_i^T S x_i equal (Homogeneous.v:132), and this iff some S >= 0 with \|S\|_F = 1 and real b has x_i^T S x_i - Tr S = b for all i (Homogeneous.v:162, no spanning needed). (ii): one alternative holds for every sample (Separation.v:368) and not both (Exclusion.v:58); the exclusion half is proved without the spanning hypothesis, and the cases d = 0 and n = 0 are treated. The paper's nearest-point argument (l.706-715), written as the minimization of \|D_X(S)\|^2 over {S >= 0, Tr S = 1}. |
| Theorem 3.1 `thm:sat` (sec. 3, l.743) | `PaperMainConditionedLimit.paper_main_conditioned_limit` (PaperMainConditionedLimit.v:26), `paper_main_conditioned_fixed_limit` (PaperMainConditionedLimit.v:14), `Conditioned.FromLower.paper_main_conditioned_from_lower` (FromLower.v:33), `Conditioned.SpectralReduction.paper_main_subcritical_spectral_reduction` (SpectralReduction.v:56), `Head.SubcriticalFit.paper_main_head_subcritical_fit_exception` (SubcriticalFit.v:34), `Cone.HeadTailFit.paper_main_cone_head_tail_conditioned_fit` (HeadTailFit.v:61) | same | paper's route | Same conclusion at N = floor(beta d^2), beta < 1/4, with the constants (2 kappa + 1)^(+-1), kappa = 2 k0^2 (the paper: (4 kappa_1^2)^(+-1), l.923-924; row 1.3). The padding to n = floor(alpha d^2) (l.752-757) is `Fixed.Density.paper_main_eventual_padding` (Density.v:124) with the monotonicity `paper_main_conditioned_probability_antitone` (Density.v:78) from `Gaussian.Sample.Deletion`. Same assembly as l.889-925: convex separation, head-tail decomposition, prop:heads, prop:lowinf, tiny-tail case; the steps differ in detail (routes R5 and R6). |
| Lemma 3.2 `lem:convex-separation` (sec. 3.1, l.792) | `Conditioned.SupportFit.paper_main_box_support_conditioned_fit` (SupportFit.v:128), `paper_main_cone_kernel_conditioned_fit` (SupportFit.v:37), `Cone.Kernel.paper_main_cone_kernel_exists_support` (Kernel.v:217), `paper_main_cone_kernel_exists` (Kernel.v:141), `Cone.KernelSlice.paper_main_cone_kernel_slice_compact` (KernelSlice.v:123) | weaker | paper's route | **Adjudication** (agent 3: weaker; agent 2: replaced). The paper (l.793-802): with K = W(B) for the box B and h(y) = sup_{S in B} <W^* y, S>, 0 in K iff h >= 0 on the unit sphere; h > 0 on the unit sphere is sufficient, and is equivalent to 0 in int K. Proof (l.805-812): the point k_0 of K closest to the origin and differentiation along segments. Formal: SupportFit.v:128 says that if for every unit y some S with lo I <= S <= hi I has positive support score sum_i y_i <W_i, S> > 0, then the conditioned event holds with the constants (hi/lo)^(-+1); this is the sufficient direction of the lemma composed with the scaling of l.922-924 (the paper's box [1/(2 kappa_1), 2 kappa_1] gives hi/lo = 4 kappa_1^2). Underneath, Kernel.v:217 and 141: if every unit y has positive support on the cone sphere K_kappa cap S_F (`Geometry.HeadWidth.paper_main_head_cone_sphere`, HeadWidth.v:35), some P on the cone sphere is orthogonal to every W_i, proved by minimizing sum_i <W_i, S>^2 on the compact trace-one slice of the cone (KernelSlice.v:123) and differentiating along segments: the paper's nearest-point argument, applied to the slice instead of the box. The "only if" direction and the characterization of the interior are not proved; the paper does not use them. Verdict: statement weaker (one direction); argument paper's route (both tables had called it replaced). |
| Proposition 3.3 `prop:heads` (sec. 3.1, l.834; proof sec. 3.2) | `Head.RegularProbability.paper_main_head_width_coercive_probability_uniform` (RegularProbability.v:161), `paper_main_head_width_coercive_probability_fixed` (RegularProbability.v:75), `Head.WidthProbability.paper_main_head_width_regular_probability_fixed` (WidthProbability.v:35), `Head.WidthRegular.paper_main_head_width_regular_event_fixed` (WidthRegular.v:146), `paper_main_head_width_regular_transfer` (WidthRegular.v:56), `Head.WidthActual.paper_main_head_width_actual_selected` (WidthActual.v:79) | weaker | paper's route | **Adjudication** (agent 3: weaker; agent 2: same). The paper (l.835-850): with probability tending to one, simultaneously for all \|J\| <= K_d, w(K_kappa_1 cap ker W_J cap S_F) >= w(K_kappa_0 cap S_F) - o(d) >= (sqrt(alpha) + 3 eta) d with kappa_1 = 2 kappa_0, and the sections D_J are nonempty with the box eq:DJ-box. Formal (RegularProbability.v:161): for every eps > 0 there is kappa >= 1 such that for every N(d) <= C d^2, every K and every c > 0, outside an event of probability tending to 0, if the Gram matrix of all N features is coercive with constant c d, then every head of at most K d ln d rows has section width at least (1/2 - eps) d for the cone K_kappa; the proof takes kappa = 2 k0^2 with k0 from row 2.2 at eps/2 (RegularProbability.v:75). The transfer inequality w(section) >= w(K_k0 cap S_F) - eps d is WidthRegular.v:56, with the residual event and a measurable approximate maximizer as hypotheses; WidthActual.v:79 is its deterministic form with loss (eps + 2 eta) d + 1 + 1/d^2. Differences: the coercivity of the Gram matrix (row 2.9) is a hypothesis on the sample, discharged in `Conditioned.SpectralReduction` for alpha < 1/4; the cone is K_(2 k0^2) instead of K_(2 kappa_0); the loss is eps d for each eps, with an event depending on eps, instead of one o(d); the measurable maximizer of l.962-964 is replaced by an approximate one over a finite net (route R5). Verdict: weaker (an added hypothesis on the sample and a larger cone). Argument: the paper's exact correction through the inverse feature Gram matrix (l.851-854), with the modifications of R5. |
| Proposition 3.4 `prop:lowinf` (sec. 3.1, l.858; proof secs. 3.3-3.5) | `Head.SubcriticalProbability.paper_main_head_subcritical_probability` (SubcriticalProbability.v:36), `Head.SubcriticalFixed.paper_main_head_subcritical_fixed_event` (SubcriticalFixed.v:53), `paper_main_head_list_positive` (SubcriticalFixed.v:42), `Head.SubcriticalFamily.paper_main_head_subcritical_family_event` (SubcriticalFamily.v:29), `Head.SubcriticalGood.paper_main_head_subcritical_selected_good` (SubcriticalGood.v:35), `Head.SubcriticalEvent.paper_main_head_subcritical_bad` (SubcriticalEvent.v:34) | weaker | paper's route | **Adjudication** (agent 3: weaker; agent 2: same). The paper (l.859-868): fixed theta, c_* > 0 depending on alpha such that, with probability tending to one, for every \|J\| <= K_d satisfying eq:head-width, the infimum over unit z supported off J with \|z\|_inf <= theta/sqrt(d) of sup_{S in D_J} sum_i z_i <W_i, S> is at least c_* d. Formal (SubcriticalProbability.v:36): for alpha < 1/4, kappa >= 1 and L >= 0 there is theta > 0 such that for every K and every N(d) <= alpha d^2 eventually, outside an event of probability tending to 0, if no coordinate of the sample reaches d^(1/4) and the head sections satisfy the operator bound L sqrt(d), then every J with \|J\| <= K d ln d whose sections of the same size have width at least (1/2 - g/16) d, g = 1/2 - sqrt(alpha), satisfies `paper_main_head_list_positive`: the section is nonempty and every unit tail vector capped by theta/sqrt(d) has a positive score at some section element. Only positivity is exported; the margin (g/4) sqrt(d) on the Frobenius unit sphere, the paper's c_* d on D_J = sqrt(d)(...) (l.863), stays inside the proof (SubcriticalEvent.v:34, 43-44). The two hypotheses on the sample are discharged by the coordinate tail of row 2.10 at d^(1/4) and by the upper feature edge. Verdict: weaker (positivity only, and added hypotheses on the sample). Argument: the paper's plan of l.870-871 (Gordon's inequality for the surrogate, interpolation transfer, clipping and concentration, union over heads), with the modifications R2, R4 and R7. |
| Lemma 3.5 `lem:regularity` (sec. 3.1, l.872) | `Head.TailDecompositionLog.paper_main_head_tail_regularity` (TailDecompositionLog.v:139), `Head.TailDecomposition.head_tail_decomposition_explicit` (TailDecomposition.v:61), `Head.Peeling.peeling_iteration` (Peeling.v:142) | same | paper's route | Same peeling as l.882-886, with the explicit constant C_theta = 16/(theta^2 ln 2) (TailDecompositionLog.v:27, `head_tail_constant`). |
| Lemma 3.8 `lem:head-correction-bounds` (sec. 3.2, l.970) | `Geometry.HeadSpectral.paper_main_head_correction_bounds_cone` (HeadSpectral.v:162), `Geometry.HeadEntries.paper_main_head_correction_bounds` (HeadEntries.v:107), `Geometry.HeadCorrection.paper_main_head_condition_transfer` (HeadCorrection.v:283), `paper_main_head_support_transfer` (HeadCorrection.v:176), `Head.CorrectionScale.paper_main_head_correction_eventual` (CorrectionScale.v:133), `Head.WidthActual.paper_main_head_width_actual_selected` (WidthActual.v:79) | weaker | paper's route | **Adjudication** (agent 3: weaker; agent 2: same). The paper (l.972-993): for a support maximizer P in K_kappa_0 cap S_F with residuals R_d <= C_A sqrt(log d/d), on E_data and for large d, simultaneously over \|J\| <= K_d, the corrected matrix (P + E_J)/\|P + E_J\|_F with a_J = Q_J^-1 r_J and E_J = -W_J^* a_J lies in K_kappa_1 cap ker W_J cap S_F, and the section support value is at least the cone support value minus C \|Z\|_F log d/sqrt(d). Formal: the same exact correction (`Geometry.HeadCoefficients`), in a parametrized deterministic form (HeadSpectral.v:162; HeadEntries.v:107 for a Loewner box in place of the cone): under the coercivity mu of the full Gram matrix, diagonal entries at least q0, off-diagonal entries at most q1, residuals at most R_d, X_J X_J^T <= lam I and the scalar conditions m R_d^2 <= mu eta^2, m R_d <= mu A_1, R_d + q1 A_1 <= q0 A_inf, (A_inf lam + A_1)/sqrt(d) <= delta, delta < 1/(kappa_0 sqrt(d)), kappa_0/sqrt(d) + delta <= kappa (1/(kappa_0 sqrt(d)) - delta), the corrected matrix lies in K_kappa cap S_F, solves the head equations, is within 2 eta of P in Frobenius norm and loses at most 2 eta \|Z\|_F of support value. CorrectionScale.v:133 instantiates the scalars with t = d^(1/32): residual threshold a/t^8 = a d^(-1/4) (the paper: C_A sqrt(log d/d)), eta = E/t^7 of order d^(-7/32) (the paper's loss C log d/sqrt(d)), A_inf of order 1/(d t^6), delta of order 1/(sqrt(d) t^4), and the target cone K_(2 kappa_0^2) (the paper: K_kappa_1 = K_(2 kappa_0)), because only the spectral box (kappa_0 sqrt(d))^-1 I <= P <= kappa_0/sqrt(d) I is used (`Geometry.HeadSpectral.paper_main_head_spectral_box`, HeadSpectral.v:107). Weyl's inequality (l.1042) is replaced by addition in the Loewner order (HeadCorrection.v:283); \|E_J\|_F is bounded with the lower edge alone (`Geometry.HeadCoefficients.paper_main_head_correction_energy`, HeadCoefficients.v:81). Verdict: weaker (coarser rates and a larger cone). Argument: the same correction and the same chain of bounds (l.996-1034). |
| Lemma 3.9 `lem:interpolation` (sec. 3.3, l.1150) | `Soft.Comparison.paper_main_soft_public_comparison` (Comparison.v:92), `Soft.PublicFeatures.paper_main_public_feature_soft_comparison` (PublicFeatures.v:137), `Multirow.IntegratedBound.paper_multirow_integrated_bound_results` (IntegratedBound.v:35) | weaker | paper's route | Same path sqrt(t) W + sqrt(1 - t) G and same bound 4 R_(N,d) M_3/(3 d^(3/2)) (l.1160), but proved only for the soft min-max Phi of Lemma 3.12 (l.1287-1293), with M_3 <= 10 b^3 (beta + gamma)^2 theta/sqrt(d) inserted (row 3.12; b a bound on the operator norm of the matrices) and R_(N,d) bounded by row 3.11: \|E Phi(W) - E Phi(G)\| <= (40/3) k^3 (beta + gamma)^2 theta (d + 2 sqrt(d ln N) + 2 ln N)/d^2 (Comparison.v:107). There is no statement for a general C^3 function F. The interpolation path and the cancellation of the divergence terms are `Multirow.*` and `Joint.*` (row 3.10). |
| Lemma 3.10 `lem:chaos-ibp` (sec. 3.3, l.1186) | `Gaussian.Vector.Stein.gaussian_vector_second_stein` (VectorStein.v:78), `Gaussian.Law.LibraryBridge.gaussian_iterated_coordinate_second_stein_gauss` (LawBridge.v:352) with library `library:gaussian.gauss_ibp.gauss_ibp2` (gauss_ibp.v:469), `Quadratic.TimeStein.quadratic_gaussian_time_stein` (TimeStein.v:65), `Joint.SteinIdentities.joint_gaussian_stein_cancellation` (SteinIdentities.v:169), `Row.ConditionalStein.gaussian_row_full_stein_of_regular` (ConditionalStein.v:183), `Multirow.FullStein.paper_multirow_full_stein_results` (FullStein.v:24), `Chaos.SecondContractionBounds.chaos_projective_bound` (SecondContractionBounds.v:149), `Multirow.IntegratedBoundSteps.multirow_integrated_remainder_sum_bound` (IntegratedBoundSteps.v:68) | weaker | paper's route | **Adjudication** (agent 3: weaker, with `quadratic_gaussian_time_stein`, `joint_gaussian_stein_cancellation`, `chaos_projective_bound` and `gaussian_vector_second_stein`; agent 2: same, with `paper_multirow_full_stein_results`, `gaussian_row_full_stein_of_regular`, `gaussian_iterated_coordinate_second_stein_gauss`, `gauss_ibp2` and `multirow_integrated_remainder_sum_bound`). The paper (l.1188-1204): for a row i and the C^3 function F of Lemma 3.9, (1/(2 sqrt(t))) E <W_i, Psi> = (1/d) E div_i Psi + (sqrt(t)/(2 d^(3/2))) E R_i(t) with R_i(t) = (1/2) sum_(a,b) D_i^3 F[U_a, U_b, V_ab], and \|R_i(t)\| <= 4 \|x_i\|^2 \|D_i^3 F\|_(pi,op); proof (l.1208) by E[(x_a x_b - delta_ab) f] = E[d_a d_b f]. Both counterpart sets exist at `3736fa2` and lie on one chain of the tree (each name is referenced by the next module, checked in the sources): the second-order Stein identity for f with polynomial bounds, which the paper states without proof, is `gauss_ibp2` in the library, transported to the list-based expectation in LawBridge.v:352 and to vectors in VectorStein.v:78 (used by `Quadratic.EntryStein`); TimeStein.v:65 is eq:ibp for one row, E <W(x), gradient> = (2 sqrt(t)/d) E[divergence] + (t/(d sqrt(d))) E[contraction of the third derivative], for the nested soft min-max observables; SteinIdentities.v:169 pairs it with the first-order identity for the GOE row and cancels the divergence terms, E[quadratic/(2 sqrt(t)) - goe/(2 sqrt(1 - t))] = (sqrt(t)/(2 d sqrt(d))) E[remainder]; ConditionalStein.v:183 lifts the identity to the law of all rows under regularity; FullStein.v:24 states it for each row and summed over rows (E[velocity_i] = (sqrt(t)/(2 d sqrt(d))) E[remainder_i], FullStein.v:36-40). The remainder bound eq:Ri-bound is SecondContractionBounds.v:149, \|contraction(T, x)\| <= 4 \|x\|^2 times the projective norm of T, for every tensor T represented by trace atoms (used by `Row.RemainderSum`), and summed over rows with the M_3 bound of row 3.12 in IntegratedBoundSteps.v:68. The identity is stated for the soft min-max observables only, not for a general C^3 F; the two ingredients are general. Verdict: weaker (a special case of the paper's statement); counterparts: the union of the two sets; argument: the paper's (second-order integration by parts applied to the entries of Psi). |
| Lemma 3.11 `lem:max-radius` (sec. 3.3, l.1235) | `Radius.ExpectationBound.gaussian_expected_maximum_radius` (ExpectationBound.v:52), `Radius.ExpectedMaximum.gaussian_maximum_radius_expected_bound` (ExpectedMaximum.v:109) | same | paper's route | Identical bound d + 2 sqrt(d ln N) + 2 ln N and same proof (moment generating function of the chi-square, `Radius.ExponentialMoments`, log-sum-exp, Jensen). |
| Lemma 3.12 `lem:soft` (sec. 3.3, l.1295) | `Soft.Extrema.soft_minimax_bounds` (Extrema.v:177), `Soft.MatrixProjectiveBound.soft_matrix_projective_sum_bound` (MatrixProjectiveBound.v:48), `Tensor.ProjectiveSum.matrix_nested_projective_sum_low_influence` (ProjectiveSum.v:149), `Soft.BlockThirdBound.lower_block_third_bound` (BlockThirdBound.v:27) | same | paper's route | Same sandwich bounds (l.1298-1302; Extrema.v:177) and the same three terms of the third derivative, with the explicit constant C = 10: sum_i \|D_i^3 Phi\|_(pi,op) <= 10 k^3 (beta + gamma)^2 theta/sqrt(d) (MatrixProjectiveBound.v:57-58, the paper's l.1304-1306). The projective norm is `Tensor.ProjectiveNormBounds` (read). |
| Lemma 3.13 `lem:gaussian-soft-head` (sec. 3.4, l.1436) | `Soft.FeatureMargin.paper_main_public_goe_soft_margin` (FeatureMargin.v:117), `Gordon.SoftMargin.paper_main_gordon_soft_width_margin` (SoftMargin.v:57), `Head.SectionApproxWidth.paper_main_head_section_net_width` (SectionApproxWidth.v:93), `paper_main_head_section_approx_width_exists` (SectionApproxWidth.v:133) | weaker | replaced | The paper (l.1438-1448): conditionally on a good head, the min-max over the two nets is at least c_0 d except with conditional probability exp(-c_prob d^2) (eq:net-margin-G), and E_G Phi_J >= c_1 d (eq:PhiG-mean). Formal: only the mean bound, proved directly from Gordon's inequality in expectation on the two finite nets: E_G Phi >= sqrt(2/d) (w(net) - sqrt(N)) - ln r/beta (FeatureMargin.v:117, 122-128), with w(net) the Gaussian width of the net of section elements, within eps sqrt(D_d) of the section width (SectionApproxWidth.v:93; the nets and their entropies, SectionApproxWidth.v:133). The high-probability bound eq:net-margin-G (l.1440-1445), the bound on \|G^*\| (eq:Gstar-bound) and the Cauchy-Schwarz step (l.1458-1470) have no counterpart (route R2). Agent 3 graded "replaced, weaker": statement weaker, argument replaced. |
| Corollary 3.14 `cor:chaos-soft-head` (sec. 3.4, l.1473) | `Head.SoftTail.paper_main_head_soft_expectation` (SoftTail.v:91), `Soft.ConeMargin.paper_main_data_soft_cone_margin` (ConeMargin.v:44), `Soft.ParameterChoice.paper_main_soft_scaled_margin` (ParameterChoice.v:83), `paper_main_soft_parameters` (ParameterChoice.v:29) | same | paper's route | An explicit lower bound on E_W Phi for a fixed head: E_W Phi >= sqrt(2/d) (w - sqrt(N)) - ln r/beta - (200/3) kappa^3 (beta + gamma)^2 theta/(d^2 sqrt(d)) (ConeMargin.v:54-58), then at beta = gamma = A d sqrt(d) the level ((1/2 - sqrt(alpha))/2) sqrt(d) on the unit sphere (ParameterChoice.v:93). The formal scores are the paper's divided by sqrt(d), so the formal inverse temperatures A d sqrt(d) are the paper's beta = gamma = L d. The order in which the constants (eps, A, theta) are chosen is ParameterChoice.v:29. |
| Lemma 3.15 `lem:clipped-soft-heads` (sec. 3.4, l.1501) | `Data.SoftConcentration.paper_main_data_soft_clipped_lower_margin` (SoftConcentration.v:119), `paper_main_data_soft_clipping_mean` (SoftConcentration.v:57), `Head.SubcriticalTail.paper_main_head_subcritical_clipped_tail` (SubcriticalTail.v:55), `Head.CompactTail.paper_main_head_compact_clipped_tail` (CompactTail.v:65), `Head.SoftTail.paper_main_head_soft_clipped_lower_tail` (SoftTail.v:116), `Head.SubcriticalFamily.paper_main_head_subcritical_family_event` (SubcriticalFamily.v:29), `Clipping.Limits.paper_main_clipped_head_union_tends_to_zero` (Limits.v:116) | weaker | paper's route | The paper clips the rows radially at 2 sqrt(d) (l.1498) and gets exp(-c d^2) per head (l.1506). The formal proof clips every coordinate at d^(1/4) (`Gaussian.Lipschitz.Clip`, `Data.Clipped`); the clipped functional is 2 (kappa/sqrt(d)) d^(1/4)-Lipschitz, so one head fails with probability exp(-c d^(3/2)) instead of exp(-c d^2) (SubcriticalTail.v:75-76); the union over the exp(C d (ln d)^2) heads (`Head.FamilyCount.paper_main_head_families_exp`, FamilyCount.v:98) still vanishes (Limits.v:116; route R4). The clipping error of the mean (l.1544-1550) is SoftConcentration.v:57. Argument: the paper's (clipping, Gaussian concentration of a Lipschitz functional, union over heads) with another clipping. |
| Theorem 4.1 `thm:unsat` (sec. 4, l.1613) | `Unsat.Limit.paper_main_unsat_supercritical_limit` (Limit.v:259), `paper_main_unsat_fixed_density_limit` (Limit.v:242), `paper_main_unsat_fixed_density_limit_from_events` (Limit.v:74), `Fixed.Density.paper_main_unsat_from_fixed` (Density.v:231) | same | paper's route | Same statement, with measurability. The trimming to n = floor(gamma d^2) (l.1621-1631) is Density.v:231 with `Fixed.Density.paper_main_eventual_trimming` (Density.v:142). P(fit) is bounded by P(the upper feature edge fails) + P(F_d), where F_d is a union over a net of orientations (Limit.v:74). The assembly follows the paper's plan of section 4.1 (a witness, its spectral split, a net, the exclusion of near-witnesses on each net element, a union bound); the steps inside are replaced (routes R8 to R12). |
| Lemma 4.2 `lem:homogeneous-witness` (sec. 4.1, l.1639) | `Projection.PinchingLoss.paper_main_fit_unit_witness` (Loss.v:16), `Geometry.Homogeneous.paper_main_homogeneous_kernel` (Homogeneous.v:132), `paper_main_homogeneous_witness` (Homogeneous.v:162) | stronger | paper's route | **Adjudication** (agent 3: weaker; agent 2: same). The paper (l.1640-1645): if x_1, ..., x_n span R^d, a fit exists iff some S >= 0 with \|S\|_F = 1 and some real b satisfy Q_x(S) = b 1. Formal: Homogeneous.v:132 (for d > 0 and a spanning sample, a fit exists iff some nonzero S >= 0 is in the kernel) composed with Homogeneous.v:162 (the kernel form iff the witness form, no hypothesis) is the paper's equivalence, in the tree through row 2.12. Loss.v:16 gives the direction "a fit gives a unit witness" for N, d > 0 without spanning, the direction thm:unsat uses, so the unsatisfiable phase never uses that the sample spans R^d (the paper invokes spanning at l.1649). Agent 3 named Loss.v:16 only. Verdict: stronger (the paper's statement, plus one direction without its hypothesis). |
| Proposition 4.3 `prop:translated-univ` (sec. 4.1, l.1716) | `Hybrid.FiniteMean.paper_main_hybrid_finite_mean_comparison` (FiniteMean.v:100), `paper_main_hybrid_finite_row_comparison` (FiniteMean.v:41), `Loss.Replacement.paper_main_loss_array_comparison` (Replacement.v:62), `Loss.RowIncrement.paper_main_loss_row_increment_comparison` (RowIncrement.v:119), `Unsat.FiniteTail.paper_main_unsat_ordered_tail` (FiniteTail.v:41) | same | replaced | The paper (l.1717-1733): for closed sets C_m of matrices with \|B\|_F <= C_0 and Tr \|B\|^3 <= m^-kappa, the supremum over offsets and C_m of \|E inf L_data - E inf L_goe\| tends to 0. Formal: no limit m -> oo and no infimum over a closed set; the comparison is between the soft minima (inverse temperature beta) over a finite list I of candidates (H_j, b_j, B_j) with B_j symmetric, \|B_j\|_op <= eps and \|B_j\|_F <= S_f: \|E Z_data - E Z_goe\| <= 2 eta + C(beta, eta) eps S_f for every eta > 0 (FiniteMean.v:100-112), uniform in N, the offsets and the prior. The bulk cutoff eps is a constant, not d^(-1/4), and infima are reached only after concentration (routes R8 to R10). Statement: the same in its role (the comparison of expected minima between data and surrogate, with an explicit error). |
| Proposition 4.4 `prop:hybrid-gap` (sec. 4.1, l.1739; proof sec. 4.3) | `Hybrid.Assembly.paper_main_hybrid_gap_event` (Assembly.v:134), `paper_main_hybrid_gap_event_joint` (Assembly.v:364), `Hybrid.Loss.paper_main_hybrid_risk_gap` (Loss.v:129), `Hybrid.Residual.paper_main_hybrid_residual_gap` (Residual.v:330) | stronger | paper's route | Outside an event of probability exp(-c d^2), the risk is at least e for all symmetric H, PSD B and real b with \|H\|_F^2 + \|B\|_F^2 >= 1/4 (Assembly.v:148-152): H only symmetric (the paper: PSD), no upper bound \|H\|_F^2 + \|B\|_F^2 <= 4 (l.1746), any gamma > 1/4 with \|N - gamma d^2\| <= eta d^2, bulk dimension up to d - r, and r <= sqrt(d) + 1 (Assembly.v:140) instead of r <= ceil(sqrt(d)). From the paper's three cases (section 4.3). |
| Proposition 4.5 `prop:true-net-gap` (sec. 4.1, l.1804; proof sec. 4.4) | `Unsat.Orientation.paper_main_unsat_orientation_constants` (Orientation.v:32), `Orientation.Exception.paper_main_orientation_exception` (Exception.v:51), `Orientation.Union.paper_main_orientation_union_fit` (Union.v:118), `Orientation.Family.paper_main_orientation_family_uniform` (Family.v:97), `Unsat.FiniteTail.paper_main_unsat_ordered_tail` (FiniteTail.v:41) | same | replaced | The net I_d of tuples (r, U, H, b) (l.1796) and the bound e_gamma/4 on the infimum over C_U(H) (l.1806-1810) are not formalized. Instead, for every orientation O (an orthogonal matrix) and rank r <= 1/eps_0^2, one event of probability at most exp(-N (e/4)^2/2) contains every sample whose feature Gram matrix is bounded and which admits an admissible candidate (A, b) for O of quadratic risk at most 16 L tau (Orientation.v:37-47); the union over a net of orientations in projector distance (`Orientation.Net`, Net.v:201, entropy (4 + 8 r/tau) ln 2 (r + 1)(d + 1)) and over r contains every fit (Union.v:118). The union bound runs over orientations only, with entropy O(d), not over heads and offsets with entropy O(d^(3/2)) (route R9). Statement: the same in its role (exclusion of all near-witnesses on a net, with high probability). |
| Lemma 4.6 `lem:transport` (sec. 4.1, l.1818) | `Projection.Pinching.paper_main_pinching_perturbation` (Pinching.v:95), `Projection.PinchingLoss.paper_main_pinching_witness_risk` (Loss.v:28), `paper_main_pinching_cutoff_bulk` (Loss.v:68), `Projection.PinchingAnnulus.paper_main_pinching_annulus` (Annulus.v:47), `Orientation.Witness.paper_main_orientation_fit_witness` (Witness.v:103) | same | replaced | No orthogonal transport O with \|O - I\|_op <= C tau (l.1819-1821) and no principal angles. The witness S is pinched by the projector U of the net member: A = U S U + (I - U) S (I - U), with \|S - A\|_F <= 4 \|U - P\|_F \|S\|_F (Pinching.v:95), quadratic risk at most 16 L tau when \|U - P\|_F <= tau (Loss.v:28), Frobenius norm in [1/2, 2] (Loss.v:58) and bulk operator norm at most eps_0 + tau^2 (Loss.v:68; route R9). Statement: the same in its role (rounding a witness to the net with a small loss). |
| Proposition 4.8 `prop:finite-prior-free-entropy` (sec. 4.2, l.1944) | `Hybrid.FiniteMean.paper_main_hybrid_finite_mean_comparison` (FiniteMean.v:100), `Loss.Replacement.paper_main_loss_array_comparison` (Replacement.v:62), `Loss.RowIncrement.paper_main_loss_row_increment_comparison` (RowIncrement.v:119), `Loss.ReplicaComparison.paper_main_loss_product_comparison` (ReplicaComparison.v:94), `paper_main_loss_replicated_comparison` (ReplicaComparison.v:123), `Loss.LogPolynomial.paper_main_loss_log_remainder` (LogPolynomial.v:57), `Loss.BlockComparison.paper_main_loss_conditional_prefix_comparison` (BlockComparison.v:38), `Projection.PublicOperator.paper_main_projection_public_comparison` (PublicOperator.v:54), `Projection.Comparison.paper_main_projection_smooth_comparison` (Comparison.v:69) | same | replaced | The paper sketches a modification of Theorem 4.6 of Bandeira and Maillard (l.1955), which it does not reproduce. The formal proof is complete and has its own route: rows are replaced one at a time (the Lindeberg replacement proved in `Loss.Replacement` from the block comparison BlockComparison.v:38; the library's `lindeberg_replacement` is not referenced); the soft-min increment of one row is -ln A/beta with A a Gibbs average of exp(-beta loss), expanded into a polynomial in 1 - A (LogPolynomial.v:57, `Loss.Replica`) whose powers are averages over Gibbs replicas of products of loss factors; each product, evaluated at the quadratic forms y^T B_j y - Tr B_j of one Gaussian row, is compared with the same product at Gaussian linear forms of the same covariance by the fixed-dimensional smooth comparison (PublicOperator.v:54: error K^2 2 C eps S for a C^2 test of K features; Comparison.v:69), proved by the square-root interpolation and the Stein identities of `Projection.*` and `Gaussian.Coordinate.UniformSumBound` (the library's `gauss_interpolation` is not referenced). Error 2 eta + C(beta, eta) eps \|B\|_F per row (RowIncrement.v:125-130), uniform in N, the offsets and the prior (route R10). Statement: a complete statement with the same role as the sketched one. |
| Lemma 4.9 `lem:ground-state-transfer` (sec. 4.2, l.1962) | `Orientation.Prior.paper_main_orientation_prior` (Prior.v:48), `Loss.QuadraticPrior.paper_main_quadratic_prior_positive` (QuadraticPrior.v:63), `Orientation.BlocksLoss.paper_main_orientation_candidate_bound` (BlocksLoss.v:135), `paper_main_orientation_candidate_bound_rotate` (BlocksLoss.v:153), `Loss.JointNet.paper_main_loss_joint_net` (JointNet.v:49) | same | replaced | No limsup_m and no C delta + (C/beta) log(1 + 2 C_0/delta) (l.1965-1970). A finite prior of admissible candidates of size ln s <= 3 C(delta/(L + 3)) d^2 approximates the risk of every admissible (A, b) within 4 (L + 1) delta (QuadraticPrior.v:69-76); the soft minimum over it is at most the minimal risk plus ln s/(beta N) (BlocksLoss.v:140-141), so the finite-prior functional of a fit is at most 16 L tau + 4 (L + 1) delta + ln s/(beta N) (Prior.v:63-65). The delta-net, its entropy and the Lipschitz step are used sample by sample after concentration, on the data side only, with beta fixed; there is no comparison of expected ground states. Statement: the same in its role (the ground state is approximated by a finite-prior soft minimum up to delta and an entropy term). |
| Lemma 4.10 `lem:head-smallball` (sec. 4.3, l.2072) | `Head.SmallBallUniform.paper_main_head_small_ball_uniform_poly` (SmallBallUniform.v:646), `paper_main_head_small_ball_uniform` (SmallBallUniform.v:482), `Head.SmallBallPZ.paper_main_head_small_ball_probability` (SmallBallPZ.v:188), `Head.SmallBallFourth.paper_main_head_small_ball_moments` (SmallBallFourth.v:349), `Head.SmallBallCount.paper_main_head_row_count_lower_exp` (SmallBallCount.v:379), `Head.SmallBallNet.paper_main_head_small_ball_param_net` (SmallBallNet.v:200); library `library:probability.moments.paley_zygmund` (moments.v:87) | same | replaced | **Adjudication** (agent 3: replaced; agent 2: same). The paper (l.2073-2078): universal a_0, delta_0, c_0 such that for large d and 1 <= r <= k_d, with probability at least 1 - exp(-c_0 n), \|K(H, b)_J\|_2 >= a_0 sqrt(n) (2 \|H\|_F^2 + b^2)^(1/2) for all symmetric H, real b and \|J\| >= (1 - delta_0) n. Formal (SmallBallUniform.v:646): for 306432 (r + 1)^3 <= m, outside an event of probability at most exp(-((2 ln 2 - 1)/2432) m), every symmetric H, real b and J with \|J\| >= (1 - 1/1216) m satisfy sum_{i in J} (g_i^T H g_i - Tr H - b)^2 >= (m/4864)(2 \|H\|_F^2 + b^2): the paper's eq:smallball with a_0^2 = 1/4864, delta_0 = 1/1216 and c_0 = (2 ln 2 - 1)/2432, under an explicit threshold on m in place of "for all large d", satisfied for r <= sqrt(d) + 1 and m = N >= (gamma/2) d^2 (`Hybrid.Density`). Verdict: statement same; the two tables agreed on the facts, and agent 3's grade concerned the argument, which is replaced: a net of the parameters (H, b), a Markov truncation of \|g g^T - I\|_F and binomial tails over the rows (SmallBallNet.v:200, SmallBallCount.v:379) instead of Sauer's lemma and the VC inequality (l.2093-2098), and E Y^4 <= 19 sigma^4 computed from the moments of x^2 - 1 after a rotation (SmallBallFourth.v:355) instead of hypercontractivity (l.2088), so Paley-Zygmund gives 1/76 instead of 1/324 (SmallBallPZ.v:188; route R11). |
| Lemma 4.11 `lem:projected-bulk-escape` (sec. 4.3, l.2126) | `Hybrid.Bulk.paper_main_hybrid_bulk_event` (Bulk.v:29), `Projected.BulkConditional.paper_main_projected_psd_conditional_tail` (BulkConditional.v:949), `Projected.BulkEscape.paper_main_projected_escape_tail` (BulkEscape.v:37), `Projected.BulkUnion.paper_main_projected_count_entropy` (BulkUnion.v:105), `Projected.BulkLaw.paper_main_projected_law` (BulkLaw.v:186), `Projected.BulkComplement.paper_main_projected_complement_mx` (BulkComplement.v:66), `Hybrid.Assembly.paper_main_hybrid_operator_event` (Assembly.v:39) | stronger | paper's route | **Adjudication** (agent 3: stronger; agent 2: same). The paper (l.2128-2137): conditionally on a head satisfying the small-ball condition, for large d and 0 <= r <= k_d, with conditional probability at least 1 - exp(-Delta^2 d^2/64) - exp(-n/4), \|P_J R(B)_J\|_2 >= c_bulk sqrt(n) \|B\|_F and \|R(B)_J\|_2 <= C_0 sqrt(n) \|B\|_F for all PSD B and \|J\| >= (1 - delta) n. Formal (Bulk.v:29): for gamma > 1/4 there are eta, delta < 1/1216, c, c_2 and d_0 such that for d >= d_0, \|N - gamma d^2\| <= eta d^2, r <= sqrt(d) + 1, r + mi + 1 <= d and every measurable head-feature map, outside an event of probability at most exp(-c_2 d^2) under the joint law of head and bulk (and under the product law, BulkConditional.v:949), for every J with \|J\| >= (1 - delta) N and every PSD B of Frobenius norm one, the distance from R(B)_J to the range of the head features, the minimum over coefficient vectors c of \|R(B)_J + X_J c\|, exceeds c d; no small-ball condition and no full column rank of the head features is needed (a complement basis, BulkComplement.v:66, and Bessel's inequality replace P_J). The upper bound \|R(B)\|_2 <= C(rho) sqrt(N) \|B\|_F holds for all symmetric B outside an event of probability 2 exp(-N/2) (Assembly.v:39-47, from the GOE operator bound of row 2.8). The union over J costs exp(k (1 + ln(N/k))) (BulkUnion.v:105) instead of exp(n H_2(delta)) (l.2171). Verdict: stronger (fewer hypotheses). Argument: the paper's (escape through a mesh for the Gaussian bulk, BulkEscape.v:37; rotation invariance, BulkLaw.v:186; a union over deletion sets), with the complement basis in place of the projection (route R11). |
| Lemma 4.12 `lem:conditional-true-mean-gap` (sec. 4.4, l.2282) | `Hybrid.FiniteMean.paper_main_hybrid_finite_goe_mean` (FiniteMean.v:177), `paper_main_hybrid_finite_mean_comparison` (FiniteMean.v:100), `Loss.ExpectedGap.paper_main_loss_expected_gap` (ExpectedGap.v:22), `Hybrid.FiniteTail.paper_main_hybrid_finite_data_lower_tail` (FiniteTail.v:35), `Unsat.FiniteTail.paper_main_unsat_ordered_tail` (FiniteTail.v:41) | weaker | replaced | The paper (l.2283-2296): for fixed r <= k_d and a deterministic U, P(E_U^c) <= exp(-c_gamma d^2) for the head event E_U, and on E_U, for every H in H_U and b with C_U(H) nonempty, E[E_(U,H,b)({W_i}) given (g_i)] >= e_gamma/2. Formal: nothing is conditioned on the head and there is no head event. E Z_goe >= e (1 - exp(-c d^2)) holds for the mean over heads and bulks together (FiniteMean.v:177, 191-193; the step from a high-probability bound to the mean is ExpectedGap.v:22), the comparison of row 4.3 transfers it to the data, E Z_data >= E Z_goe - (2 eta + C eps S_f), and the lower tail exp(-N t^2/2) (Hybrid FiniteTail.v:35-46; Unsat FiniteTail.v:41) replaces McDiarmid (l.2330-2335; routes R9 and R12). Statement: weaker (the unconditional mean bound follows from the paper's conditional one, not conversely). Agent 3 graded "replaced, weaker": statement weaker, argument replaced. |

Count by statement relation: same 18, weaker 15, stronger 6, absent 0.
Count by argument relation: paper's route 26, replaced 13 (Lemmas 2.3,
2.5, 2.6, 2.7, 2.11, 3.13, 4.6, 4.9, 4.10, 4.12 and Propositions 4.3, 4.5,
4.8).

Verdicts of the adjudicated rows (statement, argument): Lemma 2.2
stronger, paper's route; Lemma 2.4 weaker, paper's route; Lemma 2.7
stronger, replaced; Lemma 2.10 stronger, paper's route; Lemma 3.2 weaker,
paper's route; Proposition 3.3 weaker, paper's route; Proposition 3.4
weaker, paper's route; Lemma 3.8 weaker, paper's route; Lemma 3.10 weaker,
paper's route, with the union of the two counterpart sets; Lemma 4.2
stronger, paper's route; Lemma 4.10 same, replaced; Lemma 4.11 stronger,
paper's route. The three rows graded "replaced, weaker" by agent 3 (Lemmas
2.3, 3.13, 4.12) are weaker, replaced.

**Remarks.** Remarks 3.6, 3.7 and 4.7 have no formal statement. Their
claims hold in the formal proof as follows.
- Remark 3.6 (condition number O((1/4 - alpha)^-2)): the formal constants
  of Theorem 1.3 have the same order.
- Remark 3.7 (where 1/4 enters the satisfiable phase): 1/4 enters only
  through 1/2 - sqrt(alpha) > 0
  (`Soft.ParameterChoice.paper_main_soft_subcritical_gap`,
  ParameterChoice.v:20). The remark also says that the feature map stays
  well conditioned up to density 1/2. The formal proof does not prove that:
  its lower feature edge stops at 1/4 (Lemma 2.6).
- Remark 4.7 (where 1/4 enters the unsatisfiable phase): the hypothesis
  gamma > 1/4 is used only in the hybrid gap
  (`Hybrid.Density.paper_main_hybrid_density_margin_gamma`, Density.v:326)
  and passed down from there; gamma < 1/2 is used only to get N <= d^2 for
  the upper feature edge. The remark (l.1909-1911) and the proof of
  Proposition 4.5 rely on the uniform universality of Proposition 4.3 over
  offsets that depend on the head realization; the proposition is stated
  for deterministic offsets, which suffices by conditioning (l.2316-2319).

## (a) Results the paper cites without proof

The formal proof assumes nothing from the paper or the literature: every
cited result is either proved, replaced by a weaker statement that it
proves, or avoided.

| Cited result | Where the paper uses it | What the formal proof does |
|---|---|---|
| Kogan, Nandy and Huang, extreme eigenvalues of polynomial-scaling kernel matrices, Thm 1.2(2a) | Lemma 2.6 (l.543) | Its own moment method, with non-sharp constants (route R3). Upper edge: the expectation of tr W^L of the off-diagonal part of V V^T is a sum over closed walks (`SquareFree.WalkExpansion`), each weighted by a Gaussian moment bounded through the multiplicity excess (`SquareFree.WalkWeight`, `SquareFree.WalkExcess`); the walks are counted by a twin code (`SquareFree.WalkShapeCode`, `WalkShapeOnce`, `WalkShapeBound`), giving E tr W^L <= N (52 d^2)^L for L = 2^(k+3), k = log_2 log_2 d (`SquareFree.EdgeUpper.paper_main_squarefree_offdiag_trace_le`, EdgeUpper.v:165), then Markov at t = 104 d^2 (`SquareFree.EdgeUpperLimit.paper_main_squarefree_offdiag_rate`, EdgeUpperLimit.v:230). Lower edge: the non-backtracking recursion of their Lemma 5.1 is proved exactly (`SquareFree.EdgeLower.pmlo_knh`, EdgeLower.v:385), the traces of powers of the non-backtracking matrices are bounded by a count of marked walks (`SquareFree.WalkNBMoment.pmnct_moment_le`, WalkNBMoment.v:245), the column remainders by deterministic operator bounds and column-norm concentration (`Column.Remainder*`, `Column.RemainderProbability.paper_main_column_remainder_probability`, RemainderProbability.v:41), and a Chebyshev-polynomial step turns the bounds into the Loewner box -(49/24) I <= T_1 - s I with s about sqrt(2 n/d^2) (`SquareFree.EdgeLower.pmlo_cheb_box`, EdgeLower.v:246), from which the square-free Gram matrix is at least (d^2/128) I when 4 N <= d^2 (`SquareFree.Coercivity.paper_main_squarefree_coercivity_generic`, Coercivity.v:118). The box is a little worse than their sharp constant 2: with 49/24 the final scalar step (63/64 + s^2 - (49/24) s > 0) works for s < 0.78, about density 0.3 (our computation), and the formal statement assumes 4 n <= d^2. |
| Tropp, matrix Bernstein, Thm 6.6.1 | Lemma 2.7 (l.585) | Not used. A fourth trace moment (`Feature.DiagonalMoment.paper_main_diag_trace_moment`, Moment.v:868) and Markov's inequality; no truncation. |
| Vershynin, norms of rectangular Gaussian matrices, Thm 7.3.1 | Lemma 2.5 (l.495), used in Prop. 2.8, Lemma 2.10, eq:Gstar-bound, Lemma 4.11 | A net bound with worse constants (`Gaussian.Tail.Operator.paper_main_gaussian_operator_tail`, OperatorTail.v:74; row 2.5). eq:Gstar-bound is not needed (route R2). The library also proves the sharp mean E \|G\|_op <= E\|g\| + E\|h\| and its tail by Sudakov-Fernique (`library:comparison.escape.gauss_opnorm_mean`, escape.v:778; `gauss_opnorm_tail`, escape.v:847), but the proof of the paper does not use them. |
| Rudelson and Vershynin, Hanson-Wright inequality | Lemma 2.11 (l.660), in prop:heads | Its own proof for Gaussian vectors: orthogonal diagonalization, rotation invariance and a chi-square Chernoff bound (`Gaussian.Orthogonal.HansonWright.paper_main_gaussian_quadratic_tail`, QuadraticTail.v:57; `Gaussian.Orthogonal.Tail.paper_main_gaussian_orthogonal_square_two_sided_tail`, OrthogonalTail.v:36; library `library:comparison.chi_square.gauss_centered_chi2_abs_tail`, chi_square.v:351). |
| Gordon (1985), comparison theorem for min-max of finite Gaussian arrays, in probability; Thrampoulidis, Oymak and Hassibi for background | Lemma 2.3 (l.448-454) | The expectation form for finite families, proved in the library from Kahane's comparison inequality applied to a smooth min-max (`library:comparison.gordon.gordon`, gordon.v:648, and `gordon_cov`, gordon.v:771, from `library:gaussian.gauss_interpolation.gauss_comparison`, gauss_interpolation.v:369). It has no equal-variance hypothesis. The bilinear instance min_z max_v z^T A v against <g, z> + <h, v> is `library:comparison.escape.auxT_bilT_minmax` (escape.v:409), the only entry point of this comparison that the tree references (from `Gordon.Processes`); `aux_bil_minmax` (escape.v:335) and the Sudakov-Fernique inequality for the maximum (`library:comparison.slepian.sudakov_fernique`, slepian.v:389) serve inside the library for the escape and operator-norm results. The probability form is never proved (route R2). |
| Gordon (1988), escape through a mesh | Lemma 2.4 (l.478), in Lemma 4.11 | Proved: the expectation bound in the library from the same comparison and nets (`library:comparison.escape.gordon_escape`, escape.v:603; `library:matrix.nets.net_exists`, nets.v:406), then Gaussian concentration; threshold sqrt(N - 1) (`Gaussian.Lipschitz.EscapeTail.paper_main_gaussian_escape_sqrt_tail`, EscapeTail.v:18). The library's tail form with the exact mean (`gordon_escape_tail`, escape.v:684) is not referenced. |
| eq:chi-mean, sqrt(s - 1) <= E\|g_s\| <= sqrt(s) (l.491) | Lemmas 2.3, 2.4, 4.11 | Proved (`Gaussian.Lipschitz.EuclideanNorm.paper_main_gaussian_norm_expectation`, Norm.v:77; `Gaussian.Lipschitz.NormConcentration.paper_main_gaussian_norm_mean_lower`, NormConcentration.v:78); the Gamma-function formula is not. |
| Boucheron, Lugosi and Massart, Gaussian concentration, Thm 5.6 | Lemmas 2.3, 3.15, eq:radius (l.469, l.1551) | Proved in the library by the Herbst argument with the sharp constant (`library:comparison.gauss_concentration.gauss_concentration`, gauss_concentration.v:930); tails by Chernoff (`Gaussian.Lipschitz.Concentration.paper_main_gaussian_lipschitz_lower_tail`, LipschitzConcentration.v:109). |
| Boucheron, Lugosi and Massart, McDiarmid's inequality, Thm 6.2 | Prop. 4.5 (l.2331) | Its own bounded-difference inequality, on full rows, by Hoeffding's lemma and induction over rows (`Loss.ConcentrationRow.paper_main_concentration_rows`, ConcentrationRow.v:292; `Loss.ConcentrationTail.paper_main_concentration_lower_tail`, ConcentrationTail.v:29). For rows that change the function by at most 1/N, it gives exp(-N t^2/2) where McDiarmid gives exp(-2 N t^2): an exponent 4 times smaller, which is enough. |
| Amelunxen, Lotz, McCoy and Tropp, Prop. 10.2 (width versus statistical dimension) | Lemma 2.1 (l.365) | Its argument written out for the PSD cone, with the Gaussian Poincare inequality of the library (`Gaussian.Width.SignedSupport.paper_main_gaussian_mean_positive_square_lower`, WidthVariance.v:113; `paper_main_gaussian_positive_square_lower`, WidthVariance.v:73; `library:comparison.gauss_concentration.gauss_poincare_lipschitz`, gauss_concentration.v:1124) applied to the positive part of the support function (`Cone.ProjectionSupport.paper_main_psd_sphere_support_max`, ProjectionSupport.v:114). |
| Anderson, Guionnet and Zeitouni, Thm 2.1.22 (\|Z\|_op/sqrt(d) -> sqrt(2)), and the semicircle law | Lemma 2.2 (l.390-401) | Not used. A net bound \|Z\|_op <= 20 sqrt(d) with probability at least 1 - 2 exp(-10 d) (`Gaussian.Symmetric.OperatorTail.paper_main_symmetric_gaussian_operator_good_set`, SymmetricOperatorTail.v:20), the lower bound E\|Z_+\|_F >= d/2 - 1 from Lemma 2.1, and E (Tr Z)^2 = d (route R1). |
| Bandeira and Maillard, Lemma 3.6 | Lemma 2.2 (the paper reproves it) | Not used. |
| Bandeira and Maillard, free-entropy universality, Thm 4.6 and sec. 4 | Prop. 4.8 (only sketched, l.1955) | Not used. A complete proof by another route (route R10). |
| Lindeberg's replacement principle (used implicitly through Bandeira and Maillard) | Prop. 4.8 (l.1955) | `library:probability.lindeberg.lindeberg_replacement` (lindeberg.v:230) exists but is not referenced; the tree proves the replacement it needs in `Loss.Replacement` (row 4.8). |
| Second-chaos interpolation and Gaussian comparison with matching covariances | Lemma 3.9 (l.1254-1275), Prop. 4.8 (l.1955) | The library's `library:gaussian.gauss_interpolation.gauss_interpolation` (gauss_interpolation.v:294) and `gauss_comparison` (gauss_interpolation.v:369) are general statements for C^2 tests of Gaussian vectors, but the tree does not reference them. The theories use their own interpolation calculus (`Gaussian.Covariance.InterpolationCoefficients`, `Gaussian.Coordinate.UniformSumBound`, `Multirow.*`, `Projection.*`) and the law statement `library:comparison.gauss_law.gauss_mulmx_law` (gauss_law.v:569) through `Gaussian.Orthogonal.EqualCovariance.paper_main_covariance_equal_expectation` (CovarianceBounds.v:81). |
| Aliprantis and Border, measurable maximum theorem, Thm 18.19; the measurable minimum theorem for eq:net-selector | Prop. 3.3 (l.964), sec. 3.5 (l.1553) | Not used. The maximizer P(Z) is the first maximizer over a fixed finite net of the cone sphere, within eps \|Z\|_F of the supremum (`Cone.ApproxSelector.paper_main_cone_selector_gaussian`, ApproxSelector.v:197; `Head.FiniteSupportSelector.paper_main_finite_argmax_measurable`, FiniteSupportSelector.v:79), and the events are shown measurable through countable nets (`Head.SectionMeasurable.paper_main_head_section_support_measurable`, SectionMeasurable.v:370). The conditional step of l.1074-1078 is `Clipping.ResidualConditional.paper_main_cone_selector_conditional` (ResidualConditional.v:46), with Markov on the section probability (`Gaussian.Sample.ConditionalException.paper_main_conditional_exception_reverse_markov`, ConditionalException.v:38). Nets of a fixed head are chosen classically, and probabilities are integrated over the head by a Fubini bound on sections (routes R5 and R7). |
| Second-order Gaussian integration by parts, E[(x_a x_b - delta_ab) f] = E[d_a d_b f] (stated without reference) | Lemma 3.10 (l.1208) | Proved, for f with polynomial growth (`Gaussian.Vector.Stein.gaussian_vector_second_stein`, VectorStein.v:78, from `library:gaussian.gauss_ibp.gauss_ibp2`, gauss_ibp.v:469, through `Gaussian.Law.LibraryBridge.gaussian_iterated_coordinate_second_stein_gauss`, LawBridge.v:352). |
| The chi-square moment generating function, E exp(t x^2) = (1 - 2t)^(-1/2) | Lemma 3.11 (l.1242) | `Gaussian.Line.QuadraticMGF.gaussian_quadratic_exponential_expectation` (QuadraticMGF.v:42), from `library:comparison.chi_square.integral_normal_expR_sqr` (chi_square.v:86) through `Gaussian.Law.LibraryBridge`; the bound of l.1244 and the maximum are `Radius.ExponentialMoments` and `Radius.ExpectedMaximum`. |
| Weyl's inequality | Lemma 3.8 (l.1042) | Replaced by addition in the Loewner order (`Geometry.HeadCorrection.paper_main_head_condition_transfer`, HeadCorrection.v:283). |
| Packing bounds for nets, (1 + 2/rho)^N and the like | sec. 3.5, Prop. 4.5, Lemma 4.9 | Grid nets with log-cardinality (4 + 4/eps) ln 2 times the dimension (`Gordon.Entropy.paper_main_gordon_entropy_net`, Entropy.v:144; `Loss.JointNet.paper_main_loss_joint_net`, JointNet.v:49; `Loss.BallNet.paper_main_loss_ball_net`, BallNet.v:45). |
| Szarek, nets of the Grassmannian | Prop. 4.5 (l.1755) | Its own net of orthogonal frames in the projector distance \|P_U - P_V\|_F <= tau, built from nets of the unit ball of R^(d x d), with log-cardinality (4 + 8 r/tau) ln 2 (r + 1)(d + 1) (`Orientation.Net.paper_main_orientation_net`, Net.v:201). It is worse than Szarek's bound and enough only because the head rank is bounded (route R8). |
| The binomial entropy bounds sum_{j <= delta n} C(n, j) <= exp(n H_2(delta)) and sum_{k <= K_d} C(n, k) <= exp(C K_d log(e n/K_d)) | Lemma 4.11 (l.2171), sec. 3.5 (l.1562) | Replaced by sum_{j <= k} C(n, j) <= exp(k (1 + ln(n/k))) (`Projected.BulkUnion.paper_main_projected_count_entropy`, BulkUnion.v:105) and by `Head.FamilyCount.paper_main_head_families_entropy` (FamilyCount.v:81). |
| The principal-angle identity | Lemma 4.6 | Not needed (pinching, route R9). |
| Gaussian hypercontractivity, \|Y\|_4 <= 3 \|Y\|_2 for degree two | Lemma 4.10 (l.2088) | Not used: E Y^4 <= 19 sigma^4 is computed from the moments of x^2 - 1 after a rotation (`Head.SmallBallFourth.paper_main_head_small_ball_moments`, SmallBallFourth.v:349). |
| Paley-Zygmund inequality | Lemma 4.10 (l.2088) | The library's `library:probability.moments.paley_zygmund` (moments.v:87), referenced by `Head.SmallBallPZ`. |
| Sauer's lemma and the VC inequality (Devroye, Gyorfi and Lugosi, Thm 12.5) | Lemma 4.10 (l.2093-2098) | Not used: a net of the parameters, a Markov truncation and binomial tails (route R11). |
| Gordan-Stiemke duality (Boyd and Vandenberghe) | Cor. 1.4, Lemma 2.12 (l.173) | Proved directly (row 2.12). |
| Rotation invariance of the standard Gaussian (used implicitly) | eq:decompose, Lemma 4.11 | Proved in the library (`library:comparison.gauss_law.gauss_orthogonal_law`, gauss_law.v:607) and used through `Projected.BulkLaw.paper_main_projected_law` (BulkLaw.v:186) and `Orientation.Rotation.paper_main_orientation_rotate_law` (Rotation.v:147). |
| Spectral theorem and spectral projectors (used implicitly) | eq:split-def, sgn(M_u) in thm:sat, and throughout | The library's real spectral theorem (`library:matrix.real_spectral.symmetric_spectral`, real_spectral.v:295), by a Rayleigh maximum on the unit sphere (`rayleigh_max`, real_spectral.v:236) and Householder reflections (`householder`, real_spectral.v:152); referenced by `Spectral.SymmetricDiagonalization`, the only entry point of the tree. sgn(M_u) is avoided (route R6). |
| Operator norm from traces of powers and from quadratic forms | l.2158-2167 and the edge arguments | `library:matrix.opnorm.opnorm_le_trace_exp` (opnorm.v:282, used by `Feature.DiagonalTrace`, `SquareFree.EdgeUpper`, `SquareFree.WalkNBEvent`) and `opnorm_le_form_exp` (opnorm.v:292, used by `SquareFree.EdgeLower`); the commutator inequality tr(ABAB) <= tr(A^2 B^2) is `library:matrix.real_spectral.mxtrace_ABAB_le` (real_spectral.v:64). |
| Almost sure spanning of the sample for n >= d (stated) | Lemma 2.12, cor:alternative, thm:unsat (l.678, l.1649) | Proved where it is needed, for cor:alternative (`Gaussian.Spanning.AlmostSure.paper_main_gaussian_spanning_ae`, Spanning.v:85). thm:unsat does not need it (row 4.2). |

## (b) Changes of route

- **R1. Widths of cones (sec. 2.1, Lemmas 2.1 and 2.2).** The projection
  onto the PSD cone is built as a nearest point, with Moreau's
  decomposition, without the spectral theorem
  (`Cone.Projection.paper_main_psd_projection`, Projection.v:196;
  `paper_main_psd_moreau`, Projection.v:229). Lemma 2.1 uses the Poincare
  inequality in place of the cited Proposition 10.2 of Amelunxen, Lotz,
  McCoy and Tropp. Lemma 2.2 keeps the paper's candidate (l.387-418), but
  bounds its value pointwise on and off the event \|Z\|_op <= 20 sqrt(d)
  (`Gaussian.Width.Condition.paper_main_gaussian_condition_point_bound`,
  ConditionWidth.v:151; `Gaussian.Width.ConditionBound`,
  `Gaussian.Symmetric.OperatorTail`, `Cone.Condition`) and integrates, so
  no limit in probability, no semicircle law and no uniform integrability
  are used. The result is non-asymptotic.
- **R2. Gordon's inequality in expectation (secs. 2.2, 3.3, 3.5; l.434-476,
  l.1451-1471).** The paper proves a tail bound for the min-max over the
  whole sphere and a compact set (Lemma 2.3), applies it at t = eta d
  (eq:gordon-tail-margin), restricts to nets on the event
  \|G^*\| <= C_G sqrt(d), and passes to expectations by Cauchy-Schwarz
  (Lemma 3.13). The formal proof applies Gordon's inequality in expectation
  directly to the finite nets of dual vectors and of the head section, then
  the log-sum-exp bound (`Gordon.Processes`, `Gordon.Width`,
  `Gordon.SoftMargin.paper_main_gordon_soft_width_margin`, SoftMargin.v:57;
  `Gordon.Nets`, `Gordon.Entropy`). The net loss is eps sqrt(D_d), also in
  expectation (`Head.SectionApproxWidth.paper_main_head_section_net_width`,
  SectionApproxWidth.v:93). Probability enters only after the comparison
  with the data, through the concentration of the clipped data functional
  (R4); the Lipschitz lower tail `Gaussian.Lipschitz.LowerMargin` is the tool.
- **R3. Feature edge (sec. 2.3, l.538-616).** Both edges are proved by
  moment methods (see (a); `SquareFree.*`, `Column.*`, `DiagonalBlock.*`,
  `Feature.UpperProbability`). The lower edge holds only up to density 1/4,
  the upper edge for densities in [c, 1], with explicit but non-sharp
  constants (d^2/128 and 109 d^2) and explicit polynomial rates, for each
  sequence N(d) separately; the paper's compactness argument over K is not
  needed. The lower edge uses the upper edge and the coordinate clipping
  inside its column-norm events
  (`Column.ConcentrationFrame.paper_main_column_frame`,
  ConcentrationFrame.v:210), which the paper's lower edge does not. The
  diagonal block uses a fourth trace moment instead of matrix Bernstein
  (row 2.7). The bound \|E_J\|_F^2 = a^T Q_J a is replaced by
  a^T r <= \|r\|^2/mu, so the head correction needs only the lower edge
  (`Geometry.HeadCoefficients.paper_main_head_correction_energy`,
  HeadCoefficients.v:81).
- **R4. Clipping (secs. 2.4, 3.5; l.1517-1566).** The paper clips the
  radius at 2 sqrt(d), bounds the clipping error with nuclear norms and
  chi-square tails, and gets exp(-c d^2) per head. The formal proof clips
  every coordinate at d^(1/4) (`Data.Clipped.paper_main_data_clipped_feature`,
  Clipped.v:28; `Gaussian.Lipschitz.Clip`). Each clipped score is then
  2 k d^(-1/4)-Lipschitz in all coordinates
  (`Data.ClippedSoft.paper_main_data_clipped_soft_lipschitz`,
  ClippedSoft.v:54), the mean changes by at most
  V/a + 2 a N d exp(-sqrt(d)/2)
  (`Gaussian.Lipschitz.ClippingTransfer.paper_main_gaussian_clipping_mean_loss`,
  ClippingTransfer.v:22), and one head fails with probability
  exp(-c d^(3/2)). The union over the exp(C d (ln d)^2) heads, counted by
  `Head.FamilyCount`, still goes to 0
  (`Clipping.Rates.paper_main_clipped_head_union_rate`, Rates.v:168). The
  event that some coordinate reaches d^(1/4), of probability at most
  2 N d exp(-sqrt(d)/2), is added to the exceptional set
  (`Clipping.Limits.paper_main_coordinate_clipping_tends_to_zero`,
  Limits.v:75).
- **R5. Head sections (sec. 3.2, Prop. 3.3, Lemma 3.8; l.960-1096).** The
  exact correction of the paper is kept, with four differences. The Borel
  maximizer P(Z) is replaced by the first maximizer over a fixed finite
  eps-net of K_k0 cap S_F, which is measurable and loses eps \|Z\|_F
  (`Cone.ApproxSelectorResidual.paper_main_cone_selector_residual`,
  ApproxSelectorResidual.v:31); hence a loss eps d in Prop. 3.3 instead of
  o(d). The residuals r_i are bounded at the coarse threshold
  sqrt(4 + 4 k0) d^(-1/4), with the Gaussian Hanson-Wright inequality and a
  rate 2 exp(-sqrt(d)/2) per row
  (`Clipping.ResidualRates.paper_main_residual_exponential_rate`,
  ResidualRates.v:61), and the joint-to-conditional passage (l.1074-1093)
  is Markov on the section probability with tau = d^(-4)
  (`Gaussian.Sample.ConditionalException.paper_main_conditional_exception_reverse_markov`,
  ConditionalException.v:38; `Head.WidthRegular`, WidthRegular.v:71-72).
  The integration over Z uses 2v <= v^2/a + a with a = d^2 instead of
  Cauchy-Schwarz
  (`Head.WidthExpectation.paper_main_head_width_expectation_transfer`,
  WidthExpectation.v:47). The Weyl step uses only the box
  (k0 sqrt(d))^-1 I <= P <= k0/sqrt(d) I
  (`Geometry.HeadSpectral.paper_main_head_spectral_box`,
  HeadSpectral.v:107), whose ratio is k0^2, so the corrected matrices lie
  in K_(2 k0^2). The rates of Lemma 3.8 are polynomial in t = d^(1/32)
  (`Head.CorrectionScale`, CorrectionScale.v:139-142) instead of powers of
  log d, and the law of a selected head is `Head.SelectionLaw` (permutation
  invariance of the product law).
- **R6. Assembly of thm:sat (sec. 3.1; l.805-821, l.889-924).** The convex
  separation is done on the trace-one slice of the cone K_kappa, made
  compact by adding the Loewner witness as a coordinate
  (`Cone.KernelSlice.paper_main_cone_kernel_slice_compact`,
  KernelSlice.v:123; `Cone.Kernel.paper_main_cone_kernel_variational`,
  Kernel.v:104), by the paper's own nearest-point argument (row 3.2);
  the fit is then produced from a kernel element of the cone sphere
  (`Cone.Kernel`, `Conditioned.SupportFit`, `Cone.HeadTailFit`). Section
  matrices are rescaled into [I, k I] and the box is [1/2, k + 1/2]
  (`Cone.HeadTailFit.paper_main_condition_box`, HeadTailFit.v:16), which
  gives the constants (2 k + 1)^(+-1). In the tiny-tail case (l.901-921,
  `Head.TailSupportSplit.paper_main_support_tiny`, TailSupportSplit.v:175)
  the perturbation is delta M_u/\|M_u\|_F instead of delta_0 sgn(M_u), so
  no spectral sign function is needed
  (`Head.TailSupport.paper_main_support_perturbation`, TailSupport.v:80).
  The spread case uses only that the tail score is positive.
- **R7. Low-influence tail (secs. 3.4 and 3.5; l.1254-1275).** The
  interpolation of Lemma 3.9 keeps the paper's path and constants but is
  proved for the soft min-max only, through the row-wise Stein identities
  of `Row.*`, `Joint.*` and `Multirow.*`, with the library's Gaussian
  integration by parts through `Gaussian.Law.LibraryBridge` (row 3.10). The head
  is fixed, its nets are chosen classically, the tail probability is
  bounded under the law of the tail rows, and the bound is integrated over
  the head by a section bound
  (`Head.SubcriticalConditional.paper_main_head_selection_section_bound`,
  SubcriticalConditional.v:34). The bad event is the exact min-max over
  the whole capped dual set and section
  (`Head.CompactEvent.paper_main_head_compact_value`, CompactEvent.v:61),
  so the passages from nets to sets (eq:net-to-all) and from soft to hard
  extrema (eq:soft-to-hard) happen inside the event bound. Heads are
  counted as ordered lists with repetitions, at most (N + 1)^K
  (`Head.FamilyCount.paper_main_head_families_exp`, FamilyCount.v:98).
- **R8. Constant spectral cutoff (sec. 4.1, eq:epsd, eq:split-def;
  l.1665-1683).** The paper splits a witness at eps_d = d^(-1/4), so the
  head has rank at most sqrt(d) and the bulk has Tr B^3 -> 0, which makes
  the universality error o(1). The formal proof splits at a constant
  eps0 = eps/2 (`Orientation.Spectral.paper_main_orientation_spectral_order`,
  Spectral.v:137; `paper_main_orientation_spectral_decomposition`,
  Spectral.v:175), so the head rank is at most a constant
  rmax >= 1/eps0^2 (`Orientation.Family.paper_main_orientation_rank_bound`,
  Family.v:150; `Orientation.Witness`, Witness.v:107), and the bulk
  satisfies only \|B\|_op <= eps (eps0 + tau^2 after pinching). The
  universality error 2 eta + 2 C eps is then made small by choosing eps
  after C = C(beta, eta)
  (`Unsat.SupercriticalParameters.paper_main_unsat_cutoff_parameters`,
  SupercriticalParameters.v:42), not by letting d grow. No Schatten-3
  bound appears. The bounded rank is also what makes the orientation net
  of R9 small enough.
- **R9. Nets, pinching and finite priors (secs. 4.1 and 4.4;
  l.1755-1851).** The paper takes a union over a net I_d of tuples
  (r, U, H, b) with entropy O(d^(3/2)), rounds a witness to the net by a
  rotation O close to the identity (Lemma 4.6), conditions on the head
  coordinates of U, and applies Prop. 4.3 and McDiarmid's inequality for
  each tuple. The formal proof takes a net of orientations only, in the
  projector distance, with entropy O(d)
  (`Orientation.Family.paper_main_orientation_family_uniform`,
  Family.v:97; `Orientation.Net`). A witness is pinched by the projector of
  the nearest orientation (row 4.6). For each orientation, the whole
  sample is rotated, which keeps its Gaussian law
  (`Orientation.Rotation.paper_main_orientation_rotate_law`,
  Rotation.v:147), and one joint delta-net of all admissible (H, b, B),
  fixed before the data (`Orientation.Prior.paper_main_orientation_prior`,
  Prior.v:48), enters a soft minimum at a fixed inverse temperature
  (rows 4.5, 4.6, 4.9). The entropy of that prior, of order d^2, is paid
  as ln s/(beta N), a small constant, instead of in a union bound. Nothing
  is conditioned on the head: the hybrid mean is taken over heads and
  bulks together (`Hybrid.FiniteMean.paper_main_hybrid_finite_goe_mean`,
  FiniteMean.v:177), and the head small-ball failure enters only through
  exp(-c d^2) in that mean.
- **R10. Bulk universality (sec. 4.2; l.1917-2025).** In place of the
  free-entropy interpolation of Bandeira and Maillard: (1) whole rows are
  replaced one at a time (`Loss.Replacement.paper_main_loss_array_comparison`,
  Replacement.v:62); (2) for one row, the change of the soft minimum is
  -ln A/beta, with A a Gibbs average of exp(-beta loss)
  (`Loss.Gibbs.paper_main_gibbs_row_increment`, Gibbs.v:49); (3) -ln A is
  approximated uniformly by a polynomial in 1 - A, whose powers are
  averages over Gibbs replicas of products of loss factors
  (`Loss.Replica.paper_main_loss_row_poly_uniform`, Replica.v:91); (4)
  each product, evaluated at the quadratic forms y^T B_j y - Tr B_j of one
  Gaussian row, is compared with the same product at Gaussian linear forms
  of the same covariance, along the path sqrt(t) Q + sqrt(1 - t) L, with
  first-order Gaussian integration by parts
  (`Projection.Comparison.paper_main_projection_smooth_comparison`,
  Comparison.v:69). The error is 2 eta + C(beta, eta) eps \|B\|_F with
  eps = max \|B_j\|_op, for every N, all dimensions, all offsets and every
  finite prior, with explicit errors and no limits (rows 4.3, 4.8, 4.9;
  `Loss.*`, `Projection.*`, `Hybrid.FiniteMean`). Only two bounded
  derivatives of the test function are used. The paper's own second-chaos
  Lindeberg principle (Lemma 3.9) is not used here, nor is the library's
  Lindeberg file (`library/probability/lindeberg.v`).
- **R11. Hybrid gap (sec. 4.3; l.2081-2108).** Lemma 4.10 is proved with
  a net of the parameters (H, b), a Markov truncation of \|g g^T - I\|_F
  and binomial tails over the rows
  (`Head.SmallBallUniform.paper_main_head_small_ball_uniform`,
  SmallBallUniform.v:482), instead of Sauer's lemma and the VC inequality;
  it needs n >= 306432 (r + 1)^3, where the paper needs r^2 log n = o(n).
  The fourth moment is computed instead of hypercontractivity. Lemma 4.11
  does not use the projection P_J: for a fixed head, an orthonormal basis
  of the complement of the head range
  (`Projected.BulkComplement.paper_main_projected_complement_mx`,
  BulkComplement.v:66) and Bessel's inequality bound the residual from
  below for every head coefficient, so the small-ball event is not needed
  in the bulk bound. Deletion sets are counted with exp(k (1 + ln(n/k)))
  instead of exp(n H_2(delta)). One event on head and bulk together is
  bounded; the conditional form eq:hybrid-conditional is not stated.
- **R12. Concentration in the unsatisfiable phase (sec. 4.4;
  l.2329-2349).** McDiarmid's inequality, applied by the paper to the
  bulk rows conditionally on the head, is replaced by the formal
  bounded-difference inequality for Gaussian rows
  (`Loss.ConcentrationRow`) applied to full rows (head and bulk), with
  oscillation 1/N per row: P(Z_data <= E Z_data - t) <= exp(-N t^2/2)
  (`Hybrid.FiniteTail.paper_main_hybrid_finite_data_lower_tail`,
  FiniteTail.v:35). The union over the orientation net is
  `Orientation.Union`.
- **R13. Measurability (everywhere).** The events are proved measurable:
  the three events of the statement by countable rational approximation
  (`Measurability.*`), the exceptional events by continuity of the
  functionals of the sample (`Analysis.ContinuousTupleMeasurability`,
  `Gaussian.Smooth.Centered`). The paper does not discuss measurability except
  at l.964 and l.1553.
- **R14. Fixed densities (everywhere).** The reductions to fixed densities
  (l.752-757, l.1621-1631) are `Fixed.Density` with `Gaussian.Sample.Deletion`: deleting
  points cannot increase the fit probabilities (Density.v:66, 78).

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
  (`Data.FeatureMomentsCoordinates.pmdf_regular`,
  FeatureMomentsCoordinates.v:48), and transports their iterated Gaussian
  expectations to the product law (`Data.FeatureMoments.pmdf_actual`,
  FeatureMoments.v:60). The second-order Stein identity of Lemma 3.10
  assumes differentiability, a continuous second derivative and polynomial
  bounds on f and its first two derivatives
  (`Gaussian.Vector.Stein.gaussian_vector_second_stein`, VectorStein.v:78).
  The comparison of section 4.2 assumes test functions with two bounded
  continuous derivatives, and the concentration inequalities assume
  continuous bounded functions
  (`Loss.ConcentrationTail.paper_main_concentration_lower_tail`,
  ConcentrationTail.v:29: continuity and a row oscillation bound c; the
  normalized soft minimum has c = 1/N, `Loss.ConcentrationSoftMin`,
  ConcentrationSoftMin.v:112-126, the paper's 1/n at l.2330). The paper's
  uses satisfy all of these: polynomials, the soft min-max (smooth, with
  bounded derivatives), and the bounded smooth loss 1 - exp(-t^2). The
  paper covers them in one sentence (l.1274) or not at all.
- **Measurability.** Every event and every statistic must be measurable,
  including infima and suprema over uncountable sets: the fit event, the
  width of a data-dependent section, the min-max of section 3.5, the
  infimum over (J, v, c) in Lemma 4.11. The formal proof shows it through
  countable nets, rational approximation and continuity
  (`Measurability.Fit.pm_fit_event_measurable`, Fit.v:372;
  `Head.SectionWidthLaw.paper_main_head_section_width_measurable`,
  SectionWidthLaw.v:158;
  `Projected.BulkConditional.paper_main_projected_bad_measurable`,
  BulkConditional.v:826). The paper discusses only the measurable
  selection of section 3.5. Satisfied.
- **Finite index sets.** Gordon's inequality is proved for finite families
  only, and the nets of section 3.5 must lie inside the sets they
  approximate; the net vectors of
  `Gordon.SoftMargin.paper_main_gordon_soft_width_margin`
  (SoftMargin.v:59-60) must have norm exactly one, which the nets of
  `Gordon.Entropy` (Entropy.v:144) do. The paper uses compact sets.
  Satisfied, since nets exist.
- **Nonemptiness.** Head sections, priors and capped dual sets must be
  nonempty. The paper uses the convention that an infimum over an empty
  set is +infinity and omits empty C_U(H); the formal proof takes the
  support of an empty set to be 0 and derives nonemptiness of sections
  from positive width. Satisfied.
- **Explicit ranges of d.** The paper says "for all large d". The formal
  thresholds are explicit and sometimes very large: d >= 2^9600 for the
  rate of the upper feature edge
  (`SquareFree.EdgeUpperLimit.paper_main_squarefree_offdiag_rate`,
  EdgeUpperLimit.v:230; `SquareFree.WalkNBRate.pmnbr_rate`,
  WalkNBRate.v:221, read), d0 of order 10^15 for the hybrid gap near
  gamma = 1/4 (computed from the formal threshold), d > 1734/eps for
  Lemma 2.2, d >= rmax^2 + 1 for the head rank. The theorems are stated
  for all large d with an existential threshold, so the limits hold, but
  these inner thresholds are astronomically larger than the paper's
  unstated ones. They do not matter for the asymptotic statement.
- **Logarithmic conditions.** ln N <= d in
  `Soft.PublicFeatures.paper_main_public_feature_soft_comparison_coarse`
  (PublicFeatures.v:175) and `Soft.ConeMargin` (ConeMargin.v:51); 1 <= ln d
  in the coherence and sparse-norm events of row 2.10. Satisfied for
  N <= d^2 and d >= 2 ln d.
- **Density windows.** The lower feature edge needs 4 N <= d^2, d^2 <= c_1 N
  and a density eventually at least c
  (`SquareFree.LowerProbability.paper_main_squarefree_lower_probability`,
  LowerProbability.v:36-39); the upper edge needs N <= d^2 and a density
  eventually at least c > 0; the hybrid gap needs \|N - gamma d^2\| <= eta d^2,
  r <= sqrt(d) + 1 and r + m + 1 <= d
  (`Hybrid.Assembly.paper_main_hybrid_gap_event`, Assembly.v:138-140). The
  padded and trimmed counts N = floor(beta d^2), with beta in (0, 1/4) or
  (1/4, 1/2), satisfy them
  (`Fixed.SubcriticalCounts.paper_main_fixed_subcritical_counts`,
  SubcriticalCounts.v:18; `Unsat.Limit`, Limit.v:7-8). The paper's Lemma
  2.6 has no such restriction, and the formal proof does not cover its
  range (1/4, 1/2); the unsatisfiable phase uses only the upper edge.
- **Head size.** r <= sqrt(d) + 1, r <= rmax, and n >= 306432 (r + 1)^3 for
  the head small ball
  (`Head.SmallBallUniform.paper_main_head_small_ball_uniform_poly`,
  SmallBallUniform.v:647). Satisfied for large d (`Hybrid.Density`,
  Density.v:326-340).
- **Parameters of the unsatisfiable phase.**
  `Orientation.Witness.paper_main_orientation_fit_witness`
  (Witness.v:105-107) needs tau <= 1/8, eps_0 + tau^2 <= eps and
  1/eps_0^2 <= rmax < d, chosen by
  `Unsat.SupercriticalParameters.paper_main_unsat_cutoff_parameters`
  (SupercriticalParameters.v:42) and `Unsat.Limit` (Limit.v:7-8);
  `Loss.QuadraticPrior.paper_main_quadratic_prior_positive`
  (QuadraticPrior.v:65-66) needs candidates with \|A\|_F^2 <= 4 and
  \|b\| <= L, satisfied by pinched witnesses
  (`Projection.PinchingLoss.paper_main_pinching_unit_norm`, Loss.v:58) and by the
  Gram bound (`Feature.LossControl.paper_main_feature_witness_offset`,
  LossControl.v:19, read);
  `Unsat.Orientation.paper_main_unsat_orientation_constants`
  (Orientation.v:44-45) needs the feature Gram matrix at most K I with
  K <= N L^2, where (gamma/2) L^2 = 109, discharged by row 2.8
  (`Loss.EntropyBudget.paper_main_loss_feature_constant`,
  EntropyBudget.v:19).
- **Matrices.** Coefficient matrices must be symmetric for the Stein
  identities; operator-norm bounds are stated as bounds on bilinear forms
  (`Cone.ConditionOperator.paper_main_cone_opnorm_le`,
  ConditionOperator.v:41); the cone K_k is written in Loewner form,
  lam I <= S <= k lam I for some lam > 0. The residual tail
  `Gaussian.Sample.ResidualTail.paper_main_gaussian_residual_tail` (Residual.v:84-87)
  needs \|P\|_F = 1 and the bilinear bound kappa/sqrt(d), satisfied by
  every element of the cone sphere
  (`Spectral.OperatorTransport.paper_main_matrix_operator_cone_sphere`,
  OperatorTransport.v:144; `Geometry.HeadSpectral.paper_main_head_condition_box`,
  HeadSpectral.v:151), as in the paper's l.966. Satisfied.
- **Positivity of the support.** `Cone.Kernel.paper_main_cone_kernel_exists_support`
  (Kernel.v:219-220) needs a positive support value for every unit y,
  supplied by `Head.TailSupportAll.paper_main_support_all`
  (TailSupportAll.v:89) under the scalar condition
  A d^-2 (b + delta) sqrt(d) < delta sqrt(mu)/2 (TailSupportAll.v:116), the
  formal form of C/d < c'' sqrt(d) (l.921). Satisfied for large d.
- **Choice.** Several exceptional events are chosen for each d separately,
  with Hilbert's epsilon or classical choice
  (`Head.DataLog.paper_main_head_data_log_probability`, DataLog.v:77); no
  measurability in d is needed. These axioms are among the eight of
  `check/assumptions.expected`.
- **Feature bounds as hypotheses.** The satisfiable assembly takes the two
  feature edges as hypotheses outside vanishing events
  (`Conditioned.SpectralReduction.paper_main_subcritical_spectral_reduction`,
  SpectralReduction.v:56), the head-section width theorem takes the
  coercivity of the Gram matrix with constant c d
  (`Head.RegularProbability.paper_main_head_width_coercive_probability_uniform`,
  RegularProbability.v:170-171), discharged from row 2.9 for alpha < 1/4
  only, and the tail argument takes the operator bound L sqrt(d) and the
  coordinate bound d^(1/4) as hypotheses on the sample
  (`Head.SubcriticalProbability.paper_main_head_subcritical_probability`,
  SubcriticalProbability.v:44-46); the first has probability tending to
  one for N <= C d^2 (`Clipping.Limits`, Limits.v:75), the second is the
  upper edge. The coherence bound takes the radius event as a hypothesis
  (`Data.SampleTail.paper_main_data_coherence_good`, SampleTail.v:446-450),
  as in the paper (l.657). They are discharged at N = floor(beta d^2).

## (d) Formal results near the top of the tree with no paper counterpart

Depth is the distance from the two theorems in agent 3's dependency graph;
size is the number of declarations each one uses, directly or not.

| Formal result | Depth | Size | What it does |
|---|---|---|---|
| `Measurability.Fit.pm_fit_event_measurable` (Fit.v:372), `Measurability.Conditioned.pm_conditioned_event_measurable` (Conditioned.v:253), `Measurability.Balanced.pm_balanced_pd_event_measurable` (Balanced.v:385) | 1 | 76 to 86 | Measurability of the three events, asserted by the formal statement. Each event is a countable union or intersection of sets defined by polynomial inequalities over rational matrices or weights; a cluster-point argument gives the set equality. |
| `Gaussian.Spanning.AlmostSure.paper_main_gaussian_spanning_ae` (Spanning.v:85) | 4 | 39 | The sample spans R^d almost surely when n >= d (the paper's l.678, in parentheses): the determinant of the first d points is a nonzero polynomial, and its zero set is null for the Gaussian law (`Gaussian.Spanning.MultivariateZeros`). |
| `Fixed.Density.paper_main_conditioned_from_fixed` (Density.v:173), `Fixed.Density.paper_main_unsat_from_fixed` (Density.v:231), `Gaussian.Sample.Deletion.paper_main_drop_points_law` (Gaussian.Sample.Deletion.v:117) | 1 to 5 | 14 to 41 | The padding and trimming of the paper (one sentence each, l.752-757 and l.1621-1631), as statements on probabilities: the law of a sample after deleting points is the law of the smaller sample, and deleting points is measurable and cannot increase the fit probabilities (Gaussian.Sample.Deletion.v:178, 188; the paper's "feasibility is monotone", l.757). |
| `Orientation.Rotation.paper_main_orientation_rotate_law` (Rotation.v:147) | 5 | 228 | Rotating every point by an orthogonal matrix keeps the product Gaussian law. The paper uses it without comment in eq:decompose. |
| `Feature.UpperProbability.paper_main_feature_upper_event_measurable` (UpperProbability.v:18), `Hybrid.FiniteArray.paper_main_hybrid_finite_data_regular` (FiniteArray.v:167) | 5 | 341 to 379 | Measurability of the exceptional events and regularity (continuity, polynomial bounds) of the soft losses, needed to state and integrate them. |
| `Loss.ExpectedGap.paper_main_loss_expected_gap` (ExpectedGap.v:22) | 6 | 281 | E F >= e (1 - p) when F >= 0 and F >= e outside an event of probability p: the step from a high-probability bound to a mean. |
| `Loss.ConcentrationSoftMin.paper_main_softmin_lower_tail` (ConcentrationSoftMin.v:112) | 6 | 399 | The bounded-difference inequality for the soft minimum, uniform in the prior; it replaces the cited McDiarmid inequality. |
| `Head.SubcriticalEvent.paper_main_head_subcritical_bad_measurable` (SubcriticalEvent.v:57), `Head.SectionWidthLaw.paper_main_head_section_width_measurable` (SectionWidthLaw.v:158) | 11 to 13 | 640 to 693 | Measurability of the bad event of section 3.5 and of the section width as a function of the head (the width is a Tonelli integral). |
| `Head.SubcriticalConditional.paper_main_head_selection_section_bound` (SubcriticalConditional.v:34), `Head.Law.paper_main_split_coordinates_section_bound` (Law.v:183) | 11 to 12 | 16 to 63 | The formal form of "condition on the head": a bound on every section of a measurable joint event bounds the event. |
| `Gaussian.Law.LibraryBridge.gaussian_iterated_expectation_gauss` (LawBridge.v:272) | 15 | 137 | The bridge that lets the library's Gaussian measure on row vectors act on the list-based law of the frozen definitions: `gauss d` of the library is the image of the product law of the statement (`gauss_gaussian_product_law`, LawBridge.v:88), and iterated expectations are integrals against it. |

The largest formal subtrees without a paper proof are re-proofs of results
the paper cites, listed in (a): the moment method for the feature edge
(about 1,300 declarations below
`Column.RemainderProbability.paper_main_column_remainder_probability`
(RemainderProbability.v:41) and 860 below
`SquareFree.LowerProbabilityTrace.paper_main_squarefree_trace_rate`
(LowerProbabilityTrace.v:51)), and the universality of section 4.2 (about
1,000 declarations below
`Hybrid.FiniteMean.paper_main_hybrid_finite_mean_comparison`
(FiniteMean.v:100)).

By distance from the frozen files in agent 2's block graph (distance 0: the
frozen files; distance 1: `PaperMainFinalAssembly`,
`PaperMainConditionedLimit`), the modules without a counterpart in the
paper are:

- Distance 2: `Asymptotics` (7 declarations: squeezes of limits, and the
  reduction `paper_main_sat_from_conditioned` (Asymptotics.v:104) of
  Theorem 1.2(a) to Theorem 1.3, which the paper states in one sentence at
  l.741); `Fixed.Density` (13: reductions to n = floor(beta d^2) by padding
  and trimming, Density.v:173, 231); `Measurability.Fit`,
  `Measurability.Conditioned`, `Measurability.Balanced` (32, 16, 30: the
  three events are Borel); `Balanced.Probability`, `Balanced.Limit` (4, 1:
  the two limits of Corollary 1.4 from Theorem 1.2, the paper's l.173);
  `Unsat.Limit` (4: the assembly of Theorem 4.1 from the orientation
  events, Limit.v:74, which collects the paper's proof of l.1854-1906 in
  one statement).
- Distance 3: `Balanced.Law`, `Balanced.Supercritical` (a failed fit and
  spanning imply the balanced certificate; almost sure equality of the two
  events, Supercritical.v:85); `Conditioned.FromLower` (Theorem 1.3 at
  fixed density from the lower edge, FromLower.v:33);
  `Fixed.LowerProbability` (the lower edge at n = floor(beta d^2),
  LowerProbability.v:40); `Measurability.Countable`.
- Distance 4: `Gaussian.Sample.Deletion` (18); `Feature.GramBlocks` (16:
  Q Q^* = D D^T + V V^T, GramBlocks.v:118, the paper's l.519);
  `Geometry.Exclusion`, `Geometry.Homogeneous`, `Geometry.Separation` (the
  alternative, row 2.12); `Geometry.HeadCoefficients` (coercivity and Gram
  matrix of a head, `paper_main_head_coercive`, HeadCoefficients.v:31);
  `SquareFree.LowerProbability` (row 2.6); `Unsat.Orientation` (the
  constants of the unsatisfiable phase chosen in order, Orientation.v:32;
  the paper fixes its constants inside proofs, l.1855, l.2110-2117,
  l.2216).
- Distance 5: `Conditioned.FromLowerScalars` (0 < lm <= lp);
  `Conditioned.SpectralReduction` (SpectralReduction.v:56, 91: Theorem 1.3
  from the two spectral bounds on the features, with the exceptional
  events of `Head.SubcriticalFit`); `Feature.LossControl` (the quadratic
  risk `paper_main_quadratic_risk`, LossControl.v:15, its Lipschitz bound
  under a Gram bound, LossControl.v:62, and `paper_main_quadratic_risk_zero`,
  LossControl.v:85: the paper's eq:empirical-loss and eq:Q-lip);
  `Fixed.CountBounds`, `Fixed.SubcriticalCounts` (counts at fixed
  density); `Gaussian.Spanning.AlmostSure`; `Gordon.Entropy` (nets of unit vectors
  with ln \|net\| <= (4 + 4/eps) ln 2 d, Entropy.v:144);
  `Hybrid.FiniteMean`, `Orientation.Exception`, `Orientation.Family`,
  `Orientation.Net`, `Orientation.Union`, `Orientation.Witness`,
  `Unsat.FiniteTail`, `Unsat.Rates`, `Unsat.SupercriticalParameters` (the
  finite-prior and orientation-net machinery of rows 4.3, 4.5, 4.6, 4.9);
  `Loss.EntropyBudget` (c L^2 = 109); `SquareFree.ChebyshevParametersEdge`,
  `SquareFree.WalkNBRate`, `SquareFree.LowerProbabilityAssembly`,
  `SquareFree.EdgeUpperLimit` (row 2.6); `Measurability.Compact`,
  `Measurability.Coordinates`.
- Distance 6: `Analysis.ContinuousTupleMeasurability` (continuous functions
  of the coordinates are measurable); `Gaussian.Symmetric.Coordinates`,
  `Gaussian.Iterated.Definitions` (the iterated Gaussian
  expectation on lists, the paper's E); `Gaussian.Spanning.MultivariateZeros`
  (polynomial functions of the sample vanish on a null set);
  `Head.SectionMeasurable`; `Hybrid.FiniteArray`, `Hybrid.FiniteTail`;
  `Loss.Empirical`; `Measurability.Box`; `Orientation.Prior`,
  `Orientation.Rotation`; `Projection.Pinching`; `SquareFree.EdgeLower`
  (row 2.6); `Column.RemainderProbability`; `Geometry.HeadCorrection` (the
  deterministic part of row 3.8).
- Deeper, with no counterpart anywhere in the paper: `Gaussian.Law.LibraryBridge`
  (distance 8); `Analysis.RealsBridge` (distance 7: pointwise identities
  between Stdlib's and MathComp's real operations); `Head.SelectionLaw`
  (distance 11: the law of a fixed head of rows and its tail is a product
  law, SelectionLaw.v:135); `Gaussian.Sample.PermutationLaw` (invariance of the
  product law under coordinate permutations); `Cone.ApproxSelector`
  (distance 14), `Head.FiniteSupportSelector` (distance 15),
  `Clipping.ResidualConditional` (distance 12): the measurable selectors
  and the conditional Markov step of section (a).

## (e) Gaussian-specific and distribution-free parts

The paper is written for Gaussian data, and so is the formal proof. Three
kinds of Gaussian use must be told apart: the law of the data x_i, the law
of the Gaussian surrogate (GOE rows, the hybrid bulk), and the auxiliary
Gaussian Z that defines widths. The surrogate and Z are Gaussian by
construction and would stay Gaussian for non-Gaussian data, although the
covariance of the surrogate would have to match that of the data (first
row of the table below).

**Distribution-free** (deterministic, or using only that the rows are
independent and identically distributed):
- convex duality: the Gordan-Stiemke alternative of Lemma 2.12 and the
  separation of Lemma 3.2 (`Geometry.*`, `Cone.Kernel*`,
  `Conditioned.SupportFit`);
- cone geometry: the PSD projection and Moreau's decomposition, the
  condition cones (`Cone.Projection`, `Cone.Condition*`);
- the spectral theorem and operator norms (`library:matrix.real_spectral`,
  `library:matrix.opnorm`), the spectral split and pinching
  (`Orientation.Spectral`, `Projection.Pinching`, `Pinching.*`);
- nets and counting (`library:matrix.nets`, `Gordon.Entropy`,
  `Orientation.Net`, `Head.FamilyCount`, the walk counting of the feature
  edge);
- the head-tail decomposition (Lemma 3.5) and the algebra of the exact
  correction (Lemma 3.8, `Geometry.Head*`);
- the soft extrema and their third derivatives in the projective norm
  (Lemma 3.12, `Soft.Extrema`, `Tensor.*`, `Chaos.CubicMassBounds`), the
  contraction bound of Lemma 3.10 (pointwise in x);
- the bounded-difference inequality, row replacement, the replica
  expansion (`Loss.Concentration*`, `Loss.Replacement`, `Loss.Gibbs`,
  `Loss.Replica`), Paley-Zygmund and the counting of the head small ball,
  the risk bounds of the hybrid gap (`Hybrid.Loss`, `Hybrid.Residual`).
  These are stated for the iterated Gaussian expectation but use only the
  product structure;
- almost sure spanning, which needs only a law with a density.

**Gaussian law of the surrogate or of the auxiliary Z only** (these
arguments would survive non-Gaussian data, up to the covariance of the
surrogate): the widths of Lemmas 2.1 and 2.2; Gordon's inequality and
escape through a mesh (library `comparison/gordon.v`,
`comparison/escape.v`); the norms of Gaussian matrices (Lemma 2.5) for the
surrogate, although the same net argument is also applied to the data (row
"Data estimates" of the table below); the Stein identity for the GOE rows
(`Joint.SectionStein.joint_goe_section_stein`, SectionStein.v:78); the
rotation invariance of the hybrid bulk array
(`Projected.BulkLaw.paper_main_projected_law`, BulkLaw.v:186).

**Gaussian law of the data**, by component:

| Component | Paper | What is Gaussian | Formal modules |
|---|---|---|---|
| Chaos-to-GOE transfer, satisfiable phase | Lemmas 3.9, 3.10 | Second-order Stein identity for x; the GOE surrogate matches the covariance of the chaos rows. For independent coordinates with fourth moment m_4, Var(x^T A x) = 2 \|A\|_F^2 + (m_4 - 3) sum_a A_aa^2, so the GOE surrogate is the right one only when m_4 = 3. | `Gaussian.Vector.Stein`, `Quadratic.EntryStein`, `Quadratic.TimeStein`, `Multirow.*`, `Soft.Comparison` |
| Concentration of the clipped functional | Lemma 3.15 | Dimension-free Gaussian concentration of a Lipschitz function of all n d coordinates. The soft min-max is not convex, so Talagrand's convex-distance inequality would not replace it directly. | `Data.SoftConcentration`, `Gaussian.Lipschitz.Concentration` |
| Data estimates | Lemma 2.10, eq:radius | Chi-square and linear Gaussian tails (sub-Gaussian tails would do); the coherence bound uses the law of <x_i, x_j> given x_i, that is rotation invariance. The bound L d (ln d)^2 on the Gram matrices of the data heads is the operator-norm net bound of Lemma 2.5 applied to the data: the exception events are net tests of the bilinear forms u^T X_J v of the sample, whose tails are the Gaussian tails of unit linear forms of the sample (`Data.HeadOperator`). A sub-Gaussian operator-norm bound would do. | `Gaussian.Sample.Radius*`, `Data.CoherenceLimit`, `Data.SampleTail`, `Data.HeadOperator`, `Data.HeadOperatorUniform`, `Head.DataLog` |
| Residuals of the head correction | Lemma 2.11 in Prop. 3.3 | The Hanson-Wright proof uses diagonalization and rotation invariance. By our reading of the proof, the Markov step costs a factor N d^4, so a one-row tail o(d^(-6)) at the threshold d^(-1/4) suffices, and a high moment bound on x^T P x - Tr P would do. | `Gaussian.Orthogonal.HansonWright`, `Gaussian.Sample.Residual*` |
| Feature edge | Lemmas 2.6, 2.7 | Exact Gaussian moments of monomials, including the vanishing of odd moments, and explicit fourth and eighth moments. The paper cites Kogan, Nandy and Huang, whose theorem covers centered coordinates with moment growth; the formal proof is more Gaussian-specific here, and a non-Gaussian version would have to redo the walk count for odd multiplicities. | `SquareFree.Walk*`, `Column.*`, `DiagonalBlock.*` |
| Orientations and head/bulk independence | eq:decompose, secs. 4.1, 4.4 | Rotation invariance of the sample: it reduces every orientation to fixed coordinates and makes the head and bulk parts of a point independent standard Gaussians. This is the main obstacle in the unsatisfiable phase for non-Gaussian data. | `Orientation.Rotation`, `Head.Law` |
| Bulk universality | Props. 4.3, 4.8 | First-order Gaussian integration by parts for the bulk vector and Gaussian fourth moments of quadratic forms (the surrogate covariance 2 <A, B> again needs m_4 = 3). It is the only use of the data law in that comparison. | `Projection.*`, `Loss.ReplicaComparison` |
| Head small ball | Lemma 4.10 | E Y^2 = 2 \|H\|_F^2 + b^2 and E Y^4 <= 19 sigma^4 by rotation and explicit moments, and E \|g g^T - I\|_F^2 = r (r + 1). Any law with a small-ball bound for quadratic forms would do. | `Head.SmallBall*` |

The Gaussian law of the data enters the two phases through the feature
edge (rows 2.6-2.9), the elementary estimates (row 2.10), the residual
tails (row 2.11), the head selection laws, the chaos-to-Gaussian
comparisons (rows 3.9, 4.3, 4.8) and the concentration of the clipped and
soft functionals (rows 3.15, 4.12). Everything about widths, Gordon's
inequalities and the hybrid model concerns auxiliary Gaussian objects.

Module lists by law, from agent 2's reading of the statements:

- Gaussian law of the data x (`gaussian_product_law (n d)` in the
  statement): `Data.*`, `SquareFree.Diagonal*`, `SquareFree.EdgeUpper*`,
  `SquareFree.Walk{Moments,Expansion,Bridge,NB,NBEvent,NBRate,NBMoment,NBCount}`,
  `SquareFree.LowerProbability*`, `Column.Concentration*`,
  `Column.RemainderProbability`, `Feature.DiagonalMoment`,
  `Feature.DiagonalLimit`, `Feature.UpperProbability`,
  `Fixed.LowerProbability`, `Gaussian.Sample.Radius*`, `Gaussian.Sample.Residual*`,
  `Gaussian.Spanning.AlmostSure`, `Clipping.*`, `Head.DataLog`, `Head.SelectionLaw`,
  `Head.Law`, `Head.LawBounds`, `Head.Subcritical*`, `Head.CompactTail`,
  `Head.SoftTail`, `Head.SmallBall*`, `Head.WidthRegular`,
  `Head.WidthProbability`, `Head.RegularProbability`, `Soft.Comparison`,
  `Soft.PublicFeatures`, `Soft.ConeMargin`, `Soft.FeatureMargin` (data
  half), `Multirow.*`, `Row.*`, `Joint.*`, `Quadratic.*`,
  `Loss.Replacement`, `Loss.RowIncrement`, `Loss.Replica*`,
  `Loss.Concentration*`, `Hybrid.FiniteMean`, `Hybrid.FiniteTail`,
  `Hybrid.FiniteArray`, `Hybrid.Assembly` (head half),
  `Orientation.Rotation`, `Orientation.Exception`, `Orientation.Prior`,
  `Unsat.*`, `Balanced.*`, `Measurability.*`, `Gaussian.Sample.Deletion`, `Fixed.Density`.
- Gaussian law of auxiliary objects only (the symmetric Gaussian matrix Z
  that defines widths, the GOE surrogate rows G_i, the Gaussian matrices
  A, g, h of the comparison inequalities): `Gaussian.Width.Psd`,
  `Gaussian.Symmetric.DimensionReal`, `Gaussian.Width.Condition*`,
  `Gaussian.Symmetric.{Law,PublicLaw,Reflection}`, `Gaussian.Symmetric.OperatorTail`,
  `Gaussian.Width.SignedSupport`, `Gaussian.Symmetric.FeatureTail`,
  `Gaussian.Tail.Operator`, `Gaussian.Tail.Matrix`, `Gaussian.Symmetric.PublicFeature`,
  `Gaussian.Symmetric.ForwardConstant`, `Gaussian.Lipschitz.EscapeTail`, `Gaussian.Lipschitz.LowerMargin`,
  `Gordon.*`, `Head.Section*`, `Head.Width{Expectation,Approx,Actual}`,
  `Cone.ApproxSelector*`, `Cone.GaussianCoordinates*`, `Projected.*`,
  `Hybrid.Bulk`, `Hybrid.Density`, `Soft.FeatureMargin` (GOE half),
  `Projection.*` (Gaussian comparison of the surrogate rows), and the
  library files `library:comparison.*`, `library:gaussian.*` (statements
  about `gauss n`, an abstract Gaussian vector).
- Distribution-free (no probability measure in the statement):
  `Geometry.*`,
  `Cone.{Condition,ConditionOperator,Kernel,KernelSlice,Projection,ProjectionSupport,HeadTailFit}`,
  `Spectral.*`, `Pinching.*`, `Projection.{Algebra,Blocks,Frobenius,Pinching}`,
  `Matrix.*`, `Tensor.*`, `Polynomial.*`, `Gibbs.*`, `Goe.*`,
  `Analysis.*`,
  `Loss.{Translated,QuadraticPrior,BallNet,JointNet,Empirical,EntropyBudget,LogPolynomial,NormalizedArray,SoftNormalized,Array,Gibbs}`,
  `Orientation.{Net,Family,Spectral,Witness,Blocks,BlocksLoss,Union}`,
  `SquareFree.{EdgeLower,Coercivity,Box,ChebyshevParameters*,WalkCount,WalkExcess,WalkShape*,WalkWeight,WalkNBCore*,WalkNBMarks,LogarithmicGrowth,MatrixFamilyCauchy*}`,
  `Column.Remainder{,Bounds,Cross,Frame,Powers,Recurrence,Scaling,Tolerance}`,
  `Column.ConcentrationCoefficient`, `Column.ConcentrationScaling`,
  `Feature.DiagonalTrace`,
  `Feature.{GramBlocks,SpectralBridge,LossControl,ForwardBound}`,
  `Head.{TailDecomposition*,TailSupport*,Peeling,FamilyCount,CorrectionScale,CorrectionRates,SectionApprox*,FiniteSupportSelector}`,
  `Soft.{Extrema,Lipschitz,ParameterChoice,BlockScoreBounds,BlockThirdBound,MatrixProjectiveBound,MinimaxFrechet,LowerDerivativeBounds,ClippingScale}`,
  `Conditioned.{SupportFit,FromLowerScalars}`,
  `Fixed.{CountBounds,SubcriticalCounts}`, `Asymptotics`,
  `Unsat.{SupercriticalParameters,Rates}`, `library:matrix.*`,
  `library:probability.moments` (abstract probability space), and
  `library:probability.lindeberg` (abstract laws).

## (f) Possible errors and gaps

In the paper (none affects the conclusion):
- Typos: l.1203, eq:Ri-bound has unbalanced bars (`||\cR_i(t)|` for
  `|\cR_i(t)|`); eq:radial-weight (l.1266-1270) writes M_3(F({Z_i(t)}))
  although M_3(F) is a supremum; l.273 calls Lemma 3.9 a proposition;
  l.2061, eq:head-dominating-bound, writes the bulk term as
  C_0 sqrt(n) \|B\|_F^2 where Lemma 4.11 gives C_0 sqrt(n) \|B\|_F, which
  is what the proof uses at l.2229 (eq:case-head) and what the formal proof
  uses; the set I of large residuals is defined with \|u_i\| >= 1 at l.1751
  and with \|u_i\| > 1 at l.2044 and l.2239 (harmless).
- Lemma 2.1 (l.350) is stated for d >= 1, but sqrt(D_d/2 - 1) is not
  defined for d = 1 (D_1/2 - 1 = -1/2). The formal statement holds for
  every d because Stdlib's sqrt is 0 on negative numbers.
- Lemma 2.2, proof (l.395-411): the convergences eq:semicircle-facts are
  cited from the semicircle law without a reference for Tr Z_+/d^(3/2)
  and \|Z_+\|_F^2/d^2, and the uniform integrability argument (l.411) is
  stated, not proved. The formal proof avoids all of it (route R1).
- Lemma 2.6 (l.543): the applicability of Theorem 1.2(2a) of Kogan, Nandy
  and Huang to the square-free degree-two kernel with the given
  normalization is asserted, not checked. The formal proof does not use it
  and proves the lower edge only for n/p^2 <= 1/4, so the paper's claim on
  (1/4, 1/2) remains unverified formally (no error found).
- Proposition 3.3 (l.964, l.1079-1080): the measurable maximum theorem
  gives a measurable selection of the argmax for the fixed compact set;
  the paper then uses it conditionally on the data with P independent of
  the data, which is correct but the independence is implicit. Formally
  this is handled by selectors and `Head.SelectionLaw` (route R5).
- Lemma 4.10 (l.2093-2096, l.2104): the shatter coefficient of unions of
  two half-spaces is bounded by Pi_hs(N)^2, and the exponent p_0^2 n/128
  follows from t = p_0/2 in the VC inequality with n t^2/32. Both correct;
  no issue found.
- Lemma 4.12 (l.2283-2286) claims P(E_U^c) <= exp(-c d^2) uniformly for
  0 <= r <= k_d, but Lemma 4.10 is stated for 1 <= r <= k_d; the case
  r = 0 is handled only inside the proof of Proposition 4.4 (l.2199,
  "after decreasing a_0 if necessary"), where \|b\| sqrt(\|J\|) >= a_0 sqrt(n) \|b\|
  holds since \|J\| >= (1 - delta) n. Fine.
- Proposition 4.3 (l.1716-1733) is stated along one sequence n = n(m), but
  Lemma 4.12 applies it uniformly over r <= k_d (l.2316-2325), so several
  values of n occur for one m. Uniformity follows by taking the worst n
  for each m; the paper does not say so. Remark 4.7 (l.1909-1911) and the
  proof of Proposition 4.5 also rely on the uniformity over offsets that
  depend on the head realization, which follows by conditioning
  (l.2316-2319). No gap.
- Proposition 4.8 (l.1939, l.1955) is only sketched, as a modification of a
  theorem of Bandeira and Maillard that the paper does not reproduce. The
  formal proof gives a complete proof of a statement with the same role
  (route R10).
- The paper does not discuss the measurability of the infima and suprema
  over uncountable sets (E_C, E_(U,H,b), the events of Propositions 4.4
  and 4.5, the widths of data-dependent sections), except at l.964 and
  l.1553. They are measurable, and the formal proof proves the instances
  it uses (route R13).
- The rate exp(-c d^2) claimed for the tail events (l.868, l.1368, eq:conc
  at l.1504) is correct for the paper's radial clipping; the formal proof
  uses another clipping and a weaker rate (route R4). Not an error.

In the formal proof: no gap was found; the kernel checks it. The items
below are gaps between what is proved and what the paper claims, and
cleanup items.
- Lemma 2.6 and Proposition 2.8 are proved only below density 1/4 for the
  lower edge (rows 2.6, 2.8); the paper's uniform statement on (0, 1/2) is
  not formalized. Nothing in the main theorems needs it.
- The constants lambda_-, lambda_+ of Theorem 1.3 exist but are not
  computed (kappa is produced by `Head.SubcriticalFit` through
  `Soft.ParameterChoice` and `Gaussian.Width.ConditionBound` with an
  existential K); likewise the thresholds in d are existential, and some
  inner thresholds are explicit but enormous: d >= 2^9600 in the rate of
  the upper feature edge (EdgeUpperLimit.v:230, WalkNBRate.v:221), d0 of
  order 10^15 in the hybrid gap near gamma = 1/4, 306432 (r + 1)^3 <= n in
  the head small ball (SmallBallUniform.v:647); see (c).
- The formal proof assumes the eight classical axioms of
  `check/assumptions.expected` (excluded middle, functional and
  propositional extensionality, choice, as MathComp-Analysis does); the
  paper's proof is classical as well, so this is not a discrepancy.
- Lemma 2.5 is used in its net form with the constant 20 ln 2 (row 2.5);
  the sharp constants of the paper are in the library but not in the tree
  (no used block references `gauss_opnorm_mean` or `gauss_opnorm_tail`).
- The proof of the paper does not use these library theorems:
  `gordon_escape_tail`, `gauss_opnorm_mean` and `gauss_opnorm_tail` of
  `library/comparison/escape.v` (the forms of Lemmas 2.4 and 2.5 with the
  paper's sharp thresholds), `sudakov_fernique` of
  `library/comparison/slepian.v`, `gauss_interpolation` and
  `gauss_comparison` of `library/gaussian/gauss_interpolation.v`, and
  `lindeberg_replacement` of `library/probability/lindeberg.v`. The
  formal proof uses weaker or specialized forms proved in `theories/`
  instead (rows 2.4, 2.5, 3.9, 4.8; route R10). Nine of the 25 library
  files are not referenced from `theories/` (section "What was
  compared"). This is a duplication, not a gap.
- Module headers that still describe declarations deleted because the
  main theorem does not use them, at `3736fa2`: `Projected.BulkEscape`
  (it names `paper_main_projected_escape_zero` and
  `paper_main_projected_psd_escape`, which no longer exist),
  `Gaussian.Symmetric.DimensionReal` (announces the limit 1/2 and contains only the
  dimension formula), `Gordon.UnitValueBound` and `Gaussian.Lipschitz.LowerMargin`
  (describe a set-index min-max statistic that they no longer define). A
  section comment without declarations below it remains at the end of
  `Hybrid.FiniteMean` ("4. The data mean"). The two lane C items that
  agent 3 listed, the section comment of `Loss.ConcentrationTail` and the
  labels "M119" and "M121" in the header of `Orientation.Spectral`, were
  fixed in commit `3a2cb48` and are gone at `3736fa2`.
