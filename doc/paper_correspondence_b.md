# Correspondence between the paper and the formal proof

Paper: arXiv 2608.10184v1, `/srv/ellipsoid-fitting/papers/2608.10184v1/manuscript.tex`
(2368 lines). Line numbers below refer to this file.

Formal proof: commit `2a06058` of the hub (branch `main` after phase 3), the
tree from which the branch `review/b` was created. Module names are the
logical names of `_CoqProject` (`theories/A/B.v` is `A.B`, `library/x/y.v`
is `GaussianAnalysis.x.y`, written `library:x.y` below). Line numbers of a
formal declaration are the lines of the `.v` file at this commit.

Method. The tree was built with `make build` through the Docker wrapper.
The dependency tree below the two theorems that the frozen file
`PaperMainResults.v` uses, `PaperMainFinalAssembly.paper_main_results_from_conditioned`
and `PaperMainConditionedLimit.paper_main_conditioned_limit`, was computed
from the `.glob` files with the block graph of `scripts/unused.py`
(`Analysis.reach`): a declaration is in the tree when its block is
reachable from a block of the frozen files. The numbers of this section
come from that computation at `2a06058`:

- `theories/`: 605 modules in `_CoqProject`, 5164 declaration blocks
  (`Definition`, `Lemma`, `Theorem`, ... with their proofs); 5156 blocks
  in every one of the 605 modules are in the tree. The 8 blocks outside it
  are the function-level bridge lemmas `RleF`, `RltF`, `INRF`, `RmaxF`,
  `RminF`, `RinvF`, `RdistF`, `lnF` of `Analysis.RealsBridge`.
- The longest chain from the statement to a used declaration has 44
  steps; the modules at distance at most 3 are listed in section (d).
- `library/`: the used blocks of `theories/` reference 109 declarations
  of 16 library files: `matrix.euclidean` (20 declarations),
  `matrix.opnorm` (17), `matrix.real_spectral` (9), `matrix.nets` (4),
  `gaussian.gauss` (5), `gaussian.gauss_ibp` (5),
  `gaussian.measurable_matrix` (5), `comparison.escape` (14),
  `comparison.chi_square` (6), `comparison.gauss_concentration` (4),
  `comparison.gauss_law` (4), `comparison.gordon` (4),
  `comparison.slepian` (4), `comparison.gauss_linear` (3),
  `comparison.gauss_smoothing` (1, a `Require`), `probability.moments`
  (4). The nine other library files (`gauss_interpolation`,
  `gauss_moments`, `partial_derivative`, `normal_integral`, `normal_mgf`,
  `normal_linear`, `gauss_rotation`, `gauss_shift`, `probability.lindeberg`)
  are not referenced from `theories/` (they may be used inside the
  library; the analysis does not follow references between library
  files).

Every statement about a formal declaration was checked on the proof
skeleton of the module (the `.v` file with proofs removed) at `2a06058`,
and the names were checked against the `.glob` index of the build. No
Rocq query was run beyond the build; claims that rest on reading rather
than on the build are marked "(read)". Statements about the paper cite
manuscript lines.

Numbering of the paper. The theorem counter is shared by remarks and the
conjecture, so the numbered results of sections 1.2 to 4 are 1.2 to 1.4,
2.1 to 2.12, 3.1 to 3.5 and 3.8 to 3.15 (3.6 and 3.7 are remarks), 4.1 to
4.6 and 4.8 to 4.12 (4.7 is a remark): 39 rows.

## Table

Relation: `same` means the formal statement implies the paper's statement
in the paper's generality (constants may differ); `weaker` means it covers
less (a smaller range, a special case, or a worse rate that the paper
states explicitly); `stronger` means it covers strictly more; `replaced`
means no formal statement plays the role of this result in the form the
paper gives it, and another statement does its job; `absent` means nothing
in the tree corresponds to it.

| Paper result | Formal counterpart(s) | Relation | Note |
|---|---|---|---|
| Thm 1.2, `thm:main`, §1.2 (l.141) | `MainStatement.main_statement` (MainStatement.v:45), `PaperMainResults.paper_main_results` (PaperMainResults.v:15), `PaperMainFinalAssembly.paper_main_results_from_conditioned` (PaperMainFinalAssembly.v:15) | same | Both phases, with the measurability of the fit event as an extra conclusion (`Measurability.Fit.pm_fit_event_measurable`, Fit.v:372). The density conditions are written out (`PaperMainDefinitions.paper_main_limsup_lt`, `paper_main_liminf_gt`, PaperMainDefinitions.v:140,148). |
| Thm 1.3, `thm:conditioned`, §1.2 (l.151) | `PaperMainConditionedLimit.paper_main_conditioned_limit` (PaperMainConditionedLimit.v:26), `Fixed.Density.paper_main_conditioned_from_fixed` (Density.v:173), `Conditioned.FromLower.paper_main_conditioned_from_lower_exists` (FromLower.v:82) | same | Constants: the formal fit satisfies `(2k+1)^-1 I <= S <= (2k+1) I` for some `k = k(alpha*) >= 1` (`Conditioned.SpectralReduction.paper_main_subcritical_raw_spectral_reduction`, SpectralReduction.v:91); the paper gives `(4 kappa_1^2)^-1`, `4 kappa_1^2` with `kappa_1 = 2 kappa_0` (l.748, l.778). Neither constant is computed. |
| Cor 1.4, `cor:alternative`, §1.2 (l.164) | `Balanced.Probability.paper_main_balanced_from_sat` (Probability.v:61), `Balanced.Limit.paper_main_balanced_supercritical_limit` (Limit.v:29), `Balanced.Supercritical.paper_main_balanced_from_unsat` (Supercritical.v:127), `Measurability.Balanced.pm_balanced_pd_event_measurable` (Balanced.v:385) | same | The formal route uses the exclusion of fit and balanced certificate (`Geometry.Exclusion`), the almost sure spanning for `d <= n` (`Gaussian.Spanning.paper_main_gaussian_spanning_ae`, Spanning.v:85) and `Geometry.Separation.paper_main_fit_alternative` (Separation.v:381), as the paper's l.173 announces. |
| Lem 2.1, `lem:psd-width`, §2.1 (l.350) | `Gaussian.PsdWidth.paper_main_gaussian_psd_projection_second_moment` (PsdWidth.v:81), `paper_main_gaussian_psd_width_bounds` (PsdWidth.v:211), `Cone.Projection.paper_main_psd_moreau` (Projection.v:229) | same | `E |Z_+|_F^2 = D_d/2` and `sqrt(D_d/2 - 1) <= w <= sqrt(D_d/2)` exactly as (l.353, l.357). The cited Prop. 10.2 of [ALMT14] (l.365) is replaced by the Gaussian Poincare bound `Gaussian.WidthVariance.paper_main_gaussian_positive_square_lower` (WidthVariance.v:73) applied to the positive part of the support function (`Cone.ProjectionSupport.paper_main_psd_sphere_support_max`, ProjectionSupport.v:114). |
| Lem 2.2, `lem:widthcone`, §2.1 (l.379) | `Gaussian.ConditionWidthBound.paper_main_gaussian_condition_width_large` (ConditionWidthBound.v:115), `paper_main_gaussian_condition_width_lower` (ConditionWidthBound.v:83), `Cone.Condition.paper_main_cone_shift_scaled` (Condition.v:220) | same | The formal bound is explicit: for every `s > 0`, `w(K_kappa cap S_F) >= (1/2 - s) d - 3 - 864/d` with `kappa = (20 + s)/s` (ConditionWidthBound.v:83). The paper's proof (l.390-417) uses the semicircle law and convergence in probability; the formal proof uses the shift `Z_+ + s sqrt d I` with the operator norm bound `|Z|_op <= 20 sqrt d` outside an event of probability `2 exp(-10 d)` (`Gaussian.SymmetricOperatorTail.paper_main_symmetric_gaussian_operator_good_set`, SymmetricOperatorTail.v:20) and the second moment of the trace. |
| Lem 2.3, `lem:gordon`, §2.2 (l.424) | `Gordon.Width.paper_main_gordon_finite_width_margin` (Width.v:114), `Gordon.SoftMargin.paper_main_gordon_soft_width_margin` (SoftMargin.v:57), `Gordon.Processes.paper_main_gordon_process_comparison` (Processes.v:177), `Gaussian.GordonTail.paper_main_gaussian_lipschitz_lower_margin` (GordonTail.v:33); library `library:comparison.escape.auxT_bilT_minmax` (escape.v:409, used by `Gordon.Processes`), itself from `library:comparison.gordon.gordon` (gordon.v:648) | replaced | The tail inequality for a compact index set `T` with the constant `2 exp(-t^2/4)` (l.427-431) is not proved. The formal proof uses Gordon's comparison in expectation for finite families of unit vectors (`E min_y max_t z_y^T A v_t >= E sup_t <h, v_t> - sqrt N`, Width.v:114, with `sqrt N` in place of `E|g_N|`), its soft version with the entropy loss `ln r / beta` (SoftMargin.v:57), nets to pass from finite families to sets (`Gordon.Nets.paper_main_gordon_net_width_error`, Nets.v:76), and Gaussian concentration of a Lipschitz function for the tail (GordonTail.v:33, bound `exp(-u^2/(2 L^2))`). |
| Lem 2.4, `lem:escape`, §2.2 (l.478) | `Gaussian.EscapeTail.paper_main_gaussian_escape_sqrt_tail` (EscapeTail.v:18), `Gordon.EscapeExpectation.paper_main_gordon_escape_expectation` (EscapeExpectation.v:115); library `library:comparison.escape.gordon_escape` (escape.v:603, used by `Gordon.EscapeExpectation`) | same | Proved, with `sqrt(N - 1)` in place of `E|g_N|` (the paper uses the same lower bound, l.491) and the bound `exp(-u^2/2)`, from the library's expectation form and the concentration of row 2.3. The library's tail form `gordon_escape_tail` (escape.v:684) keeps the exact mean but is not referenced by the tree. |
| Lem 2.5, `lem:gauss-rect`, §2.2 (l.495) | `Gaussian.OperatorTail.paper_main_gaussian_operator_tail` (OperatorTail.v:74), `Gaussian.FeatureTail.paper_main_gaussian_operator_exponential_tail` (FeatureTail.v:45); library `library:comparison.escape.gauss_opnorm_tail` (escape.v:847) | weaker | The formal proof uses a net bound: `P(|A|_op > 2 B) <= 2 exp(20 ln 2 (N + M) - B^2/2)` (OperatorTail.v:74), that is `|A|_op <= 2 sqrt(2 (20 ln 2 (N + M) + t))` outside probability `2 exp(-t)`, instead of the sharp `sqrt N + sqrt M + t` of (l.499). The library proves the sharp form (escape.v:847), but no used block references `gauss_opnorm_mean`, `gauss_opnorm_tail` or `gauss_opnorm_mean_sqrt`. |
| Lem 2.6, `lem:squarefree-edge`, §2.3 (l.521) | `SquareFree.LowerProbability.paper_main_squarefree_lower_probability` (LowerProbability.v:36), `SquareFree.EdgeUpperLimit.paper_main_squarefree_upper_bound` (EdgeUpperLimit.v:361), `paper_main_squarefree_upper_event_tends_to_zero` (EdgeUpperLimit.v:303), `SquareFree.Coercivity.paper_main_squarefree_coercivity` (Coercivity.v:141) | weaker | No limits `(1 -+ sqrt(2 rho))^2` (l.525-529). Upper edge: `V V^T <= 106 d^2 I` with probability tending to one for `0 < N <= d^2` (EdgeUpperLimit.v:361). Lower edge: only through the full raw Gram, `Q Q^* >= (d^2/128) I`, under `4 N <= d^2` and `d^2 <= c_1 N` (LowerProbability.v:36), that is for densities in `[c, 1/4]`, not on the paper's compact `K subset (0, 1/2)`. Both are self-contained (no [KNH25]). |
| Lem 2.7, `lem:diagonal-feature-block`, §2.3 (l.564) | `DiagonalBlock.Limit.paper_main_diag_trace_event_bound` (Limit.v:63), `paper_main_diag_trace_event_markov` (Limit.v:85), `paper_main_diag_block_tends_to_zero` (Limit.v:209), `DiagonalBlock.Moment.paper_main_diag_trace_moment` (Moment.v:868) | same | `D^T D <= 3 N I` and `D D^T <= 3 N I` outside an event of probability at most `(N (2^21 d^4 + 16 d) + 3 N (N - 1) d (4 d + 52)^2) / N^4`, which is `O(1/d)` when `N >= c d^2`. The matrix Bernstein inequality (l.585) is replaced by the fourth trace moment `E tr (D^T D - 2 N I)^4` and Markov. No truncation. |
| Prop 2.8, `prop:feature-edge`, §2.3 (l.594) | lower: as Lem 2.6; upper: `Feature.UpperProbability.paper_main_feature_upper_edge` (UpperProbability.v:54), `paper_main_feature_upper_event_bound` (UpperProbability.v:23), `Feature.GramBlocks.paper_main_feature_gram_blocks` (GramBlocks.v:118); Gaussian map: `Gaussian.PublicFeature.paper_main_public_gaussian_feature_exceptional_event` (PublicFeature.v:40), `Gaussian.Forward.paper_main_gaussian_forward_threshold` (Forward.v:27) | weaker | Upper edge `Q Q^* <= (3 N + 106 d^2) I <= 109 d^2 I` for `N <= d^2` with probability tending to one (UpperProbability.v:23, 54): same as (l.597) for every density at most 1. Lower edge only for `n/p^2 <= 1/4` (row 2.6). The GOE map bound `|G|_{F -> 2} <= C sqrt N` is proved with the net constant of row 2.5 outside probability `2 exp(-N/2)` (PublicFeature.v:40 at `t = N/2`, Forward.v:27). |
| Cor 2.9, `cor:feature-sat`, §2.3 (l.624) | `Feature.SpectralBridge.paper_main_raw_feature_coercive` (SpectralBridge.v:57), `paper_main_raw_feature_upper` (SpectralBridge.v:75), `Conditioned.SpectralReduction.paper_main_subcritical_raw_spectral_reduction` (SpectralReduction.v:91) | weaker | The normalization `W_i = Q_i/sqrt d` gives `c d I <= W W^* <= C d I` from the raw bounds (SpectralBridge.v:57, 75), with `c = 1/128`, `C = 109`. Proved for `rho_* < 1/4` only, which is the only range the satisfiable phase uses. |
| Lem 2.10, `lem:data`, §2.4 (l.636) | radius: `Gaussian.DataRadius.paper_main_data_radius_good` (DataRadius.v:217), `paper_main_data_radius_probability` (DataRadius.v:128); coordinates: `Data.SampleTail.paper_main_data_coordinate_tail` (SampleTail.v:109); coherence: `Data.CoherenceLimit.paper_main_data_coherence_log_good` (CoherenceLimit.v:104), `paper_main_data_coherence_log_tail` (CoherenceLimit.v:45); sparse norms: `Head.DataLog.paper_main_head_data_log_event` (DataLog.v:28) | same | (l.639): `|x_i|_2^2 <= 4 d` outside probability `N exp(-d/2)`. (l.641): the general tail `2 N d exp(-u^2/2)` is proved; the tree uses it at `u = d^(1/4)` (`Clipping.Limits.paper_main_coordinate_clipping_tends_to_zero`, Limits.v:75), not at `sqrt(C log d)`. (l.643): `|<W_i, W_j>| <= 73 ln d` outside probability `2 N^2/d^8`. (l.645): `X_J X_J^T <= L d (ln d)^2 I` for all `|J| <= K d ln d` outside probability `2/d`, by nets (`Data.HeadOperatorUniform`). |
| Lem 2.11, `lem:hw`, §2.4 (l.660) | `Gaussian.QuadraticTail.paper_main_gaussian_quadratic_tail` (QuadraticTail.v:57), `Gaussian.Residual.paper_main_gaussian_residual_tail` (Residual.v:84); library `library:comparison.chi_square.gauss_centered_chi2_abs_tail` (chi_square.v:351) | same | Gaussian case only (the paper's statement is for Gaussian `x`, l.661). Explicit: `P(|x^T P x - Tr P| >= u) <= 2 exp(-u^2 / (4 |P|_F^2 + 4 |P|_op u))`, which is the paper's form with `c = 1/8`. Proved by diagonalization and the chi-square moment generating function, not by [RV13]. |
| Lem 2.12, `lem:homogeneous`, §2.4 (l.677) | (i): `Geometry.Homogeneous.paper_main_homogeneous_kernel` (Homogeneous.v:132), `paper_main_homogeneous_witness` (Homogeneous.v:162); (ii): `Geometry.Separation.paper_main_homogeneous_alternative` (Separation.v:368), `paper_main_homogeneous_existence` (Separation.v:332), `Geometry.Exclusion.paper_main_fit_balanced_exclusive` (Exclusion.v:58), `paper_main_fit_alternative` (Separation.v:381) | same | (i): for `d > 0` and a spanning sample, fit iff some nonzero `S >= 0` has all `x_i^T S x_i` equal (Homogeneous.v:132), and this iff some `S >= 0` with `|S|_F = 1` and real `b` has `x_i^T S x_i - Tr S = b` for all `i` (Homogeneous.v:162, no spanning needed). (ii): one alternative holds for every sample (Separation.v:368) and not both (Exclusion.v:58). Same variational proof as (l.706-715), on the trace-one slice. |
| Thm 3.1, `thm:sat`, §3 (l.743) | `PaperMainConditionedLimit.paper_main_conditioned_limit` (PaperMainConditionedLimit.v:26), `paper_main_conditioned_fixed_limit` (PaperMainConditionedLimit.v:14), `Head.SubcriticalFit.paper_main_head_subcritical_fit_exception` (SubcriticalFit.v:34), `Cone.HeadTailFit.paper_main_cone_head_tail_conditioned_fit` (HeadTailFit.v:61) | same | The padding to `n = floor(alpha d^2)` (l.752-757) is `Fixed.Density.paper_main_eventual_padding` (Density.v:124) with the monotonicity `Fixed.Density.paper_main_conditioned_probability_antitone` (Density.v:78) from `Sampling`. Constants as in row 1.3. |
| Lem 3.2, `lem:convex-separation`, §3.1 (l.792) | `Cone.Kernel.paper_main_cone_kernel_exists_support` (Kernel.v:217), `paper_main_cone_kernel_exists` (Kernel.v:141), `Cone.KernelSlice.paper_main_cone_kernel_slice_compact` (KernelSlice.v:123), `Conditioned.SupportFit.paper_main_cone_kernel_conditioned_fit` (SupportFit.v:37) | replaced | The paper separates `0` from the convex set `W(B)` for the box `B = {1/(2 kappa_1) I <= S <= 2 kappa_1 I}` (l.795). The formal proof works on the cone sphere `K_kappa cap S_F` (`Geometry.HeadWidth.paper_main_head_cone_sphere`, HeadWidth.v:35): if `sup_{P in K_kappa cap S_F} <sum_i y_i W_i, P> > 0` for every unit `y`, then some `P` on the cone sphere is orthogonal to every `W_i` (Kernel.v:217), by minimizing `sum_i <W_i, S>^2` on the compact trace-one slice of the cone and reading the minimizer as a kernel element. Such a `P` gives the conditioned event with `kappa^-1 I <= S <= kappa I` after scaling (SupportFit.v:37). |
| Prop 3.3, `prop:heads`, §3.1 (l.834) | `Head.RegularProbability.paper_main_head_width_coercive_probability_uniform` (RegularProbability.v:161), `paper_main_head_width_coercive_probability_fixed` (RegularProbability.v:75), `Head.WidthProbability.paper_main_head_width_regular_probability_fixed` (WidthProbability.v:35), `Head.WidthRegular.paper_main_head_width_regular_transfer` (WidthRegular.v:56), `Head.WidthActual.paper_main_head_width_actual_selected` (WidthActual.v:79) | same | For every `eps > 0` some `kappa >= 1` works for every `N <= C d^2`: outside a vanishing event, if the head Gram is coercive with constant `c d`, every selection of `m <= K d ln d` rows has section width at least `(1/2 - eps) d` (RegularProbability.v:161). This is (l.838-840) with the width of `K_{kappa_0}` replaced by its lower bound (row 2.2) and the paper's `kappa_1 = 2 kappa_0` replaced by `2 k_0^2` (RegularProbability.v:90). The coercivity (row 2.9) is a hypothesis here and is discharged in `Conditioned.SpectralReduction`. The maximizer `P(Z)` of (l.962) is replaced by a measurable finite-net selector (section (a)). |
| Prop 3.4, `prop:lowinf`, §3.1 (l.858) | `Head.SubcriticalProbability.paper_main_head_subcritical_probability` (SubcriticalProbability.v:36), `Head.SubcriticalFamily.paper_main_head_subcritical_family_event` (SubcriticalFamily.v:29), `Head.SubcriticalGood.paper_main_head_subcritical_selected_good` (SubcriticalGood.v:35), `Head.SubcriticalEvent.paper_main_head_subcritical_bad` (SubcriticalEvent.v:34) | same | For `alpha < 1/4`, `kappa >= 1`, `L >= 0` there is `theta > 0` such that for every `K`, outside a vanishing event, every head `J` with `|J| <= K d ln d` and section width at least `(1/2 - g/16) d`, `g = 1/2 - sqrt alpha`, has `paper_main_head_list_positive` (SubcriticalFixed.v:42): every unit tail vector capped by `theta/sqrt d` has a positive score at some section element. The margin behind it is `(g/4) sqrt d` on the Frobenius unit sphere (SubcriticalEvent.v:43-44), the paper's `c_* d` on `D_J = sqrt d (...)` (l.863). |
| Lem 3.5, `lem:regularity`, §3.1 (l.872) | `Head.TailDecompositionLog.paper_main_head_tail_regularity` (TailDecompositionLog.v:139), `Head.TailDecomposition.head_tail_decomposition_explicit` (TailDecomposition.v:61), `Head.Peeling.peeling_iteration` (Peeling.v:142) | same | Explicit constant `C_theta = 16 / (theta^2 ln 2)` (TailDecompositionLog.v:27: `head_tail_constant`). Same peeling as (l.882-886). |
| Lem 3.8, `lem:head-correction-bounds`, §3.2 (l.970) | `Head.WidthActual.paper_main_head_width_actual_selected` (WidthActual.v:79), `Geometry.HeadSpectral.paper_main_head_correction_bounds_cone` (HeadSpectral.v:162), `Geometry.HeadCorrection.paper_main_head_condition_transfer` (HeadCorrection.v:283), `paper_main_head_support_transfer` (HeadCorrection.v:176), `Head.CorrectionScale.paper_main_head_correction_eventual` (CorrectionScale.v:133) | same | Deterministic correction `a_J = Q_J^-1 r_J`, `E_J = -W_J^* a_J` (`Geometry.HeadCoefficients`), with the bounds (l.996-1034) in parametrized form (WidthActual.v:99-104: `m r^2 <= mu eta^2`, `m r <= mu A_1`, `r + q_1 A_1 <= q_0 A_inf`, `(A_inf lam + A_1)/sqrt d <= delta`). Weyl's inequality (l.1042) is replaced by Loewner boxes (HeadCorrection.v:283). The rates are chosen with `t = d^(1/32)` (`Head.CorrectionScale`, CorrectionScale.v:139-142) instead of the paper's powers of `log d`. |
| Lem 3.9, `lem:interpolation`, §3.3 (l.1150) | `Soft.Comparison.paper_main_soft_public_comparison` (Comparison.v:92), `Soft.PublicFeatures.paper_main_public_feature_soft_comparison` (PublicFeatures.v:137), `Multirow.IntegratedBound.paper_multirow_integrated_bound_results` (IntegratedBound.v:35) | weaker | Proved only for `F` the soft minimax `Phi` of (l.1287-1293), not for every `C^3` `F`: `|E Phi(W) - E Phi(G)| <= (40/3) k^3 (beta + gamma)^2 theta (d + 2 sqrt(d ln N) + 2 ln N) / d^2` (Comparison.v:107). This is (l.1160) with `M_3` replaced by its bound of row 3.12 and `R_{N,d}` by row 3.11. The interpolation path and the cancellation of the divergence terms are `Multirow.*` and `Joint.*`. |
| Lem 3.10, `lem:chaos-ibp`, §3.3 (l.1186) | `Multirow.FullStein.paper_multirow_full_stein_results` (FullStein.v:24), `Row.ConditionalStein` (gaussian_row_full_stein_of_regular), `Gaussian.LawBridge.gaussian_iterated_coordinate_second_stein_gauss` (LawBridge.v:351); library `library:gaussian.gauss_ibp.gauss_ibp2` (gauss_ibp.v:509) | same | The identity `E[velocity_i] = sqrt t/(2 d sqrt d) E[remainder_i]` is proved for the soft minimax observables (FullStein.v:36-40) from the second-order Stein identity `E[(x_a x_b - delta_ab) f] = E[d_a d_b f]` (LawBridge.v:351, from gauss_ibp.v:509), as in the paper's proof (l.1208). The remainder bound (l.1203) is `Multirow.IntegratedBoundSteps.multirow_integrated_remainder_sum_bound` (IntegratedBoundSteps.v:68). |
| Lem 3.11, `lem:max-radius`, §3.3 (l.1235) | `Radius.ExpectedMaximum.gaussian_maximum_radius_expected_bound` (ExpectedMaximum.v:109), `Radius.ExpectationBound.gaussian_expected_maximum_radius` (ExpectationBound.v:52) | same | Identical bound `d + 2 sqrt(d ln N) + 2 ln N`, same proof (chi-square moment generating function and Jensen, `Radius.ExponentialMoments`). |
| Lem 3.12, `lem:soft`, §3.3 (l.1295) | `Soft.Extrema.soft_minimax_bounds` (Extrema.v:177), `Soft.MatrixProjectiveBound.soft_matrix_projective_sum_bound` (MatrixProjectiveBound.v:48), `Soft.BlockThirdBound.lower_block_third_bound` (BlockThirdBound.v:27) | same | Sandwich (l.1298-1302) as Extrema.v:177; third-derivative sum `<= 10 k^3 (beta + gamma)^2 theta / sqrt d` (MatrixProjectiveBound.v:57-58), the paper's (l.1304-1306) with `C = 10`. The projective norm is `Tensor.ProjectiveNormBounds` (read). |
| Lem 3.13, `lem:gaussian-soft-head`, §3.4 (l.1436) | `Soft.FeatureMargin.paper_main_public_goe_soft_margin` (FeatureMargin.v:117), `Gordon.SoftMargin.paper_main_gordon_soft_width_margin` (SoftMargin.v:57), `Head.SectionApproxWidth.paper_main_head_section_approx_width_exists` (SectionApproxWidth.v:133) | replaced | The conditional tail (l.1440-1445) with `exp(-c d^2)` and the second-moment argument (l.1458-1470) are not proved. The expectation bound (l.1447) is obtained directly: `E Phi(G) >= sqrt(2/d) (w(net) - sqrt N) - ln r / beta` (FeatureMargin.v:122-128), with `w(net)` the Gaussian width of the net of section elements, from Gordon's comparison in expectation. |
| Cor 3.14, `cor:chaos-soft-head`, §3.4 (l.1473) | `Soft.ConeMargin.paper_main_data_soft_cone_margin` (ConeMargin.v:44), `Head.SoftTail.paper_main_head_soft_expectation` (SoftTail.v:91), `Soft.ParameterChoice.paper_main_soft_scaled_margin` (ParameterChoice.v:83), `paper_main_soft_parameters` (ParameterChoice.v:29) | same | `E_W Phi >= sqrt(2/d)(w - sqrt N) - ln r/beta - (200/3) kappa^3 (beta + gamma)^2 theta / (d^2 sqrt d)` (ConeMargin.v:54-58), then at `beta = gamma = A d sqrt d` the level `((1/2 - sqrt alpha)/2) sqrt d` on the unit sphere (ParameterChoice.v:93). The order of the constants `(eps, A, theta)` is ParameterChoice.v:29. |
| Lem 3.15, `lem:clipped-soft-heads`, §3.4 (l.1501) | `Head.SubcriticalTail.paper_main_head_subcritical_clipped_tail` (SubcriticalTail.v:55), `Head.CompactTail.paper_main_head_compact_clipped_tail` (CompactTail.v:65), `Head.SoftTail.paper_main_head_soft_clipped_lower_tail` (SoftTail.v:116), `Data.SoftConcentration.paper_main_data_soft_clipped_lower_margin` (SoftConcentration.v:119), `Head.SubcriticalFamily.paper_main_head_subcritical_family_event` (SubcriticalFamily.v:29), `Clipping.Limits.paper_main_clipped_head_union_tends_to_zero` (Limits.v:116) | weaker | The paper clips rows radially at `2 sqrt d` (l.1498) and gets `exp(-c d^2)` (l.1506). The formal proof clips every coordinate at `d^(1/4)` (`Gaussian.LipschitzClip`, `Data.Clipped`), gets Lipschitz constant `2 (kappa/sqrt d) d^(1/4)` and the tail `exp(-c d sqrt d)` (SubcriticalTail.v:75-76); the union over the `exp(C d (ln d)^2)` heads (`Head.FamilyCount.paper_main_head_families_exp`, FamilyCount.v:98) still vanishes (Limits.v:116). The clipping error of the mean (l.1544-1550) is `Data.SoftConcentration.paper_main_data_soft_clipping_mean` (SoftConcentration.v:57). |
| Thm 4.1, `thm:unsat`, §4 (l.1613) | `Unsat.Limit.paper_main_unsat_supercritical_limit` (Limit.v:259), `paper_main_unsat_fixed_density_limit` (Limit.v:242), `Fixed.Density.paper_main_unsat_from_fixed` (Density.v:231) | same | The trimming to `n = floor(gamma d^2)` (l.1621-1631) is Density.v:231 with `Fixed.Density.paper_main_eventual_trimming` (Density.v:142). |
| Lem 4.2, `lem:homogeneous-witness`, §4.1 (l.1639) | `Pinching.Loss.paper_main_fit_unit_witness` (Loss.v:16), `Geometry.Homogeneous.paper_main_homogeneous_kernel` (Homogeneous.v:132), `paper_main_homogeneous_witness` (Homogeneous.v:162) | same | Fit implies a witness `S >= 0`, `|S|_F = 1`, `Q_x(S) = b 1` for `N, d > 0` without spanning (Loss.v:16); the equivalence under spanning is the composition of Homogeneous.v:132 and 162 (row 2.12). The formal unsatisfiable phase uses only the first direction. |
| Prop 4.3, `prop:translated-univ`, §4.1 (l.1716) | `Hybrid.FiniteMean.paper_main_hybrid_finite_mean_comparison` (FiniteMean.v:100), `paper_main_hybrid_finite_row_comparison` (FiniteMean.v:41), `Loss.Replacement.paper_main_loss_array_comparison` (Replacement.v:62), `Loss.RowIncrement.paper_main_loss_row_increment_comparison` (RowIncrement.v:119) | replaced | No limit `m -> oo` and no infimum over a closed set `C_m` (l.1724-1730). The formal statement compares, for a finite list `I` of candidates `(H_j, b_j, B_j)` with `B_j` symmetric, `|B_j|_op <= eps` and `|B_j|_F <= S_f`, the soft minimum (inverse temperature `beta`) of the normalized empirical risks under chaos rows and under GOE rows: `|E Z_data - E Z_goe| <= 2 eta + C eps S_f` for every `eta > 0`, with `C = C(beta, eta)` (FiniteMean.v:100-112). The bulk cutoff `eps` is a constant, not `d^(-1/4)`. |
| Prop 4.4, `prop:hybrid-gap`, §4.1 (l.1739) | `Hybrid.Assembly.paper_main_hybrid_gap_event` (Assembly.v:134), `paper_main_hybrid_gap_event_joint` (Assembly.v:364), `Hybrid.Loss.paper_main_hybrid_risk_gap` (Loss.v:129), `Hybrid.Residual.paper_main_hybrid_residual_gap` (Residual.v:330) | stronger | Outside an event of probability `exp(-c d^2)`, the risk is at least `e` for all symmetric `H`, PSD `B` and real `b` with `|H|_F^2 + |B|_F^2 >= 1/4` (Assembly.v:148-152): no upper bound `4` (l.1746), `H` need not be PSD, and `r <= sqrt d + 1` (Assembly.v:140) instead of `r <= ceil(sqrt d)`. |
| Prop 4.5, `prop:true-net-gap`, §4.1 (l.1804) | `Orientation.Union.paper_main_orientation_union_fit` (Union.v:118), `Orientation.Exception.paper_main_orientation_exception` (Exception.v:51), `Unsat.FiniteTail.paper_main_unsat_ordered_tail` (FiniteTail.v:41), `Unsat.Orientation.paper_main_unsat_orientation_constants` (Orientation.v:32), `Orientation.Family.paper_main_orientation_family_uniform` (Family.v:97) | replaced | The net `I_d` of (l.1796) and the bound `e_gamma/4` on the infimum over `C_U(H)` (l.1810) are not formalized. Instead: for every orientation `O` (orthogonal matrix) and rank `r <= 1/eps_0^2`, an event of probability at most `exp(-N (e/4)^2/2)` contains every sample whose Gram matrix is bounded and which admits an admissible candidate `(A, b)` for `O` of quadratic risk at most `16 L tau` (Orientation.v:37-47); the union over a net of orientations in projector distance (`Orientation.Net`, Net.v:201, entropy `(4 + 8 r/tau) ln 2 (r + 1)(d + 1)`) and over `r` contains every fit (Union.v:118). |
| Lem 4.6, `lem:transport`, §4.1 (l.1818) | `Pinching.Loss.paper_main_pinching_witness_risk` (Loss.v:28), `Orientation.Witness.paper_main_orientation_fit_witness` (Witness.v:103), `Pinching.Annulus.paper_main_pinching_annulus` (Annulus.v:47), `Pinching.Loss.paper_main_pinching_cutoff_bulk` (Loss.v:68) | replaced | No orthogonal transport `O` with `|O - I|_op <= C tau` (l.1819-1821). The witness `S` is pinched by the net projector `U`: `U S U + (I - U) S (I - U)` has quadratic risk at most `16 L tau` when `|U - P|_F <= tau` (Loss.v:28), Frobenius norm in `[1/2, 2]` (Loss.v:58) and bulk operator norm at most `eps_0 + tau^2` (Loss.v:68). |
| Prop 4.8, `prop:finite-prior-free-entropy`, §4.2 (l.1944) | `Loss.Replacement.paper_main_loss_array_comparison` (Replacement.v:62), `Loss.RowIncrement.paper_main_loss_row_increment_comparison` (RowIncrement.v:119), `Loss.ReplicaComparison.paper_main_loss_replicated_comparison` (ReplicaComparison.v:123), `Loss.LogPolynomial.paper_main_loss_log_remainder` (LogPolynomial.v:57), `Loss.BlockComparison.paper_main_loss_conditional_prefix_comparison` (BlockComparison.v:38), `Projection.PublicOperator.paper_main_projection_public_comparison` (PublicOperator.v:54), `Projection.Comparison.paper_main_projection_smooth_comparison` (Comparison.v:69) | replaced | [BM25, Thm 4.6] (l.1955) is not used. The expectation of the soft minimum over the finite prior is compared row by row (Lindeberg replacement proved in `Loss.Replacement` from the block comparison BlockComparison.v:38; the library's `lindeberg_replacement` is not referenced), and each row increment is compared through the expansion of `-ln` of the Gibbs factor into a polynomial (LogPolynomial.v:57, `Loss.Replica`) whose terms are Gibbs replica averages of products of the loss factors, compared by the fixed-dimensional smooth comparison of centered quadratic forms with Gaussian linear forms of the same covariance (PublicOperator.v:54: error `K^2 2 C eps S` for a `C^2` test of `K` features), proved by the square-root interpolation and the Stein identities of `Projection.*` and `Gaussian.CovarianceDerivative` (the library's `gauss_interpolation` is not referenced). The result is an explicit bound `2 eta + C eps S_f` per row (RowIncrement.v:125-130), uniform in the offsets and the prior. |
| Lem 4.9, `lem:ground-state-transfer`, §4.2 (l.1962) | `Orientation.Prior.paper_main_orientation_prior` (Prior.v:48), `Loss.QuadraticPrior.paper_main_quadratic_prior_positive` (QuadraticPrior.v:63), `Orientation.BlocksLoss.paper_main_orientation_candidate_bound` (BlocksLoss.v:135), `Loss.JointNet.paper_main_loss_joint_net` (JointNet.v:49) | replaced | No `limsup_m` and no `C delta + (C/beta) log(1 + 2 C_0/delta)` (l.1968-1969). A finite prior of admissible candidates of size `ln s <= 3 C(delta/(L + 3)) d^2` approximates the risk of every admissible `(A, b)` within `4 (L + 1) delta` (QuadraticPrior.v:69-76); the soft minimum over it is at most the minimal risk plus `ln s/(beta N)` (BlocksLoss.v:140-141), so the finite-prior functional of a fit is at most `16 L tau + 4 (L + 1) delta + ln s/(beta N)` (Prior.v:63-65). |
| Lem 4.10, `lem:head-smallball`, §4.3 (l.2072) | `Head.SmallBallUniform.paper_main_head_small_ball_uniform_poly` (SmallBallUniform.v:646), `paper_main_head_small_ball_uniform` (SmallBallUniform.v:482), `Head.SmallBallPZ.paper_main_head_small_ball_probability` (SmallBallPZ.v:189), `Head.SmallBallFourth.paper_main_head_small_ball_moments` (SmallBallFourth.v:349), `Head.SmallBallCount.paper_main_head_row_count_lower_exp` (SmallBallCount.v:379), `Head.SmallBallNet.paper_main_head_small_ball_param_net` (SmallBallNet.v:200); library `library:probability.moments.paley_zygmund` (moments.v:85) | same | For `306432 (r + 1)^3 <= m`, outside an event of probability `exp(-((2 ln 2 - 1)/2432) m)`, every symmetric `H`, real `b` and `J` with `|J| >= (1 - 1/1216) m` satisfy `sum_{i in J} (g_i^T H g_i - Tr H - b)^2 >= (m/4864)(2 |H|_F^2 + b^2)` (SmallBallUniform.v:646-656): the paper's (l.2075) with `a_0^2 = 1/4864`, `delta_0 = 1/1216`. Hypercontractivity (l.2088) is replaced by the computed fourth moment `E Y^4 <= 19 (E Y^2)^2` (SmallBallFourth.v:355), so Paley-Zygmund gives `1/76` instead of `1/324`; the VC inequality (l.2098) is replaced by a net of parameters and binomial tail bounds on row counts. |
| Lem 4.11, `lem:projected-bulk-escape`, §4.3 (l.2126) | `Hybrid.Bulk.paper_main_hybrid_bulk_event` (Bulk.v:29), `Projected.BulkConditional.paper_main_projected_psd_conditional_tail` (BulkConditional.v:949), `Projected.BulkEscape.paper_main_projected_escape_tail` (BulkEscape.v:37), `Projected.BulkUnion.paper_main_projected_count_entropy` (BulkUnion.v:105), `Projected.BulkLaw.paper_main_projected_law` (BulkLaw.v:186), `Hybrid.Assembly.paper_main_hybrid_operator_event` (Assembly.v:39) | same | Lower bound `c d |B|_F` for all PSD `B` and all `J` with `|J| >= (1 - delta) N`, conditionally on the head, outside probability `exp(-c_2 d^2)` (Bulk.v:59-67); the union over `J` costs `exp(k (1 + ln(N/k)))` (BulkUnion.v:105) instead of `exp(n H_2(delta))` (l.2171). The upper bound `|R(B)|_2 <= C sqrt N |B|_F` is Assembly.v:39-47 from the GOE operator bound of row 2.8. |
| Lem 4.12, `lem:conditional-true-mean-gap`, §4.4 (l.2282) | `Hybrid.FiniteMean.paper_main_hybrid_finite_goe_mean` (FiniteMean.v:177), `paper_main_hybrid_finite_mean_comparison` (FiniteMean.v:100), `Loss.ExpectedGap.paper_main_loss_expected_gap` (ExpectedGap.v:22), `Hybrid.FiniteTail.paper_main_hybrid_finite_data_lower_tail` (FiniteTail.v:35), `Unsat.FiniteTail.paper_main_unsat_ordered_tail` (FiniteTail.v:41) | replaced | No conditioning on the head and no head event `E_U` (l.2284-2288). The expectation of the finite-prior functional under the joint law of head and GOE bulk is at least `e (1 - exp(-c d^2))` (FiniteMean.v:191-193), the comparison of row 4.3 transfers it to the data, and the lower tail `exp(-N t^2/2)` (FiniteTail.v:35-46) replaces McDiarmid (l.2330-2335). |

## (a) Results the paper cites without proof, and what the formal proof does

- Gordon's min-max comparison [Gor85], finite-index form (l.448-454): proved in
  the library as `library:comparison.gordon.gordon` (gordon.v:648) and
  `gordon_cov` (gordon.v:771), for expectations of `min_u max_t` of two
  centered Gaussian arrays, by interpolation of the smooth min-max
  `smm` (gordon.v, read). The bilinear instance `min_z max_v z^T A v`
  against `<g, z> + <h, v>` is `library:comparison.escape.auxT_bilT_minmax`
  (escape.v:409), the only entry point of this comparison that the tree
  references (from `Gordon.Processes`); `aux_bil_minmax` (escape.v:335)
  and the Sudakov-Fernique inequality for the maximum
  (`library:comparison.slepian.sudakov_fernique`, slepian.v:389) serve
  inside the library for the escape and operator-norm results. The tail
  form of Lem 2.3 is obtained from the expectation by Gaussian
  concentration (row 2.3).
- Escape through a mesh [Gor88] (l.478): `library:comparison.escape.gordon_escape`
  (escape.v:603, referenced by `Gordon.EscapeExpectation`) and
  `gordon_escape_tail` (escape.v:684, not referenced), from the same
  comparison and nets (`library:matrix.nets.net_exists`, nets.v:403).
- Second-chaos interpolation and Gaussian comparison with matching
  covariances (l.1254-1275, l.1955): the library's
  `library:gaussian.gauss_interpolation.gauss_interpolation`
  (gauss_interpolation.v:345) and `gauss_comparison`
  (gauss_interpolation.v:417) are general statements for `C^2` tests of
  Gaussian vectors, but the tree does not reference them. The theories use
  their own interpolation calculus (`Gaussian.InterpolationCoefficients`,
  `Gaussian.CovarianceDerivative`, `Multirow.*`, `Projection.*`), and the
  law statement `library:comparison.gauss_law.gauss_mulmx_law`
  (gauss_law.v:569) through `Gaussian.CovarianceBounds.paper_main_covariance_equal_expectation`
  (CovarianceBounds.v:81) and `gauss_orthogonal_law` (gauss_law.v) through
  `Projected.BulkLaw`.
- Rectangular Gaussian matrices [Ver18, 7.3.1] (l.495): the library proves
  the sharp mean bound `E |G|_op <= E|g| + E|h|` and its tail
  (`gauss_opnorm_mean`, escape.v:778; `gauss_opnorm_tail`, escape.v:847)
  by Sudakov-Fernique; the tree uses the coarser net bound of
  `Gaussian.OperatorTail` (row 2.5).
- Gaussian concentration for Lipschitz functions [BLM13, 5.6] (l.469,
  l.1551): `library:comparison.gauss_concentration.gauss_concentration`
  (gauss_concentration.v:930), Herbst's argument with the sharp constant,
  through `Gaussian.LipschitzConcentration` (LipschitzConcentration.v:42).
- The width-dimension inequalities of [ALMT14, Prop. 10.2] (l.365): the
  Gaussian Poincare inequality for Lipschitz functions
  (`library:comparison.gauss_concentration.gauss_poincare_lipschitz`,
  gauss_concentration.v:1124) applied to the positive part of the support
  function (`Gaussian.WidthVariance`, row 2.1).
- The semicircle law and operator norm convergence [AGZ10] (l.390-401):
  not used; row 2.2.
- Extreme eigenvalues of kernel matrices [KNH25, 1.2(2a)] (l.543): not
  used; replaced by a self-contained moment method. Upper edge: the
  expectation of `tr W^L` of the off-diagonal part of `V V^T` is a sum
  over closed walks (`SquareFree.WalkExpansion`), each weighted by a
  Gaussian moment bounded through the multiplicity excess
  (`SquareFree.WalkWeight`, `SquareFree.WalkExcess`); the walks are counted
  by a twin code (`SquareFree.WalkShapeCode`, `WalkShapeOnce`,
  `WalkShapeBound`), giving `E tr W^L <= N (52 d^2)^L` for
  `L = 2^(k+3)`, `k = log_2 log_2 d` (EdgeUpper.v:165), then Markov at
  `t = 104 d^2` (EdgeUpperLimit.v:230). Lower edge: the non-backtracking
  recursion of [KNH25, Lemma 5.1] is proved exactly
  (`SquareFree.EdgeLower.pmlo_knh`, EdgeLower.v:385), the traces of powers
  of the non-backtracking matrices are bounded by a sharp count of marked
  walks (`SquareFree.WalkNB*`), the column remainders by deterministic
  operator bounds (`Column.Remainder*`), and a Chebyshev-polynomial step
  turns the bounds into a Loewner box `-(49/24) I <= T_1 - s I`
  (`pmlo_cheb_box`, EdgeLower.v:246), from which the square-free Gram is
  at least `(d^2/128) I` when `4 N <= d^2` (Coercivity.v:118).
- Matrix Bernstein [Tro15, 6.6.1] (l.585): not used; row 2.7.
- Hanson-Wright [RV13] (l.660): the Gaussian case is proved (row 2.11),
  through `library:comparison.chi_square` (chi_square.v:351).
- The measurable maximum theorem [AB06, 18.19] (l.964): not used. The
  maximizer `P(Z)` is replaced by a measurable selector that picks, in a
  finite net of the cone sphere, a point whose support value is within
  `eps |Z|_F` of the supremum (`Cone.ApproxSelector.paper_main_cone_selector_gaussian`,
  ApproxSelector.v:197; `Head.FiniteSupportSelector.paper_main_finite_argmax_measurable`,
  FiniteSupportSelector.v:79). The conditional step of (l.1074-1078) is
  `Clipping.ResidualConditional.paper_main_cone_selector_conditional`
  (ResidualConditional.v:46), with Markov on the section probability
  (`Gaussian.ConditionalException`, ConditionalException.v:38).
- Free-entropy universality [BM25, Thm 4.6] (l.1955): not used; row 4.8.
- Grassmannian nets [Sza83] (l.1755): not used. Nets of orthogonal
  matrices in the projector distance `|P_U - P_V|_F <= tau` are built from
  nets of the unit ball of `R^(d x d)` (`Loss.BallNet`, BallNet.v:45;
  `Orientation.Net`, Net.v:201), with
  `ln |net| <= (4 + 8 r/tau) ln 2 (r + 1)(d + 1)`.
- The VC inequality [DGL13, 12.5] and Sauer's lemma (l.2093-2098): not
  used; row 4.10.
- Gaussian hypercontractivity (l.2088): not used; row 4.10.
- Paley-Zygmund (l.2088): `library:probability.moments.paley_zygmund`
  (moments.v:85), referenced by `Head.SmallBallPZ`.
- Lindeberg's replacement principle (used implicitly at l.1955 through
  [BM25]): `library:probability.lindeberg.lindeberg_replacement`
  (lindeberg.v:223) exists but is not referenced; the tree proves the
  replacement it needs in `Loss.Replacement` (row 4.8).
- McDiarmid [BLM13, 6.2] (l.2331): not used. The lower tail of a bounded
  function of `N` independent Gaussian rows whose row oscillation is at
  most `c` is `exp(-t^2/(2 N c^2))`, proved by a row-by-row exponential
  moment bound (`Loss.ConcentrationRow.paper_main_concentration_rows`,
  ConcentrationRow.v:292; `Loss.ConcentrationTail`, ConcentrationTail.v:34).
- Gordan-Stiemke duality [BV04] (l.173): proved directly (row 2.12).
- `sqrt(s - 1) <= E|g_s| <= sqrt s` (l.491): `Gaussian.NormConcentration.paper_main_gaussian_norm_mean_lower`
  (NormConcentration.v:79) and `Gaussian.Norm.paper_main_gaussian_norm_expectation`
  (Norm.v:77); the Gamma-function identity is not used.
- The chi-square moment generating function (l.1242):
  `Gaussian.QuadraticMGF.gaussian_quadratic_exponential_expectation`
  (QuadraticMGF.v:42, `E exp(t x^2) = (1 - 2t)^(-1/2)`), from
  `library:comparison.chi_square.integral_normal_expR_sqr` (chi_square.v:86)
  through `Gaussian.LawBridge`; the bound (l.1244) and the maximum are
  `Radius.ExponentialMoments` and `Radius.ExpectedMaximum`.
- The binomial entropy bound `sum_{j <= delta n} C(n, j) <= e^(n H_2(delta))`
  (l.2171): replaced by `sum_{j <= k} C(n, j) <= exp(k (1 + ln(n/k)))`
  (BulkUnion.v:105); `sum_{k <= K_d} C(n, k) <= exp(C K_d log(e n/K_d))`
  (l.1562) by `Head.FamilyCount.paper_main_head_families_entropy`
  (FamilyCount.v:81).
- The spectral theorem for real symmetric matrices (used throughout):
  `library:matrix.real_spectral.symmetric_spectral` (real_spectral.v:265),
  by a Rayleigh maximum on the unit sphere (`rayleigh_max`,
  real_spectral.v:208) and Householder reflections (`householder`,
  real_spectral.v:129); referenced by `Spectral.SymmetricDiagonalization`
  (SymmetricDiagonalization.v:102), the only entry point of the tree.
- Operator norm from traces of powers and from quadratic forms
  (l.2158-2167 and the edge arguments): `library:matrix.opnorm.opnorm_le_trace_exp`
  (opnorm.v:252, used by `DiagonalBlock.Trace`, `SquareFree.EdgeUpper`,
  `SquareFree.WalkNBEvent`) and `opnorm_le_form_exp` (opnorm.v:261, used
  by `SquareFree.EdgeLower`); the commutator inequality
  `tr(ABAB) <= tr(A^2 B^2)` is `library:matrix.real_spectral.mxtrace_ABAB_le`
  (real_spectral.v:58).

## (b) Changes of route

1. §2.1, Lem 2.2 (l.387-418). No semicircle law. `Gaussian.ConditionWidth`,
   `Gaussian.ConditionWidthBound`, `Gaussian.SymmetricOperatorTail`,
   `Cone.Condition`: a direct lower bound on the support value of the
   shifted positive part, with a coarse operator-norm event.
2. §2.2, Lem 2.3 (l.434-476). Expectation form of Gordon on finite nets
   plus concentration, instead of the tail comparison on compact sets.
   `Gordon.Processes`, `Gordon.Width`, `Gordon.SoftMargin`, `Gordon.Nets`,
   `Gordon.Entropy`, `Gaussian.GordonTail`.
3. §2.3, Lem 2.6 to Prop 2.8 (l.538-616). Self-contained moment methods
   (section (a)); the lower edge only below density `1/4`; the fourth
   trace moment for the diagonal block. `SquareFree.*`, `Column.*`,
   `DiagonalBlock.*`, `Feature.UpperProbability`.
4. §3.1, Lem 3.2 (l.805-821) and the proof of Thm 3.1 (l.889-924). The
   fit is produced from a kernel element of the cone sphere
   (`Cone.Kernel`, `Conditioned.SupportFit`, `Cone.HeadTailFit`) instead of
   from `0 in W(B)` by convex separation. The tiny-tail case (l.901-921)
   is `Head.TailSupportSplit.paper_main_support_tiny` (TailSupportSplit.v:175)
   with the perturbation `S_0 + delta M_u/|M_u|_F`
   (`Head.TailSupport.paper_main_support_perturbation`, TailSupport.v:80);
   the sign matrix `sgn(M_u)` (l.905) is not used.
5. §3.2, Prop 3.3 (l.960-1096). The maximizer is a measurable net selector
   (section (a)); the joint-to-conditional passage (l.1074-1093) is
   Markov on the section probability with `tau = d^-4`
   (`Head.WidthRegular`, WidthRegular.v:71-72); the rates of Lem 3.8 are
   polynomial in `t = d^(1/32)` (`Head.CorrectionScale`); the head
   selection law is `Head.SelectionLaw` (permutation invariance of the
   product law).
6. §3.3, Lem 3.9 (l.1254-1275). The second-chaos interpolation is proved
   only for the soft minimax, through the row-wise Stein identities of
   `Row.*`, `Joint.*`, `Multirow.*`, with the library's Gaussian
   integration by parts (`Gaussian.LawBridge`).
7. §3.4, Lem 3.13 and Lem 3.15 (l.1451-1471, l.1517-1566). The GOE margin
   is an expectation bound from Gordon in expectation; the clipping is
   coordinate-wise at `d^(1/4)` with the tail `exp(-c d^(3/2))`; the union
   over heads uses `Head.FamilyCount`.
8. §4.1, the split of a witness (l.1665-1683). The spectral cutoff is a
   constant `eps_0` (not `d^(-1/4)`), so the head rank is at most
   `1/eps_0^2`, a constant (`Orientation.Spectral.paper_main_orientation_spectral_order`,
   Spectral.v:141; `Orientation.Witness`, Witness.v:107); the bulk
   operator norm is at most `eps_0 + tau^2` after pinching.
9. §4.1, nets and transport (l.1755-1851). Orientation nets in projector
   distance, pinching instead of rotation, finite priors of candidates
   instead of head nets and `b`-nets (section (a), rows 4.5, 4.6, 4.9).
10. §4.2, universality (l.1917-2025). Lindeberg replacement with a replica
    expansion for the soft minimum over a finite prior, with explicit
    errors and no limits (rows 4.3, 4.8, 4.9). `Loss.*`, `Projection.*`,
    `Hybrid.FiniteMean`.
11. §4.3, Lem 4.10 (l.2081-2108). Parameter net and binomial counts instead
    of VC; computed fourth moment instead of hypercontractivity.
12. §4.4, Prop 4.5 (l.2329-2349). Own bounded-difference inequality for
    Gaussian rows (`Loss.ConcentrationRow`) instead of McDiarmid; the
    union over the orientation net is `Orientation.Union`.
13. Everywhere: the events are proved measurable. The three events of the
    statement by countable rational approximation (`Measurability.*`); the
    exceptional events by continuity of the functionals of the sample
    (`Analysis.ContinuousTupleMeasurability`, `Gaussian.SmoothTail`). The
    paper does not discuss measurability except at (l.964) and (l.1553).
14. Everywhere: the reductions to fixed densities (l.752-757, l.1621-1631)
    are `Fixed.Density` with `Sampling` (deletion of points cannot increase
    the fit probabilities, Density.v:66, 78).

## (c) Hypotheses that formal lemmas add

- `SquareFree.LowerProbability.paper_main_squarefree_lower_probability`
  (LowerProbability.v:36-39): `4 N <= d^2`, `d^2 <= c_1 N` and density at
  least `c` eventually. The satisfiable phase uses it at
  `N = floor(beta d^2)`, `0 < beta < 1/4`, where they hold
  (`Fixed.SubcriticalCounts.paper_main_fixed_subcritical_counts`,
  SubcriticalCounts.v:18). The paper's Lem 2.6 has no such restriction, and
  the formal proof does not cover its range `(1/4, 1/2)`. The unsatisfiable
  phase uses only the upper edge.
- `SquareFree.EdgeUpperLimit.paper_main_squarefree_offdiag_rate`
  (EdgeUpperLimit.v:230) and `SquareFree.WalkNBRate.pmnbr_rate`
  (WalkNBRate.v:221, read): `2^9600 <= d`. The theorems are stated for
  all large `d` with an existential threshold, so the limits hold, but the
  thresholds of the formal proof are astronomically larger than the
  paper's unstated ones.
- `Head.SmallBallUniform.paper_main_head_small_ball_uniform_poly`
  (SmallBallUniform.v:647): `306432 (r + 1)^3 <= m`. Satisfied for
  `r <= sqrt d + 1` and `m = N >= (gamma/2) d^2`, large `d`
  (`Hybrid.Density`, Density.v:326-340).
- `Soft.PublicFeatures.paper_main_public_feature_soft_comparison_coarse`
  (PublicFeatures.v:182), `Soft.ConeMargin` (ConeMargin.v:51): `ln N <= d`.
  Satisfied for `N <= d^2` and `d >= 2 ln d`.
- `Gordon.SoftMargin.paper_main_gordon_soft_width_margin` (SoftMargin.v:59-60):
  the net vectors have norm exactly one. The nets of `Gordon.Entropy`
  (Entropy.v:144) are made of such vectors.
- `Head.RegularProbability.paper_main_head_width_coercive_probability_uniform`
  (RegularProbability.v:170-171): coercivity of the head Gram with constant
  `c d`. Discharged from row 2.9 for `alpha < 1/4` only.
- `Head.SubcriticalProbability.paper_main_head_subcritical_probability`
  (SubcriticalProbability.v:44-46): the sample has no coordinate of absolute
  value at least `d^(1/4)` and the head section operator bound
  `L sqrt d`. The first has probability tending to one for `N <= C d^2`
  (`Clipping.Limits`, Limits.v:75), the second is the upper edge.
- `Hybrid.Assembly.paper_main_hybrid_gap_event` (Assembly.v:138-140):
  `|N - gamma d^2| <= eta d^2`, `r <= sqrt d + 1`, `r + m + 1 <= d`.
  Satisfied by `N = floor(gamma d^2)` and the constant rank bound
  `r <= 1/eps_0^2` (`Unsat.Limit`, Limit.v:7-8).
- `Unsat.Orientation.paper_main_unsat_orientation_constants`
  (Orientation.v:44-45): the feature Gram is at most `K I` with
  `K <= N L^2`, where `(gamma/2) L^2 = 109`. Discharged by row 2.8 (upper
  edge `109 d^2 <= N L^2` for `N >= (gamma/2) d^2`,
  `Loss.EntropyBudget.paper_main_loss_feature_constant`, EntropyBudget.v:19).
- `Orientation.Witness.paper_main_orientation_fit_witness` (Witness.v:105-107):
  `tau <= 1/8`, `eps_0 + tau^2 <= eps`, `1/eps_0^2 <= r_max < d`. Chosen by
  `Unsat.SupercriticalParameters.paper_main_unsat_cutoff_parameters`
  (SupercriticalParameters.v:42) and `Unsat.Limit` (Limit.v:7-8).
- `Loss.QuadraticPrior.paper_main_quadratic_prior_positive`
  (QuadraticPrior.v:65-66): candidates with `|A|_F^2 <= 4` and `|b| <= L`.
  Satisfied by pinched witnesses (`Pinching.Loss.paper_main_pinching_unit_norm`,
  Loss.v:58) and by the Gram bound (`Feature.LossControl.paper_main_feature_witness_offset`,
  LossControl.v:19, read).
- `Gaussian.Residual.paper_main_gaussian_residual_tail` (Residual.v:85-86):
  `|P|_F = 1` and the bilinear bound `kappa/sqrt d`. Satisfied by every
  element of the cone sphere (`Spectral.OperatorTransport.paper_main_matrix_operator_cone_sphere`,
  OperatorTransport.v:144; `Geometry.HeadSpectral.paper_main_head_condition_box`,
  HeadSpectral.v:151), as in the paper's (l.966).
- `Cone.Kernel.paper_main_cone_kernel_exists_support` (Kernel.v:219-220):
  positivity of the support value for every unit `y`, supplied by
  `Head.TailSupportAll.paper_main_support_all` (TailSupportAll.v:89) under
  the scalar condition `A d^-2 (b + delta) sqrt d < delta sqrt(mu)/2`
  (TailSupportAll.v:116), the formal form of `C/d < c'' sqrt d` (l.921).
- `Loss.ConcentrationTail.paper_main_concentration_lower_tail`
  (ConcentrationTail.v:36-38): continuity of the functional and a row
  oscillation bound `c`. The normalized soft minimum has `c = 1/N`
  (`Loss.ConcentrationSoftMin`, ConcentrationSoftMin.v:112-126), the
  paper's `1/n` (l.2330).
- `Data.SampleTail.paper_main_data_coherence_good` (SampleTail.v:447-450):
  every point has `|x_k|^2 <= 4 d`; this is the radius event, as in the
  paper (l.657).

## (d) Formal results near the top of the tree with no paper counterpart

Distance is the number of steps from a block of the frozen files in the
block graph (distance 0: the frozen files themselves; distance 1:
`PaperMainFinalAssembly`, `PaperMainConditionedLimit`).

- Distance 2: `Asymptotics` (7 declarations: squeezes of limits, the
  reduction `paper_main_sat_from_conditioned`, Asymptotics.v:104, of
  Thm 1.2(a) to Thm 1.3, which the paper states in one sentence at l.741);
  `Fixed.Density` (13: reductions to `n = floor(beta d^2)` by padding and
  trimming, Density.v:173, 231; the paper's l.752-757 and l.1621-1631);
  `Measurability.Fit`, `Measurability.Conditioned`, `Measurability.Balanced`
  (32, 16, 30: the three events are Borel; no counterpart in the paper);
  `Balanced.Probability`, `Balanced.Limit` (4, 1: the two limits of Cor 1.4
  from Thm 1.2, the paper's l.173); `Unsat.Limit` (4: the assembly of
  Thm 4.1 from the orientation events, Limit.v:74, which collects the
  paper's proof of l.1854-1906 in one statement).
- Distance 3: `Balanced.Law`, `Balanced.Supercritical` (fit fails and
  spanning imply the balanced certificate; almost sure equality of the
  two events, Supercritical.v:85); `Conditioned.FromLower` (Thm 1.3 at
  fixed density from the lower edge, FromLower.v:33); `Fixed.LowerProbability`
  (the lower edge at `n = floor(beta d^2)`, LowerProbability.v:40);
  `Measurability.Countable`.
- Distance 4: `Sampling` (18: deleting points is measurable and preserves
  the product law, Sampling.v:117; monotonicity of the fit probabilities,
  Sampling.v:178, 188; the paper's "feasibility is monotone", l.757);
  `Feature.GramBlocks` (16: `Q Q^* = D D^T + V V^T`, GramBlocks.v:118, the
  paper's l.519); `Geometry.Exclusion`, `Geometry.Homogeneous`,
  `Geometry.Separation` (the alternative, row 2.12); `Geometry.HeadCoefficients`
  (coercivity and Gram of a head, `paper_main_head_coercive`,
  HeadCoefficients.v:31); `SquareFree.LowerProbability` (row 2.6);
  `Unsat.Orientation` (the constants of the unsatisfiable phase chosen in
  order, Orientation.v:32; the paper fixes its constants inside proofs,
  l.1855, l.2110-2117, l.2216).
- Distance 5, without counterpart: `Conditioned.FromLowerScalars`
  (`0 < lm <= lp`); `Conditioned.SpectralReduction` (SpectralReduction.v:56,
  91: Thm 1.3 from the two spectral bounds on the features, with the
  exceptional events of `Head.SubcriticalFit`); `Feature.LossControl`
  (the quadratic risk `paper_main_quadratic_risk`, LossControl.v:15, its
  Lipschitz bound under a Gram bound, LossControl.v:62, and
  `paper_main_quadratic_risk_zero`, LossControl.v:85: the paper's
  (eq:empirical-loss) and (eq:Q-lip)); `Fixed.CountBounds`,
  `Fixed.SubcriticalCounts` (counts at fixed density); `Gaussian.Spanning`
  (almost sure spanning, the paper's l.678 in parentheses);
  `Gordon.Entropy` (nets of unit vectors with `ln |net| <= (4 + 4/eps) ln 2 d`,
  Entropy.v:144); `Hybrid.FiniteMean`, `Orientation.Exception`,
  `Orientation.Family`, `Orientation.Net`, `Orientation.Union`,
  `Orientation.Witness`, `Unsat.FiniteTail`, `Unsat.Rates`,
  `Unsat.SupercriticalParameters` (the finite-prior and orientation-net
  machinery of rows 4.3, 4.5, 4.6, 4.9); `Loss.EntropyBudget`
  (`c L^2 = 109`); `SquareFree.ChebyshevParametersEdge`, `SquareFree.WalkNBRate`,
  `SquareFree.LowerProbabilityAssembly`, `SquareFree.EdgeUpperLimit`
  (row 2.6); `Measurability.Compact`, `Measurability.Coordinates`.
- Distance 6, without counterpart: `Analysis.ContinuousTupleMeasurability`
  (continuous functions of the coordinates are measurable);
  `Gaussian.FeatureCoordinates`, `Gaussian.IteratedExpectationDefinitions`
  (the iterated Gaussian expectation on lists, the paper's `E`);
  `Gaussian.Multivariate` (polynomial functions of the sample vanish on a
  null set); `Head.SectionMeasurable`; `Hybrid.FiniteArray`,
  `Hybrid.FiniteTail`; `Loss.Empirical`; `Measurability.Box`;
  `Orientation.Prior`, `Orientation.Rotation`; `Projection.Pinching`;
  `SquareFree.EdgeLower` (row 2.6); `Column.RemainderProbability`;
  `Geometry.HeadCorrection` (the deterministic part of row 3.8).
- Deeper, but with no counterpart anywhere in the paper: `Gaussian.LawBridge`
  (distance 8: `gauss d` of the library is the image of the product law of
  the statement, LawBridge.v:88; iterated expectations are integrals
  against it, LawBridge.v:271); `Analysis.RealsBridge` (distance 7:
  pointwise identities between Stdlib's and MathComp's real operations);
  `Head.SelectionLaw` (distance 11: the law of a fixed head of rows and
  its tail is a product law, SelectionLaw.v:135); `Gaussian.PermutationLaw`
  (invariance of the product law under coordinate permutations);
  `Cone.ApproxSelector` (distance 14), `Head.FiniteSupportSelector`
  (distance 15), `Clipping.ResidualConditional` (distance 12): the
  measurable selectors and the conditional Markov step of section (a).

## (e) Which law is used where

Gaussian law of the data `x` (`gaussian_product_law (n d)`):
`Data.*`, `SquareFree.Diagonal*`, `SquareFree.EdgeUpper*`,
`SquareFree.Walk{Moments,Expansion,Bridge,NB,NBEvent,NBRate,NBMoment,NBCount}`,
`SquareFree.LowerProbability*`, `Column.Concentration*`,
`Column.RemainderProbability`, `DiagonalBlock.Moment`, `DiagonalBlock.Limit`,
`Feature.UpperProbability`, `Fixed.LowerProbability`, `Gaussian.DataRadius*`,
`Gaussian.Residual*`, `Gaussian.Spanning`, `Clipping.*`, `Head.DataLog`,
`Head.SelectionLaw`, `Head.Law`, `Head.LawBounds`, `Head.Subcritical*`,
`Head.CompactTail`, `Head.SoftTail`, `Head.SmallBall*`, `Head.WidthRegular`,
`Head.WidthProbability`, `Head.RegularProbability`, `Soft.Comparison`,
`Soft.PublicFeatures`, `Soft.ConeMargin`, `Soft.FeatureMargin` (data half),
`Multirow.*`, `Row.*`, `Joint.*`, `Quadratic.*`, `Loss.Replacement`,
`Loss.RowIncrement`, `Loss.Replica*`, `Loss.Concentration*`,
`Hybrid.FiniteMean`, `Hybrid.FiniteTail`, `Hybrid.FiniteArray`,
`Hybrid.Assembly` (head half), `Orientation.Rotation`,
`Orientation.Exception`, `Orientation.Prior`, `Unsat.*`, `Balanced.*`,
`Measurability.*`, `Sampling`, `Fixed.Density`.

Gaussian law of auxiliary objects only (the symmetric Gaussian matrix `Z`
that defines widths, the GOE surrogate rows `G_i`, the Gaussian matrices
`A`, `g`, `h` of the comparison inequalities): `Gaussian.PsdWidth`,
`Gaussian.PsdWidthLimit`, `Gaussian.ConditionWidth*`,
`Gaussian.SymmetricLaw*`, `Gaussian.SymmetricOperatorTail`,
`Gaussian.WidthVariance`, `Gaussian.FeatureTail`, `Gaussian.OperatorTail`,
`Gaussian.MatrixTail`, `Gaussian.PublicFeature`, `Gaussian.Forward`,
`Gaussian.EscapeTail`, `Gaussian.GordonTail`, `Gordon.*`,
`Head.Section*`, `Head.Width{Expectation,Approx,Actual}`,
`Cone.ApproxSelector*`, `Cone.GaussianCoordinates*`, `Projected.*`,
`Hybrid.Bulk`, `Hybrid.Density`, `Soft.FeatureMargin` (GOE half),
`Projection.*` (Gaussian comparison of the surrogate rows), and the
library files `library:comparison.*`, `library:gaussian.*` (statements
about `gauss n`, an abstract Gaussian vector).

Distribution-free (no probability measure in the statement):
`Geometry.*`, `Cone.{Condition,ConditionOperator,Kernel,KernelSlice,Projection,ProjectionSupport,HeadTailFit}`,
`Spectral.*`, `Pinching.*`, `Projection.{Algebra,Blocks,Frobenius,Pinching}`,
`Matrix.*`, `Tensor.*`, `Polynomial.*`, `Gibbs.*`, `Goe.*`, `Analysis.*`,
`Loss.{Translated,QuadraticPrior,BallNet,JointNet,Empirical,EntropyBudget,LogPolynomial,NormalizedArray,SoftNormalized,Array,Gibbs}`,
`Orientation.{Net,Family,Spectral,Witness,Blocks,BlocksLoss,Union}`,
`SquareFree.{EdgeLower,Coercivity,Box,ChebyshevParameters*,WalkCount,WalkExcess,WalkShape*,WalkWeight,WalkNBCore*,WalkNBMarks,LogarithmicGrowth,MatrixFamilyCauchy*}`,
`Column.Remainder{,Bounds,Cross,Frame,Powers,Recurrence,Scaling,Tolerance}`,
`Column.ConcentrationCoefficient`, `Column.ConcentrationScaling`,
`DiagonalBlock.Trace`, `Feature.{GramBlocks,SpectralBridge,LossControl,ForwardBound}`,
`Head.{TailDecomposition*,TailSupport*,Peeling,FamilyCount,CorrectionScale,CorrectionRates,SectionApprox*,FiniteSupportSelector}`,
`Soft.{Extrema,Lipschitz,ParameterChoice,BlockScoreBounds,BlockThirdBound,MatrixProjectiveBound,MinimaxFrechet,LowerDerivativeBounds,ClippingScale}`,
`Conditioned.{SupportFit,FromLowerScalars}`, `Fixed.{CountBounds,SubcriticalCounts}`,
`Asymptotics`, `Unsat.{SupercriticalParameters,Rates}`,
`library:matrix.*`, `library:probability.moments` (abstract probability
space), and `library:probability.lindeberg` (abstract laws).

The Gaussian law of the data enters the two phases through the feature
edge (rows 2.6-2.9), the elementary estimates (row 2.10), the residual
tails (row 2.11), the head selection laws, the chaos-to-Gaussian
comparisons (rows 3.9, 4.3, 4.8) and the concentration of the clipped and
soft functionals (rows 3.15, 4.12). Everything about widths, Gordon's
inequalities and the hybrid model concerns auxiliary Gaussian objects.

## (f) Possible errors or gaps

In the paper (none affects the formal proof, which takes other routes):

1. l.1203: typo `||\cR_i(t)|` for `|\cR_i(t)|`.
2. l.395-411 (Lem 2.2): the convergences (eq:semicircle-facts) are cited
   from the semicircle law without a reference for `Tr Z_+ / d^(3/2)`
   and `|Z_+|_F^2/d^2`; the uniform integrability argument (l.411) is
   stated, not proved. The formal proof avoids all of it (row 2.2).
3. l.543 (Lem 2.6): the applicability of [KNH25, Thm 1.2(2a)] to the
   square-free degree-two kernel with the given normalization is asserted,
   not checked; the formal proof does not use it, and proves the lower edge
   only for `n/p^2 <= 1/4`, so the paper's claim for `(1/4, 1/2)` remains
   unverified formally (no error found).
4. l.964 (Prop 3.3): the measurable maximum theorem gives a measurable
   selection of the argmax for the fixed compact set; the paper then uses
   it conditionally on data (l.1079-1080) with `P` independent of the data,
   which is correct but the independence is implicit. Formally this is
   handled by selectors and `Head.SelectionLaw` (section (b), item 5).
5. l.2093-2096 (Lem 4.10): the shatter coefficient of unions of two
   half-spaces is bounded by `Pi_hs(N)^2`; correct. The exponent
   `p_0^2 n/128` (l.2104) follows from `t = p_0/2` in the VC inequality
   with `n t^2/32`; correct. No issue found.
6. l.2199 (Prop 4.4, `r = 0`): "after decreasing `a_0` if necessary" needs
   `|b| sqrt{|J|} >= a_0 sqrt n |b|`, true since `|J| >= (1 - delta) n`;
   fine.
7. Remark 4.7 (l.1909-1911) and the proof of Prop 4.5 rely on the uniform
   universality of Prop 4.3 over offsets that depend on the head
   realization; Prop 4.3 is stated for deterministic offsets, which
   suffices by conditioning (l.2316-2319). No gap.

No mathematical error was found in sections 1.2 to 4 beyond the typo of
item 1; items 2 to 4 are places where the paper relies on citations or
sketches that the formal proof does not reproduce.

In the formal proof (statements checked; proofs are accepted by the
kernel, so "gap" means a gap between what is proved and what the paper
claims):

1. Lem 2.6 and Prop 2.8 are proved only below density `1/4` for the lower
   edge (row 2.6); the paper's uniform statement on `(0, 1/2)` is not
   formalized. Nothing in the main theorems needs it.
2. The constants `lambda_-, lambda_+` of Thm 1.3 exist but are not
   computed (`kappa` is produced by `Head.SubcriticalFit` through
   `Soft.ParameterChoice` and `Gaussian.ConditionWidthBound` with an
   existential `K`); likewise the thresholds in `d` are existential, and
   some inner thresholds are explicit but enormous (`2^9600`, section (c)).
3. The formal proof assumes the eight classical axioms of
   `check/assumptions.expected` (excluded middle, functional and
   propositional extensionality, choice, as MathComp-Analysis does); the
   paper's proof is classical as well, so this is not a discrepancy.
4. Lem 2.5 is used in its net form with the constant `20 ln 2` (row 2.5);
   the sharp constants of the paper are in the library but not in the tree
   (no used block references `gauss_opnorm_tail`).
5. Nine of the 25 library files, among them the general Gaussian
   interpolation (`gauss_interpolation.v`) and Lindeberg's replacement
   principle (`lindeberg.v`), are not referenced from `theories/`; the
   tree proves specialized versions instead (rows 3.9, 4.8). This is a
   duplication, not a gap.
