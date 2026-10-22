(* The identity driver of the statement snapshot SnapshotPhase13 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase13.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase13.json. *)

Require GaussianApplications.SatThresholdDefinitions.
Require GaussianApplications.SatThresholdStatement.
Require GaussianApplications.MinSuperadditiveStatement.
Require GaussianApplications.PsdNormalizationStatement.
Require GaussianApplications.ProductSmoothingStatement.
Require GaussianApplications.PsdRankDefinitions.
Require GaussianApplications.PsdRankStatement.
Require Checks.LibraryStatements.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "GaussianApplications.SatThresholdDefinitions.sat_prob".
KernelIdentity "definition" "GaussianApplications.SatThresholdStatement.sat_threshold_statement".
KernelIdentity "definition" "GaussianApplications.MinSuperadditiveStatement.min_superadditive_statement".
KernelIdentity "definition" "GaussianApplications.PsdNormalizationStatement.psd_normalization_statement".
KernelIdentity "definition" "GaussianApplications.ProductSmoothingStatement.product_smoothing_statement".
KernelIdentity "definition" "GaussianApplications.PsdRankDefinitions.kn_edge".
KernelIdentity "definition" "GaussianApplications.PsdRankDefinitions.edge_cut".
KernelIdentity "definition" "GaussianApplications.PsdRankDefinitions.is_perfect_matching".
KernelIdentity "definition" "GaussianApplications.PsdRankDefinitions.perfect_matching".
KernelIdentity "definition" "GaussianApplications.PsdRankDefinitions.odd_set".
KernelIdentity "definition" "GaussianApplications.PsdRankDefinitions.crossing".
KernelIdentity "definition" "GaussianApplications.PsdRankDefinitions.shifted_matching_mx".
KernelIdentity "definition" "GaussianApplications.PsdRankStatement.psd_rank_statement".
KernelIdentity "type" "Checks.LibraryStatements.accepted_finite_mean.unif_mean_union_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_finite_mean.unif_mean_indicatorN_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_finite_mean.unif_mean_markov_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_finite_mean.unif_mean_cutoff_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_finite_mean.unif_chebyshev_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_ord_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_set_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean0_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanS_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.eq_binomial_mean_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_cst_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanD_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanZ_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.ler_binomial_mean_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_id_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_sqr_dev_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_chebyshev_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_last_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_trials_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.unif_mean_binomial_mean_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanE_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_mean.integral_binomial_mean_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.homo_iter_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.iter_le_subcomm_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.monotone_iter_le_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.iter_scale_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.iter_mix_binomial_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.binomial_mix_le_iter_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.meet_avg_linear_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.meet_avg_monotone_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.meet_avg_cst_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.meet_avgC_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_commuting_operators.iter_meet_avg_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.bchar_algebra_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.bchar_orthogonal_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.bchar_delta_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_metric_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_inversion_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_expansion_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_plancherel_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_linear_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_comp_linear_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_mulmx_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_norm_le_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_translate_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_expansion_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_translate_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_row_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.bchar_col_mx_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.blk_col_mx_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_col_mx_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_ge0_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_size_gt0_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_restrict_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_widen_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_shift_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_nonneg_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.central_bin_le_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.central_bin_ge_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.half_bin_ge_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.leq_bin_half_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.bin_near_half_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_central_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_ratio_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_binomial_bounds.bin_partial_sum_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_duality.psd_eval_cone_closed_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_duality.psdmx_dual_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_duality.psd_farkas_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_accepted".
KernelIdentity "type" "Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_affine_accepted".
KernelIdentity "type" "GaussianAnalysis.probability.finite_mean.unif_mean_union".
KernelIdentity "type" "GaussianAnalysis.probability.finite_mean.unif_mean_indicatorN".
KernelIdentity "type" "GaussianAnalysis.probability.finite_mean.unif_mean_markov".
KernelIdentity "type" "GaussianAnalysis.probability.finite_mean.unif_mean_cutoff".
KernelIdentity "type" "GaussianAnalysis.probability.finite_mean.unif_chebyshev".
KernelIdentity "type" "GaussianAnalysis.probability.finite_mean.unif_mean_tuple_prod_ord".
KernelIdentity "type" "GaussianAnalysis.probability.finite_mean.unif_mean_tuple_prod_set".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_mean0".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_meanS".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.eq_binomial_mean".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_mean_cst".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_meanD".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_meanZ".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.ler_binomial_mean".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_mean_id".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_mean_sqr_dev".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_chebyshev".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_mean_last".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_mean_trials".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.unif_mean_binomial_mean".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.binomial_meanE".
KernelIdentity "type" "GaussianAnalysis.probability.binomial_mean.integral_binomial_mean".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.homo_iter".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.iter_le_subcomm".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.monotone_iter_le".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.iter_scale".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.iter_mix_binomial".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.binomial_mix_le_iter".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.meet_avg_linear".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.meet_avg_monotone".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.meet_avg_cst".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.meet_avgC".
KernelIdentity "type" "GaussianAnalysis.probability.commuting_operators.iter_meet_avg".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.bchar_algebra".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.bchar_orthogonal".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.bchar_delta".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.blk_dist_metric".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_inversion".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_expansion".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_plancherel".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_linear".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_comp_linear".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_mulmx".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_norm_le".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_translate".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.low_blk_deg_expansion".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.low_blk_deg_translate".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.blk_dist_row".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.bchar_col_mx".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.blk_col_mx".
KernelIdentity "type" "GaussianAnalysis.fourier.boolean_fourier.fcoef_col_mx".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_factorization.psd_factorization_ge0".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_factorization.psd_factorization_size_gt0".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_factorization.psd_factorization_restrict".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_factorization.psd_factorization_widen".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_factorization.psd_factorization_shift".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_factorization.psd_factorization_nonneg".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.central_bin_le".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.central_bin_ge".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.half_bin_ge".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.leq_bin_half".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.bin_near_half".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.bin_sqr_central".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.bin_sqr_ratio".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.bin_partial_sum".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_duality.psd_eval_cone_closed".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_duality.psdmx_dual".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_duality.psd_farkas".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_duality.psd_slack_certificate".
KernelIdentity "type" "GaussianAnalysis.matrix.psd_duality.psd_slack_certificate_affine".
