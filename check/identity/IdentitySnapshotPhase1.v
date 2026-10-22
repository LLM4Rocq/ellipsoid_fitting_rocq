(* The identity driver of the statement snapshot SnapshotPhase1 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase1.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase1.json. *)

Require EllipsoidFitting.AnalysisIntegralDefinitions.
Require EllipsoidFitting.GaussianDefinitions.
Require EllipsoidFitting.GaussianProbabilityDefinitions.
Require EllipsoidFitting.GaussianProbabilityProductDefinitions.
Require EllipsoidFitting.PaperMainDefinitions.
Require EllipsoidFitting.MainStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidFitting.AnalysisIntegralDefinitions.oriented_integral".
KernelIdentity "definition" "EllipsoidFitting.AnalysisIntegralDefinitions.segment_integrable".
KernelIdentity "definition" "EllipsoidFitting.AnalysisIntegralDefinitions.oriented_has_integral".
KernelIdentity "definition" "EllipsoidFitting.AnalysisIntegralDefinitions.whole_line_integral".
KernelIdentity "definition" "EllipsoidFitting.AnalysisIntegralDefinitions.whole_line_integrable".
KernelIdentity "definition" "EllipsoidFitting.AnalysisIntegralDefinitions.whole_line_has_integral".
KernelIdentity "definition" "EllipsoidFitting.AnalysisIntegralDefinitions.continuity_2d_pt".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_kernel".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_stein_integrand".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_primitive".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_mass".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_integral".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_has_integral".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_integral_exists".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_absolutely_integrable".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_expectation".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.gaussian_density".
KernelIdentity "definition" "EllipsoidFitting.GaussianDefinitions.moment_factor".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law_density".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law_integrable".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law_expectation".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_law_probability".
KernelIdentity "opaque-body" "EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_pair_probability_setT_subproof".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.HB_unnamed_factory_1".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__probability_measure_isProbability".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__measure_function_isSigmaFinite".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__probability_measure_isSubProbability".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__measure_function_isSFinite".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__measure_function_isFinite".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_pair_probability".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_cons_tuple".
KernelIdentity "type" "EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_cons_tuple_measurable".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.HB_unnamed_factory_7".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.GaussianProbabilityProductDefinitions_gaussian_cons_tuple__canonical__measurable_function_MeasurableFun".
KernelIdentity "definition" "EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_product_law".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_quadratic_form".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_symmetric".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_psd".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_pd".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_loewner_le".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_trace".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_point".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_fit_event".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_conditioned_event".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_balanced_pd_event".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_probability".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_density".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_eventually_le".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_eventually_ge".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_limsup_lt".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_limsup_le".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_liminf_gt".
KernelIdentity "definition" "EllipsoidFitting.PaperMainDefinitions.paper_main_tends_to".
KernelIdentity "definition" "EllipsoidFitting.MainStatement.main_statement".
