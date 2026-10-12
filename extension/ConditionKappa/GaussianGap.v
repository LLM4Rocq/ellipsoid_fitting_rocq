(* The Gaussian gap above the threshold alpha(C, kappa), at Stdlib's R:
   item G1 of phase 11, second half (notes/phase11-plan.md, sections 3.4, 5
   and 6; lane B). The model is Condition/GaussianGap.v, which treats
   kappa = 3.

   Setting, constants and interface I1 (a hypothesis until item M5 lands)
   as in GaussianWitness.

   Output, interface I4 (the gap), for item D2 (Unsat): for 1 < Cp and
   alpha(Cp, kappa) < alpha, some g > 0 such that, for every n with
   n/d^2 -> alpha, every eps > 0 and every large d, outside a measurable
   set E of n d Gaussian features with
   tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps, every S
   of cond_slice Cp and every real b have
     g n <= sum_i (b - <Z_i, mxvec S>)^2:
   the gap is uniform in the intercept b, and the proof keeps the
   centering of Condition/GaussianGap.v, with n - 1 centered rows. This is
   the hypothesis of condition_unsat_gap of Condition/Unsat.v with
   gaussian_feature_law kappa d in place of gaussian_feature_law 3 d. *)
