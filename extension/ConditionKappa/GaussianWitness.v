(* The approximate Gaussian witness below the threshold alpha(C, kappa), at
   Stdlib's R: item G1 of phase 11, first half (notes/phase11-plan.md,
   sections 3.4, 5 and 6; lane B). The model is Condition/GaussianWitness.v,
   which treats kappa = 3.

   Setting. kappa > 1, c = (kappa - 3) / 2, a0 = min(1, 1 + c); C > 1. The
   cone T K_C, its base and its support function sigma_{C,kappa} are those
   of Cone (item B1). The Gaussian features are those of
   gaussian_feature_law kappa d: T_kappa stays in the step features_mul,
   through gaussian_feature_vec_dot (Gaussian/Representation.v), where the
   case kappa = 3 used cone_map3. The constants come from the bounds
   sqrt (a0 d) <= |T S|_F <= sqrt (max(1, 1 + c) C d) on the base, in place
   of sqrt d and sqrt (C d); they may depend on C, kappa and alpha.

   Interface I1, a hypothesis here until item M5 (GaussianLimit, lane A)
   lands: for C > 1,
     cvg_prob (fun d => gauss (d * d))
       (fun d a => sigma_{C,kappa}(vec_mx a) / d)
       (sqrt (condition_kappa_alpha C kappa)),
   the hypothesis hQ2 of Condition/GaussianWitness.v with sigma_{C,kappa}
   in place of cond_support C and alpha(C, kappa) in place of
   condition_alpha C.

   Output, interface I4 (the witness), for item D1 (Sat): for 1 < Cm and
   0 < alpha < alpha(Cm, kappa), some c0 >= 0 such that, for every n with
   n/d^2 -> alpha and every large d, outside a measurable set E of n d
   Gaussian features with
   tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= 1/4, some S
   of cond_slice Cm has sum_i <Z_i, mxvec S>^2 <= c0. S lies in the
   original trace-d slice: its condition number is measured on S, before
   T_kappa. This is the hypothesis of condition_sat_witness of
   Condition/Sat.v with gaussian_feature_law kappa d in place of
   gaussian_feature_law 3 d and alpha(Cm, kappa) in place of
   condition_alpha Cm. *)
