(* The unsatisfiable half of the threshold at fourth moment kappa, for
   finite mixtures of product laws, at Stdlib's R: item D2 of phase 11
   (notes/phase11-plan.md, sections 3.4, 5 and 6; lane B). The model is
   Condition/Unsat.v, which treats kappa = 3; Condition/Cover.v and
   Condition/Slices.v are reused as they are.

   Result to prove here: for K > 0, kappa > 1, C > 1 and
   alpha(C, kappa) < alpha, every finite mixture family with
   mixture_family K N w mu and mixture_fourth_moment kappa N w mu, and every
   n with n/d^2 -> alpha, the probability of
   universality_conditioned_fit_event (n d) d C tends to 0. This covers
   every alpha > alpha(C, kappa), alpha >= 1/2 included.

   Interfaces used.
   - I3, from item S3 (Curve, lane C): the analogue of condition_alpha_right
     of Condition/Curve.v for alpha(C, kappa), which gives some Cp > C with
     alpha(Cp, kappa) < alpha.
   - I4 (the gap), from item G1 (GaussianGap), at Cp: the hypothesis of
     condition_unsat_gap of Condition/Unsat.v with
     gaussian_feature_law kappa d, uniform in the intercept; see the header
     of GaussianGap. Until G1 lands, the first conditional lemma takes it
     as a hypothesis.
   Constants by their role, as in Sat: the regularity constant of the
   mixture features depends on kappa, the 3^(1/4) of the Gaussian
   regularity bound does not. *)
