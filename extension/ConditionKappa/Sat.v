(* The satisfiable half of the threshold at fourth moment kappa, for finite
   mixtures of product laws, at Stdlib's R: item D1 of phase 11
   (notes/phase11-plan.md, sections 3.4, 5 and 6; lane B). The model is
   Condition/Sat.v, which treats kappa = 3; Condition/Cover.v and
   Condition/Slices.v are reused as they are.

   Result to prove here: for K > 0, kappa > 1, C > 1 and
   0 < alpha < alpha(C, kappa), every finite mixture family with
   mixture_family K N w mu and mixture_fourth_moment kappa N w mu, and every
   n with n/d^2 -> alpha, the probability of
   universality_conditioned_fit_event (n d) d C tends to 1.

   Interfaces used.
   - I3, from item S3 (Curve, lane C): the analogue of condition_alpha_left
     of Condition/Curve.v for alpha(C, kappa), which gives some Cm with
     1 < Cm < C and alpha < alpha(Cm, kappa); and
     alpha(Cm, kappa) < alpha*(kappa) < 1/2, which gives the alpha < 1/2 of
     the mixture interpolation (in place of condition_alpha_le).
   - I4 (the witness), from item G1 (GaussianWitness), at Cm: the
     hypothesis of condition_sat_witness of Condition/Sat.v with
     gaussian_feature_law kappa d; see the header of GaussianWitness.
     Until G1 lands, the first conditional lemma takes it as a hypothesis.
   Constants by their role: the constant Kf = 2^10 K^2 / sqrt (3 - 1) of
   Condition/Sat.v is that of mix_feature_regular at the data fourth
   moment and becomes 2^10 K^2 / sqrt (kappa - 1); the 3^(1/4) of the
   Gaussian regularity bound gaussian_feature_regular holds for every kappa
   and stays. *)
