(* Actual bounded-condition Gaussian widths: an explicit dimension-uniform
   lower bound, with all exceptional-event premises discharged. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From EllipsoidFitting Require Import SoftExtrema GaussianProductDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainGaussianFeatureCoordinates PaperMainGaussianPsdWidth
  PaperMainGaussianPsdWidthLimit PaperMainGaussianConditionWidth
  PaperMainGaussianSymmetricOperatorTail PaperMainGaussianDataRadiusLimit.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Lemma paper_main_gaussian_psd_projection_mean_lower n :
  INR (S n)/2-1 <= gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_gaussian_psd_projection_norm n).
Proof.
have [HL _] := paper_main_gaussian_psd_projection_mean_bounds n.
rewrite paper_main_symmetric_dimension_real in HL.
pose d := INR (S n).
change (sqrt (d*(d+1)/2/2-1) <= gaussian_iterated_expectation (paper_main_symmetric_dimension n) (paper_main_gaussian_psd_projection_norm n)) in HL.
have Hd : 1 <= d by unfold d; rewrite S_INR; have := pos_INR n; lra.
have Hpos := sqrt_pos (d*(d+1)/2/2-1).
change (d/2-1 <= gaussian_iterated_expectation (paper_main_symmetric_dimension n) (paper_main_gaussian_psd_projection_norm n)).
case: (Rle_dec d 2) => Hsmall; first lra.
have HR : 0 <= d*(d+1)/2/2-1 by nra.
have HS := pow2_sqrt _ HR; nra.
Qed.

Theorem paper_main_gaussian_condition_width_finite n s :
  0 < s ->
  (1/2-s)*INR (S n)-2-
    INR (paper_main_symmetric_dimension n)/(2*(INR (S n))^2)-
    4*(INR (S n))^2*exp(-10*INR (S n)) <=
  paper_main_gaussian_condition_width n ((20+s)/s).
Proof.
move=> Hs.
pose d := INR (S n).
have Hd : 0 < d by unfold d; apply lt_0_INR; lia.
have [A [HM [HP HO]]] := paper_main_symmetric_gaussian_operator_good_set n.
have H := paper_main_gaussian_condition_expectation n 20 s ((20+s)/s) A (d^2)
  ltac:(lra) Hs (Logic.eq_refl _) ltac:(nra) HM HO.
have Hmult : ((((2*d^2)%Rcoq)%:E * gaussian_product_law (paper_main_symmetric_dimension n) A) <=
  (((2*d^2)%Rcoq)%:E * (2*exp(-10*d))%:E))%E.
  apply: lee_wpmul2l HP.
  rewrite lee_fin; apply/RleP; change (0 <= 2*d^2); nra.
have Htotal := le_trans H (leeD (lexx _) Hmult).
rewrite -EFinM -EFinD lee_fin in Htotal.
move/RleP: Htotal => Htotal.
change (gaussian_iterated_expectation (paper_main_symmetric_dimension n)
  (paper_main_gaussian_psd_projection_norm n) <=
  paper_main_gaussian_condition_width n ((20+s)/s)+s*d+1+
  INR (paper_main_symmetric_dimension n)/(2*d^2)+(2*d^2)*(2*exp(-10*d))) in Htotal.
have HL := paper_main_gaussian_psd_projection_mean_lower n.
change (d/2-1 <= gaussian_iterated_expectation (paper_main_symmetric_dimension n) (paper_main_gaussian_psd_projection_norm n)) in HL.
change ((1/2-s)*d-2-INR (paper_main_symmetric_dimension n)/(2*d^2)-
  4*d^2*exp(-10*d) <= paper_main_gaussian_condition_width n ((20+s)/s)).
lra.
Qed.

Lemma paper_main_condition_dimension_ratio n :
  INR (paper_main_symmetric_dimension n)/(2*(INR (S n))^2) <= 1/2.
Proof.
rewrite paper_main_symmetric_dimension_real.
pose d := INR (S n).
have Hd : 1 <= d by unfold d; rewrite S_INR; have := pos_INR n; lra.
change (d*(d+1)/2/(2*d^2) <= 1/2).
apply (Rmult_le_reg_r (2*d^2)); first nra.
replace (d*(d+1)/2/(2*d^2)*(2*d^2)) with (d*(d+1)/2) by (field; nra).
nra.
Qed.

Lemma paper_main_condition_exp_rate d :
  0 < d -> d^2*exp(-10*d) <= 216/d.
Proof.
move=> Hd.
have HE : exp(-10*d) <= exp(-d/2) by apply exp_monotone; lra.
have HR := paper_main_data_radius_rate 1 d (d^2) ltac:(lra) Hd ltac:(lra).
have HM := Rmult_le_compat_l (d^2) _ _ (pow2_ge_0 d) HE.
lra.
Qed.

Theorem paper_main_gaussian_condition_width_lower n s :
  0 < s -> (1/2-s)*INR (S n)-3-864/INR (S n) <=
    paper_main_gaussian_condition_width n ((20+s)/s).
Proof.
move=> Hs.
have H := paper_main_gaussian_condition_width_finite n s Hs.
have HR := paper_main_condition_dimension_ratio n.
have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
have HE := paper_main_condition_exp_rate (INR (S n)) Hd.
lra.
Qed.

Theorem paper_main_gaussian_condition_width_normalized_lower n s :
  0 < s -> 1/2-s-867/INR (S n) <=
    paper_main_gaussian_condition_width n ((20+s)/s)/INR (S n).
Proof.
move=> Hs.
pose d := INR (S n).
have Hd : 1 <= d by unfold d; rewrite S_INR; have := pos_INR n; lra.
have H := paper_main_gaussian_condition_width_lower n s Hs.
change ((1/2-s)*d-3-864/d <= paper_main_gaussian_condition_width n ((20+s)/s)) in H.
have HR : 864/d <= 864.
  apply (Rmult_le_reg_r d); first lra.
  replace (864/d*d) with 864 by (field; lra); lra.
change (1/2-s-867/d <= paper_main_gaussian_condition_width n ((20+s)/s)/d).
apply (Rmult_le_reg_r d); first lra.
replace ((1/2-s-867/d)*d) with ((1/2-s)*d-867) by (field; lra).
replace (paper_main_gaussian_condition_width n ((20+s)/s)/d*d) with
  (paper_main_gaussian_condition_width n ((20+s)/s)) by (field; lra).
lra.
Qed.

Theorem paper_main_gaussian_condition_width_large eps :
  0 < eps -> exists kappa, 1 <= kappa /\
    exists K, forall n, Nat.le K n ->
      (1/2-eps)*INR (S n) <= paper_main_gaussian_condition_width n kappa.
Proof.
move=> Heps.
exists ((20+eps/2)/(eps/2)); split.
- apply paper_main_condition_parameter; lra.
- have [K HK] := INR_unbounded (1734/eps).
  exists K => n Hn.
  pose d := INR (S n).
  have Hd : 0 < d by unfold d; apply lt_0_INR; lia.
  have Hlarge : 1734/eps < d by have := le_INR K (S n) ltac:(lia); unfold d; lra.
  have HR : 867/d < eps/2.
    apply (Rmult_lt_reg_r d); first exact Hd.
    replace (867/d*d) with 867 by (field; lra).
    have HE := Rmult_lt_compat_l eps _ _ Heps Hlarge.
    replace (eps*(1734/eps)) with 1734 in HE by (field; lra); nra.
  have HB := paper_main_gaussian_condition_width_normalized_lower n (eps/2) ltac:(lra).
  change (1/2-eps/2-867/d <= paper_main_gaussian_condition_width n ((20+eps/2)/(eps/2))/d) in HB.
  have HH : 1/2-eps <= paper_main_gaussian_condition_width n ((20+eps/2)/(eps/2))/d by lra.
  have HM := Rmult_le_compat_r d _ _ (Rlt_le _ _ Hd) HH.
  replace (paper_main_gaussian_condition_width n ((20+eps/2)/(eps/2))/d*d) with
    (paper_main_gaussian_condition_width n ((20+eps/2)/(eps/2))) in HM by (field; lra).
  exact HM.
Qed.
