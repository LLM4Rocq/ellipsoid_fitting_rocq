(* A polynomially decaying residual threshold with a vanishing row-union bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 PaperMainDefinitions PaperMainAsymptotics
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity PaperMainClippingLimits PaperMainClippingRates.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Definition paper_main_residual_threshold kappa d :=
  sqrt(4+4*kappa)/sqrt(sqrt d).

Lemma paper_main_residual_threshold_scale kappa d :
  0 <= kappa -> 0 < d ->
  0 < paper_main_residual_threshold kappa d /\
  d*(paper_main_residual_threshold kappa d)^2 = (4+4*kappa)*sqrt d.
Proof.
move=> Hk Hd.
have Ha : 0 < 4+4*kappa by lra.
have Hs := sqrt_lt_R0 d Hd.
have Ht := sqrt_lt_R0 (sqrt d) Hs.
have Hsa := sqrt_lt_R0 (4+4*kappa) Ha.
have HS := pow2_sqrt d (Rlt_le _ _ Hd).
have HT := pow2_sqrt (sqrt d) (Rlt_le _ _ Hs).
have HA := pow2_sqrt (4+4*kappa) (Rlt_le _ _ Ha).
split.
- unfold paper_main_residual_threshold; apply Rdiv_lt_0_compat; assumption.
- unfold paper_main_residual_threshold.
  remember (sqrt d) as sd eqn:Es in *.
  remember (sqrt sd) as td eqn:Et in *.
  apply (Rmult_eq_reg_r (td^2)).
  + replace (d*(sqrt(4+4*kappa)/td)^2*td^2) with (d*(sqrt(4+4*kappa))^2) by (field; lra).
    rewrite HA HT -HS; ring.
  + apply Rgt_not_eq,pow_lt; exact Ht.
Qed.

Lemma paper_main_residual_threshold_small kappa d :
  0 <= kappa -> 0 < d -> (4+4*kappa)^2 <= d ->
  paper_main_residual_threshold kappa d <= 1.
Proof.
move=> Hk Hd Hlarge.
have [Hr HE] := paper_main_residual_threshold_scale kappa d Hk Hd.
have HS := pow2_sqrt d (Rlt_le _ _ Hd).
have Hs := sqrt_pos d.
have Ha : 0 < 4+4*kappa by lra.
have Hroot : 4+4*kappa <= sqrt d by nra.
have HM := Rmult_le_compat_r (sqrt d) _ _ Hs Hroot.
have Hrs : (paper_main_residual_threshold kappa d)^2 <= 1 by nra.
nra.
Qed.

Lemma paper_main_residual_exponential_rate kappa d :
  0 <= kappa -> 0 < d -> (4+4*kappa)^2 <= d ->
  exp(-d*(paper_main_residual_threshold kappa d)^2 /
    (4+4*kappa*paper_main_residual_threshold kappa d)) <= exp(-sqrt d/2).
Proof.
move=> Hk Hd Hlarge.
have [Hr HE] := paper_main_residual_threshold_scale kappa d Hk Hd.
have Hr1 := paper_main_residual_threshold_small kappa d Hk Hd Hlarge.
pose den := 4+4*kappa*paper_main_residual_threshold kappa d.
have Hden : 0 < den by unfold den; nra.
have HD : den <= 4+4*kappa by unfold den; nra.
have Hs := sqrt_lt_R0 d Hd.
have HM := Rmult_le_compat_l (sqrt d) _ _ (Rlt_le _ _ Hs) HD.
have Hdiv : sqrt d <= d*(paper_main_residual_threshold kappa d)^2/den.
{ apply (Rmult_le_reg_r den); first exact Hden.
  replace (d*(paper_main_residual_threshold kappa d)^2/den*den)
    with (d*(paper_main_residual_threshold kappa d)^2) by (field; lra).
  nra. }
fold den.
apply Rlt_le,exp_increasing.
change (-d*(paper_main_residual_threshold kappa d)^2/den < -sqrt d/2).
unfold Rdiv in Hdiv |- *; nra.
Qed.
