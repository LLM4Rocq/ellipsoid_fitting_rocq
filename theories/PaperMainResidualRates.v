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

Theorem paper_main_residual_union_tends_to_zero (p : nat -> \bar R) (N : nat -> nat) C kappa :
  0 <= C -> 0 <= kappa -> (forall d, (0 <= p d)%E) ->
  (exists D, forall d, Nat.le D d -> INR (N d) <= C*(INR d)^2 /\
    (p d <= ((2*INR (N d)*exp(-INR d*(paper_main_residual_threshold kappa (INR d))^2 /
      (4+4*kappa*paper_main_residual_threshold kappa (INR d))))%Rcoq)%:E)%E) ->
  paper_main_tends_to p 0.
Proof.
move=> HC Hk Hp [D HD].
have [K HK] := INR_unbounded ((4+4*kappa)^2).
apply: (paper_main_sqrt_polynomial_tends_to_zero p (2*C) 2) => //; first lra.
exists (Nat.max D (S K)) => d Hdd.
have Hd : 0 < INR d by apply lt_0_INR; lia.
have Hlarge : (4+4*kappa)^2 <= INR d by have := le_INR K d ltac:(lia); lra.
have [HN HB] := HD d ltac:(lia).
have HE := paper_main_residual_exponential_rate kappa (INR d) Hk Hd Hlarge.
apply: (le_trans HB); rewrite lee_fin; apply/RleP.
change (2*INR (N d)*exp(-INR d*(paper_main_residual_threshold kappa (INR d))^2 /
    (4+4*kappa*paper_main_residual_threshold kappa (INR d))) <=
  (2*C)*(INR d)^2*exp(-sqrt(INR d)/2)).
have HM := Rmult_le_compat_l (2*INR (N d)) _ _ ltac:(have := pos_INR (N d); lra) HE.
have Hexp := exp_pos (-sqrt(INR d)/2).
have HN' := Rmult_le_compat_r (exp(-sqrt(INR d)/2)) _ _ (Rlt_le _ _ Hexp) HN.
nra.
Qed.
Theorem paper_main_residual_threshold_tends_to_zero kappa :
  0 <= kappa -> paper_main_tends_to
    (fun d => (paper_main_residual_threshold kappa (INR d))%:E) 0.
Proof.
move=> Hk eps Heps.
have HepsR : 0 < eps by exact/RltP.
pose a := sqrt(4+4*kappa)/eps.
have HA : 0 < sqrt(4+4*kappa) by apply sqrt_lt_R0; lra.
have Ha : 0 < a by apply Rdiv_lt_0_compat.
have [K HK] := INR_unbounded (a^4).
exists (S K) => d Hdd.
have HddN : Nat.le (S K) d by exact: (elimT ssrnat.leP Hdd).
have Hd : 0 < INR d by apply lt_0_INR; lia.
have Hr := (proj1 (paper_main_residual_threshold_scale kappa (INR d) Hk Hd)).
have Hlarge : a^4 < INR d by have := le_INR K d ltac:(lia); lra.
have Hs := sqrt_pos (INR d).
have Ht := sqrt_lt_R0 (sqrt(INR d)) (sqrt_lt_R0 _ Hd).
have HS := pow2_sqrt (INR d) (pos_INR d).
have HT := pow2_sqrt (sqrt(INR d)) Hs.
have HE : (sqrt(sqrt(INR d)))^4 = INR d by nra.
have Hroot : a < sqrt(sqrt(INR d)).
{ case: (Rlt_dec a (sqrt(sqrt(INR d)))) => H; first exact H.
  have Hle : 0 <= sqrt(sqrt(INR d)) <= a by split; lra.
  have HP := pow_incr _ _ 4 Hle.
  rewrite HE in HP; lra. }
have HM := Rmult_lt_compat_r eps _ _ HepsR Hroot.
rewrite /a in HM.
replace (sqrt(4+4*kappa)/eps*eps) with (sqrt(4+4*kappa)) in HM by (field; lra).
have Hrate : paper_main_residual_threshold kappa (INR d) < eps.
{ unfold paper_main_residual_threshold.
  apply (Rmult_lt_reg_r (sqrt(sqrt(INR d)))); first exact Ht.
  replace (sqrt(4+4*kappa)/sqrt(sqrt(INR d))*sqrt(sqrt(INR d))) with
    (sqrt(4+4*kappa)) by (field; lra).
  lra. }
have Hr0 : (0 <= (paper_main_residual_threshold kappa (INR d))%:E)%E.
{ rewrite lee_fin; apply/RleP; change (0 <= paper_main_residual_threshold kappa (INR d)); lra. }
rewrite sube0 (gee0_abs Hr0) lte_fin; exact/RltP.
Qed.
