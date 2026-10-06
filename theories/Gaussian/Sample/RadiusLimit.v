(* Vanishing failure probability for the Gaussian radius event when the
   number of observations is at most quadratic in the dimension. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  PaperMainDefinitions Asymptotics GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gaussian.Sample.Radius.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Lemma paper_main_data_exp_cubic x :
  0 < x -> x^3 * exp (-x/2) <= 216.
Proof.
intros Hx.
pose proof (exp_ineq1_le (x/6)) as He.
pose proof (exp_pos (x/6)) as Hp.
pose proof (pow_incr (x/6) (exp (x/6)) 3 ltac:(split; lra)) as Hcube.
assert (HC : x^3 <= 216 * (exp (x/6))^3) by nra.
assert (HE : (exp (x/6))^3 = exp (x/2)).
{ replace (x/2) with (x/6+x/6+x/6) by field.
  rewrite !exp_plus; ring. }
rewrite HE in HC.
pose proof (exp_pos (-x/2)) as Hneg.
pose proof (Rmult_le_compat_r (exp (-x/2)) _ _ (Rlt_le _ _ Hneg) HC) as HM.
assert (Hinv : exp (x/2) * exp (-x/2) = 1).
{ rewrite <- exp_plus; replace (x/2 + -x/2) with 0 by field; apply exp_0. }
nra.
Qed.

Lemma paper_main_data_radius_rate C x y :
  0 <= C -> 0 < x -> y <= C*x^2 -> y*exp(-x/2) <= 216*C/x.
Proof.
intros HC Hx Hy.
pose proof (paper_main_data_exp_cubic x Hx) as HE.
pose proof (exp_pos (-x/2)) as Hp.
assert (Hprod : 0 <= x*exp(-x/2)) by nra.
pose proof (Rmult_le_compat_r (x*exp(-x/2)) _ _ Hprod Hy) as H1.
pose proof (Rmult_le_compat_l C _ _ HC HE) as H2.
apply (Rmult_le_reg_r x); [exact Hx|].
replace (216*C/x*x) with (216*C) by (field; lra).
nra.
Qed.

Theorem paper_main_data_radius_tends_to_zero (N : nat -> nat) C :
  0 <= C ->
  (exists D, forall d, Nat.le D d -> INR (N d) <= C*(INR d)^2) ->
  paper_main_tends_to
    (fun d => gaussian_product_law (Nat.mul (N d) d)
      (paper_main_data_radius_event (N d) d (2*sqrt (INR d)))) 0.
Proof.
intros HC [D HD] eps Heps.
have HepsR : 0 < eps by exact/RltP.
destruct (INR_unbounded (216*C/eps)) as [K HK].
exists (Nat.max D (S K)); intros d Hdd.
have HddN : Nat.le (Nat.max D (S K)) d by exact: (elimT ssrnat.leP Hdd).
assert (Hd : Nat.lt 0 d) by lia.
assert (Hdx : 0 < INR d) by (apply lt_0_INR; exact Hd).
assert (Hlarge : 216*C/eps < INR d).
{ pose proof (le_INR K d ltac:(lia)); lra. }
assert (Hrate : 216*C/INR d < eps).
{ apply (Rmult_lt_reg_r (INR d)); [exact Hdx|].
  replace (216*C/INR d*INR d) with (216*C) by (field; lra).
  pose proof (Rmult_lt_compat_r eps _ _ HepsR Hlarge) as H.
  replace (216*C/eps*eps) with (216*C) in H by (field; lra); nra. }
have HB := paper_main_data_radius_probability (N d) d Hd.
have HR := paper_main_data_radius_rate C (INR d) (INR (N d)) HC Hdx (HD d ltac:(lia)).
have Hbound : (gaussian_product_law (Nat.mul (N d) d)
    (paper_main_data_radius_event (N d) d (2*sqrt (INR d))) <= ((216*C/INR d)%Rcoq)%:E)%E.
{ eapply le_trans; first exact HB.
  rewrite lee_fin; apply/RleP.
  change (INR (N d)*exp(-INR d/2) <= 216*C/INR d); exact HR. }
have Hp : (0 <= gaussian_product_law (Nat.mul (N d) d)
  (paper_main_data_radius_event (N d) d (2*sqrt (INR d))))%E by exact: measure_ge0.
rewrite sube0 (gee0_abs Hp).
apply: le_lt_trans Hbound _.
rewrite lte_fin; apply/RltP.
change (216*C/INR d < eps); exact Hrate.
Qed.
