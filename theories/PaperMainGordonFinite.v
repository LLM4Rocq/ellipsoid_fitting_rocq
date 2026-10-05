(* Remove the finite soft-extrema approximation in Gaussian comparison. *)
From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions
  GaussianProduct GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCovarianceDefinitions GaussianCovarianceLinear
  GaussianCovarianceDomains PaperMainGordonCoordinates PaperMainGordonGrowth
  PaperMainGordonComparison.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_max_continuous K F G :
  finite_joint_continuous K F -> finite_joint_continuous K G ->
  finite_joint_continuous K (fun xs => Rmax (F xs) (G xs)).
Proof.
intros HF HG.
apply finite_joint_continuous_ext with
  (F := fun xs => (F xs + G xs + Rabs (F xs - G xs)) / 2).
- intros xs Hxs; unfold Rmax; destruct (Rle_dec (F xs) (G xs)).
  + rewrite Rabs_left1 by lra; field.
  + rewrite Rabs_right by lra; field.
- unfold Rdiv; apply finite_joint_continuous_mult; [|apply finite_joint_continuous_constant].
  apply finite_joint_continuous_add; [apply finite_joint_continuous_add; assumption|].
  apply finite_joint_continuous_abs, finite_joint_continuous_minus; assumption.
Qed.

Lemma paper_main_gordon_finite_max_continuous K (F : list R -> nat -> R) I :
  (forall i, In i I -> finite_joint_continuous K (fun xs => F xs i)) ->
  finite_joint_continuous K (fun xs => finite_max (F xs) I).
Proof.
induction I as [|i I IH]; intros HF.
- simpl; apply finite_joint_continuous_constant.
- destruct I as [|j I].
  + simpl; apply HF; simpl; auto.
  + change (finite_joint_continuous K (fun xs => Rmax (F xs i) (finite_max (F xs) (j :: I)))).
    apply paper_main_gordon_max_continuous.
    * apply HF; simpl; auto.
    * apply IH; intros k Hk; apply HF; simpl; auto.
Qed.

Definition paper_main_gordon_finite J Y S xs :=
  finite_minimax (paper_main_gordon_scores J xs) Y S.

Lemma paper_main_gordon_finite_continuous K J Y S :
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  finite_joint_continuous K (paper_main_gordon_finite J Y S).
Proof.
intros HJ.
unfold paper_main_gordon_finite, finite_minimax, finite_min.
apply finite_joint_continuous_ext with
  (F := fun xs => -1 * finite_max (fun y => -1 * finite_max (paper_main_gordon_scores J xs y) S) Y).
- intros xs Hxs.
  assert (HE : (fun y => -1 * finite_max (paper_main_gordon_scores J xs y) S) =
    (fun y => - finite_max (paper_main_gordon_scores J xs y) S)).
  { extensionality y; ring. }
  rewrite HE; ring.
- apply finite_joint_continuous_scale.
  apply paper_main_gordon_finite_max_continuous; intros y Hy.
  apply finite_joint_continuous_scale.
  apply paper_main_gordon_finite_max_continuous; intros s Hs.
  unfold paper_main_gordon_scores; apply finite_joint_continuous_nth; apply HJ; assumption.
Qed.

Lemma paper_main_gordon_finite_growth K J Y S :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  finite_polynomial_bound K 1 1 (paper_main_gordon_finite J Y S).
Proof.
intros HY HS HJ; split; [lra|]; intros xs Hxs.
rewrite Rmult_1_l.
apply paper_main_gordon_finite_value_bound; try assumption.
intros y s Hy Hs; unfold paper_main_gordon_scores.
apply coordinate_le_weight_one; rewrite Hxs; apply HJ; assumption.
Qed.

Lemma paper_main_gordon_finite_domain K p P J Y S :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  gaussian_covariance_domain p (fun xs =>
    paper_main_gordon_finite J Y S (gaussian_covariance_image K p P xs)).
Proof.
intros HY HS HJ.
apply (gaussian_covariance_image_domain K p P _ 1 1).
- apply paper_main_gordon_finite_continuous; exact HJ.
- apply paper_main_gordon_finite_growth; assumption.
Qed.

Lemma paper_main_gordon_expectation_error K p P beta gamma J Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  let E := gaussian_iterated_expectation p (fun xs =>
    paper_main_gordon_finite J Y S (gaussian_covariance_image K p P xs)) in
  let Es := gaussian_iterated_expectation p (fun xs =>
    paper_main_gordon_value beta gamma J Y S (gaussian_covariance_image K p P xs)) in
  E - Rpower.ln (INR (List.length Y)) / beta <= Es /\
  Es <= E + Rpower.ln (INR (List.length S)) / gamma.
Proof.
intros Hb Hg HY HS HJ E Es.
set (F := fun xs => paper_main_gordon_finite J Y S (gaussian_covariance_image K p P xs)).
set (G := fun xs => paper_main_gordon_value beta gamma J Y S (gaussian_covariance_image K p P xs)).
pose proof (proj1 (paper_main_gordon_finite_domain K p P J Y S HY HS HJ)) as HF.
pose proof (proj1 (paper_main_gordon_image_domain K p P beta gamma J Y S Hb Hg HY HS HJ)) as HG.
set (a := Rpower.ln (INR (List.length Y)) / beta).
set (b := Rpower.ln (INR (List.length S)) / gamma).
destruct (gaussian_iterated_constant p (-a)) as [Hca Eca].
destruct (gaussian_iterated_constant p b) as [Hcb Ecb].
destruct (gaussian_iterated_add p F (fun _ => -a) HF Hca) as [HFa EFa].
destruct (gaussian_iterated_add p F (fun _ => b) HF Hcb) as [HFb EFb].
assert (HL : gaussian_iterated_expectation p (fun xs => F xs + -a) <=
  gaussian_iterated_expectation p G).
{ apply gaussian_iterated_monotone; try assumption.
  intros xs Hxs; unfold F, G, paper_main_gordon_finite, paper_main_gordon_value, a.
  pose proof (proj1 (soft_minimax_bounds beta gamma
    (paper_main_gordon_scores J (gaussian_covariance_image K p P xs)) Y S Hb Hg HY HS)).
  lra. }
assert (HU : gaussian_iterated_expectation p G <=
  gaussian_iterated_expectation p (fun xs => F xs + b)).
{ apply gaussian_iterated_monotone; try assumption.
  intros xs Hxs; unfold F, G, paper_main_gordon_finite, paper_main_gordon_value, b.
  exact (proj2 (soft_minimax_bounds beta gamma
    (paper_main_gordon_scores J (gaussian_covariance_image K p P xs)) Y S Hb Hg HY HS)). }
rewrite EFa, Eca in HL.
rewrite EFb, Ecb in HU.
change (E + -a <= Es) in HL.
change (Es <= E + b) in HU.
lra.
Qed.

Theorem paper_main_gordon_finite_comparison K p q P Q J Y S :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  (forall y s t, In y Y -> In s S -> In t S ->
    gaussian_covariance_entry p P (J y s) (J y t) =
    gaussian_covariance_entry q Q (J y s) (J y t)) ->
  (forall y z s t, In y Y -> In z Y -> In s S -> In t S -> y <> z ->
    gaussian_covariance_entry q Q (J y s) (J z t) <=
    gaussian_covariance_entry p P (J y s) (J z t)) ->
  gaussian_covariance_domain p (fun xs =>
    paper_main_gordon_finite J Y S (gaussian_covariance_image K p P xs)) /\
  gaussian_covariance_domain q (fun xs =>
    paper_main_gordon_finite J Y S (gaussian_covariance_image K q Q xs)) /\
  gaussian_iterated_expectation q (fun xs =>
    paper_main_gordon_finite J Y S (gaussian_covariance_image K q Q xs)) <=
  gaussian_iterated_expectation p (fun xs =>
    paper_main_gordon_finite J Y S (gaussian_covariance_image K p P xs)).
Proof.
intros HY HS HJ Hsame Hcross.
split; [apply paper_main_gordon_finite_domain; assumption|].
split; [apply paper_main_gordon_finite_domain; assumption|].
set (Ep := gaussian_iterated_expectation p (fun xs =>
  paper_main_gordon_finite J Y S (gaussian_covariance_image K p P xs))).
set (Eq := gaussian_iterated_expectation q (fun xs =>
  paper_main_gordon_finite J Y S (gaussian_covariance_image K q Q xs))).
apply Rnot_lt_le; intros Hgap.
set (a := Rpower.ln (INR (List.length Y))).
set (b := Rpower.ln (INR (List.length S))).
set (c := Rabs a + Rabs b + 1).
assert (Hc : 0 < c) by (unfold c; pose proof (Rabs_pos a); pose proof (Rabs_pos b); lra).
set (t := 2 * c / (Eq - Ep)).
assert (Ht : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
pose proof (proj2 (proj2 (paper_main_gordon_soft_comparison
  K p q P Q t t J Y S Ht Ht HY HS HJ Hsame Hcross))) as HC.
pose proof (proj1 (paper_main_gordon_expectation_error K q Q t t J Y S Ht Ht HY HS HJ)) as HL.
pose proof (proj2 (paper_main_gordon_expectation_error K p P t t J Y S Ht Ht HY HS HJ)) as HU.
fold Eq a in HL.
fold Ep b in HU.
assert (Hbound : Eq - Ep <= (a + b) / t) by (unfold Rdiv in *; lra).
assert (Hprod : (Eq - Ep) * t = 2 * c) by (unfold t; field; lra).
assert (Hmul : (Eq - Ep) * t <= a + b).
{ apply (Rmult_le_reg_r (/ t)).
  - apply Rinv_0_lt_compat; exact Ht.
  - replace ((Eq - Ep) * t * / t) with (Eq - Ep) by (field; lra).
    exact Hbound. }
pose proof (Rle_abs a); pose proof (Rle_abs b).
pose proof (Rabs_pos a); pose proof (Rabs_pos b).
unfold c in Hprod; lra.
Qed.
