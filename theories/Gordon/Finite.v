(* Remove the finite soft-extrema approximation in Gaussian comparison. *)
From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.CoordinatePolynomialContinuity Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Gaussian.CovarianceDefinitions
  Gaussian.CovarianceLinearImages Gaussian.CovariancePathDomains
  Gordon.Coordinates Gordon.Growth Gordon.Comparison.
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
