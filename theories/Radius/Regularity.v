(* Regularity of gaussian_maximum_radius N d, the largest squared Euclidean
   norm among the N consecutive blocks of d coordinates of a list of N * d
   coordinates. It is jointly continuous (gaussian_maximum_radius_continuous)
   and lies between 0 and the sum of the squares of all the coordinates
   (gaussian_maximum_radius_bounds). So on a list xs of length N * d it is
   at most N * d * gaussian_coordinate_product_weight 2 xs
   (gaussian_maximum_radius_polynomial), and it and its absolute value have
   iterated Gaussian expectations (gaussian_maximum_radius_domain, from
   gaussian_iterated_polynomial_admissible of Gaussian.CoordinateMarginals). *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateTuples
  Analysis.CoordinateTopology Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Gaussian.CoordinateMarginals
  Analysis.CoordinatePermutationContinuity
  Gaussian.CoordinatePolynomialContinuity Radius.Definitions.
Import ListNotations.
Open Scope R_scope.

Lemma maximum_radius_forall2_firstn {A B : Type} (P : A -> B -> Prop) n xs ys :
  Forall2 P xs ys -> Forall2 P (firstn n xs) (firstn n ys).
Proof.
  revert xs ys; induction n; intros xs ys H; simpl; [constructor|].
  destruct H; simpl; constructor; auto.
Qed.

Lemma maximum_radius_forall2_skipn {A B : Type} (P : A -> B -> Prop) n xs ys :
  Forall2 P xs ys -> Forall2 P (skipn n xs) (skipn n ys).
Proof.
  revert xs ys; induction n; intros xs ys H; simpl; [exact H|].
  destruct H; simpl; [constructor|apply IHn; exact H0].
Qed.

Lemma maximum_radius_continuous_firstn d k F :
  finite_joint_continuous d F ->
  finite_joint_continuous (d+k) (fun xs => F (firstn d xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - intros xs H; rewrite length_firstn, H, Nat.min_l by lia; reflexivity.
  - intros e xs ys Hx Hy H; apply maximum_radius_forall2_firstn, H.
Qed.

Lemma maximum_radius_continuous_skipn d k F :
  finite_joint_continuous k F ->
  finite_joint_continuous (d+k) (fun xs => F (skipn d xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - intros xs H; rewrite length_skipn, H; lia.
  - intros e xs ys Hx Hy H; apply maximum_radius_forall2_skipn, H.
Qed.

Lemma maximum_radius_continuous_max d F G :
  finite_joint_continuous d F -> finite_joint_continuous d G ->
  finite_joint_continuous d (fun xs => Rmax (F xs) (G xs)).
Proof.
  intros HF HG.
  apply finite_joint_continuous_ext with
    (F := fun xs => (F xs + G xs + Rabs (F xs-G xs))/2).
  - intros xs Hxs; unfold Rmax; destruct (Rle_dec (F xs) (G xs)).
    + rewrite Rabs_left1 by lra; field.
    + rewrite Rabs_right by lra; field.
  - unfold Rdiv; apply finite_joint_continuous_mult; [|apply finite_joint_continuous_constant].
    apply finite_joint_continuous_add; [apply finite_joint_continuous_add; assumption|].
    apply finite_joint_continuous_abs, finite_joint_continuous_minus; assumption.
Qed.

Lemma maximum_radius_squares_nonnegative xs : 0 <= gaussian_sum_squares xs.
Proof. induction xs; simpl; nra. Qed.

Lemma maximum_radius_squares_append xs ys :
  gaussian_sum_squares (xs++ys) = gaussian_sum_squares xs + gaussian_sum_squares ys.
Proof. induction xs; simpl; [ring|rewrite IHxs; ring]. Qed.

Lemma maximum_radius_squares_continuous d :
  finite_joint_continuous d gaussian_sum_squares.
Proof.
  induction d as [|d IH].
  - apply finite_joint_continuous_ext with (F := fun _ => 0).
    + intros xs H; destruct xs; [reflexivity|discriminate].
    + apply finite_joint_continuous_constant.
  - apply finite_joint_continuous_ext with
      (F := fun xs => nth 0 xs 0 * nth 0 xs 0 + gaussian_sum_squares (skipn 1 xs)).
    + intros xs H; destruct xs; [discriminate|reflexivity].
    + apply finite_joint_continuous_add.
      * apply finite_joint_continuous_mult; apply finite_joint_continuous_nth; lia.
      * exact (maximum_radius_continuous_skipn 1 d gaussian_sum_squares IH).
Qed.

Theorem gaussian_maximum_radius_continuous N d :
  finite_joint_continuous (N*d) (gaussian_maximum_radius N d).
Proof.
  induction N as [|N IH]; simpl; [apply finite_joint_continuous_constant|].
  apply maximum_radius_continuous_max.
  - apply maximum_radius_continuous_firstn, maximum_radius_squares_continuous.
  - apply maximum_radius_continuous_skipn, IH.
Qed.

Lemma gaussian_maximum_radius_bounds N d xs :
  0 <= gaussian_maximum_radius N d xs <= gaussian_sum_squares xs.
Proof.
  revert xs; induction N as [|N IH]; intro xs; simpl.
  - pose proof (maximum_radius_squares_nonnegative xs); lra.
  - pose proof (IH (skipn d xs)) as [HL HU].
    pose proof (maximum_radius_squares_nonnegative (firstn d xs)) as HQ.
    pose proof (maximum_radius_squares_nonnegative (skipn d xs)) as HS.
    pose proof (maximum_radius_squares_append (firstn d xs) (skipn d xs)) as HE.
    rewrite firstn_skipn in HE.
    unfold Rmax; destruct Rle_dec; split; lra.
Qed.

Lemma maximum_radius_squares_polynomial xs :
  gaussian_sum_squares xs <= INR (length xs) * gaussian_coordinate_product_weight 2 xs.
Proof.
  induction xs as [|x xs IH]; simpl; [lra|].
  pose proof (gaussian_coordinate_product_weight_at_least_one 2 xs) as HW.
  pose proof (gaussian_coordinate_weight_at_least_one 2 x) as Hx.
  pose proof (pos_INR (length xs)) as Hn.
  assert (HX : x*x <= gaussian_coordinate_weight 2 x).
  { unfold gaussian_coordinate_weight; simpl.
    pose proof (Rabs_pos x).
    assert (Rabs x * Rabs x = x*x) by
      (rewrite <- Rabs_mult; apply Rabs_pos_eq; nra).
    nra. }
  change (x*x + gaussian_sum_squares xs <=
    INR (S (length xs)) * (gaussian_coordinate_weight 2 x * gaussian_coordinate_product_weight 2 xs)).
  pose proof (Rmult_le_compat_l (gaussian_coordinate_weight 2 x) 1
    (gaussian_coordinate_product_weight 2 xs) ltac:(lra) HW) as Htop.
  pose proof (Rmult_le_compat_l
    (INR (length xs)*gaussian_coordinate_product_weight 2 xs) 1
    (gaussian_coordinate_weight 2 x) ltac:(nra) Hx) as Htail.
  rewrite S_INR; nra.
Qed.

Theorem gaussian_maximum_radius_polynomial N d :
  finite_polynomial_bound (N*d) (INR (N*d)) 2 (gaussian_maximum_radius N d).
Proof.
  split; [apply pos_INR|].
  intros xs Hxs; destruct (gaussian_maximum_radius_bounds N d xs) as [H0 H1].
  rewrite Rabs_pos_eq by exact H0.
  eapply Rle_trans; [exact H1|].
  rewrite <- Hxs; apply maximum_radius_squares_polynomial.
Qed.

Theorem gaussian_maximum_radius_domain N d :
  gaussian_iterated_integrable (N*d) (gaussian_maximum_radius N d) /\
  gaussian_iterated_absolutely_integrable (N*d) (gaussian_maximum_radius N d) /\
  gaussian_iterated_has_expectation (N*d) (gaussian_maximum_radius N d)
    (gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d)) /\
  gaussian_iterated_has_expectation (N*d) (fun xs => Rabs (gaussian_maximum_radius N d xs))
    (gaussian_iterated_expectation (N*d) (fun xs => Rabs (gaussian_maximum_radius N d xs))).
Proof.
  destruct (gaussian_iterated_polynomial_admissible (N*d) (gaussian_maximum_radius N d)
    (INR (N*d)) 2 (gaussian_maximum_radius_continuous N d)
    (gaussian_maximum_radius_polynomial N d)) as [HI [HA [HV [HAV HB]]]].
  repeat split; assumption.
Qed.
