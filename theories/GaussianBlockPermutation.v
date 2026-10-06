(* Rotating a block of coordinates does not change an iterated Gaussian
   expectation. The rotation by e of a list xs is
   skipn e xs ++ firstn e xs: the first e coordinates move to the end. If
   F is jointly continuous and polynomially bounded, its iterated Gaussian
   expectation equals that of F composed with the rotation
   (gaussian_iterated_block_rotation_bounded, for n coordinates and
   e <= n, and gaussian_iterated_block_rotation, for e + d coordinates).
   The rotated function keeps both properties
   (gaussian_block_rotation_continuous,
   gaussian_block_rotation_polynomial_bound). The proof rotates one
   coordinate at a time (block_rotation_step), moving the first coordinate
   to the last place with gaussian_iterated_move_last. *)

From Stdlib Require Import Reals List Permutation Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinatePermutationDefinitions.
From EllipsoidFitting Require Import GaussianProduct GaussianCoordinatePermutations
  GaussianPermutationContinuity GaussianPermutationWeights
  GaussianCoordinateMove.
Import ListNotations.
Open Scope R_scope.

Lemma block_rotation_permutation {A : Type} e (xs : list A) :
  Permutation (skipn e xs ++ firstn e xs) xs.
Proof.
  transitivity (firstn e xs ++ skipn e xs).
  - apply Permutation_app_comm.
  - rewrite firstn_skipn; reflexivity.
Qed.

Lemma block_rotation_length {A : Type} e (xs : list A) :
  length (skipn e xs ++ firstn e xs) = length xs.
Proof. apply Permutation_length, block_rotation_permutation. Qed.

Lemma block_firstn_forall2 {A B : Type} (P : A -> B -> Prop) e xs ys :
  Forall2 P xs ys -> Forall2 P (firstn e xs) (firstn e ys).
Proof.
  intro H; revert e; induction H; intros [|e]; simpl; constructor; auto.
Qed.

Lemma block_skipn_forall2 {A B : Type} (P : A -> B -> Prop) e xs ys :
  Forall2 P xs ys -> Forall2 P (skipn e xs) (skipn e ys).
Proof.
  intro H; revert e; induction H; intros [|e]; simpl; auto; constructor; auto.
Qed.

Lemma block_rotation_forall2 {A B : Type} (P : A -> B -> Prop) e xs ys :
  Forall2 P xs ys ->
  Forall2 P (skipn e xs ++ firstn e xs) (skipn e ys ++ firstn e ys).
Proof.
  intro H; apply Forall2_app; [apply block_skipn_forall2|apply block_firstn_forall2]; exact H.
Qed.

Lemma finite_joint_continuous_block_rotation n e F :
  finite_joint_continuous n F ->
  finite_joint_continuous n (fun xs => F (skipn e xs ++ firstn e xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - intros xs HL; rewrite block_rotation_length; exact HL.
  - intros eps xs ys Hx Hy H; apply block_rotation_forall2; exact H.
Qed.

Lemma finite_polynomial_bound_block_rotation n e C p F :
  finite_polynomial_bound n C p F ->
  finite_polynomial_bound n C p (fun xs => F (skipn e xs ++ firstn e xs)).
Proof.
  apply finite_polynomial_bound_permutation; intros xs HL; apply block_rotation_permutation.
Qed.

Lemma block_rotation_step e (xs : list R) : (e < length xs)%nat ->
  skipn (S e) xs ++ firstn (S e) xs =
    skipn e (move_coordinate_last 0 xs) ++ firstn e (move_coordinate_last 0 xs).
Proof.
  destruct xs as [|x xs]; simpl; [lia|].
  intro He.
  rewrite skipn_app, firstn_app.
  replace (e - length xs)%nat with 0%nat by lia.
  simpl; rewrite app_nil_r; rewrite <- app_assoc; reflexivity.
Qed.

Lemma gaussian_iterated_block_rotation_bounded n e F C p :
  (e <= n)%nat -> finite_joint_continuous n F -> finite_polynomial_bound n C p F ->
  gaussian_iterated_expectation n F =
    gaussian_iterated_expectation n (fun xs => F (skipn e xs ++ firstn e xs)).
Proof.
  revert n F C; induction e as [|e IH]; intros n F C He HC HB.
  - apply gaussian_iterated_expectation_ext; intros xs Hxs; simpl; now rewrite app_nil_r.
  - transitivity (gaussian_iterated_expectation n (fun xs => F (skipn e xs ++ firstn e xs))).
    + apply (IH n F C); [lia|exact HC|exact HB].
    + transitivity (gaussian_iterated_expectation n (fun xs =>
        F (skipn e (move_coordinate_last 0 xs) ++ firstn e (move_coordinate_last 0 xs)))).
      * apply (gaussian_iterated_move_last n 0 (fun xs => F (skipn e xs ++ firstn e xs)) C p); [lia| |].
        -- apply finite_joint_continuous_block_rotation; exact HC.
        -- apply finite_polynomial_bound_block_rotation; exact HB.
      * apply gaussian_iterated_expectation_ext; intros xs Hxs.
        rewrite <- block_rotation_step by lia; reflexivity.
Qed.

Theorem gaussian_block_rotation_continuous d e F :
  finite_joint_continuous (e+d) F ->
  finite_joint_continuous (e+d) (fun xs => F (skipn e xs ++ firstn e xs)).
Proof. apply finite_joint_continuous_block_rotation. Qed.

Theorem gaussian_block_rotation_polynomial_bound d e C p F :
  finite_polynomial_bound (e+d) C p F ->
  finite_polynomial_bound (e+d) C p (fun xs => F (skipn e xs ++ firstn e xs)).
Proof. apply finite_polynomial_bound_block_rotation. Qed.

Theorem gaussian_iterated_block_rotation d e F C p :
  finite_joint_continuous (e+d) F -> finite_polynomial_bound (e+d) C p F ->
  gaussian_iterated_expectation (e+d) F =
    gaussian_iterated_expectation (e+d) (fun xs => F (skipn e xs ++ firstn e xs)).
Proof. intros HC HB; apply (gaussian_iterated_block_rotation_bounded (e+d) e F C p); [lia|exact HC|exact HB]. Qed.
