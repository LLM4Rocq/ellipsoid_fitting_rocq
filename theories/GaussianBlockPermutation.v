(* Port of the inner module GaussianBlockPermutation from Coquelicot to
   MathComp-Analysis.

   In theories/ this module exists only inside the bundles
   InterpolationProofs and JointProofs, whose two copies are identical. The
   copy extracted to build/agent2/unbundled/GaussianBlockPermutation.v is
   ported here as a standalone module.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and its text. The proofs are the original ones, word for word. The
   changes are in the import lines only.
   - "From Coquelicot Require Import Coquelicot." and "Import Coquelicot."
     are dropped: no statement or proof here names a Coquelicot notion.
   - The bundle imported GaussianCoordinateProofs and named its inner
     modules GaussianProduct, GaussianCoordinatePermutations,
     GaussianPermutationContinuity, GaussianPermutationWeights and
     GaussianCoordinateMove through it. Here the standalone ported modules
     of the same names are imported directly.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So (e <= n)%nat and (e < length xs)%nat are Peano's le
   and lt, and firstn, skipn, length, Forall2, Permutation and the
   operations on R are Stdlib's, as in the original. A module that imports
   this one after loading ssreflect must write (e <= n)%coq_nat to state the
   same bound.

   The meaning of the statements follows the ported definitions they use.
   The list lemmas (block_rotation_permutation, block_rotation_length,
   block_firstn_forall2, block_skipn_forall2, block_rotation_forall2,
   block_rotation_step) involve no analysis and say exactly what they said.
   finite_joint_continuous (GaussianCoordinateDefinitions) and
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) have their
   original texts, so finite_joint_continuous_block_rotation,
   finite_polynomial_bound_block_rotation,
   gaussian_block_rotation_continuous and
   gaussian_block_rotation_polynomial_bound also say what they said.
   gaussian_iterated_expectation (GaussianProductDefinitions) now takes at
   each level a Lebesgue integral over the line against the Gaussian kernel,
   in place of an improper Riemann integral (difference 4 of
   analysis/README.md). Under the hypotheses of
   gaussian_iterated_block_rotation_bounded and
   gaussian_iterated_block_rotation, F and its rotated version are
   continuous and bounded by a constant times a polynomial weight, so every
   function integrated is absolutely integrable against the kernel, where
   the Lebesgue and the improper Riemann values agree. The two theorems are
   therefore the same statements as before, about the same numbers. This
   agreement is a mathematical argument and is not proved in Rocq. The
   equalities themselves are proved here from the ported
   gaussian_iterated_move_last, whose statement is the original text. No
   statement is weakened. *)

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
