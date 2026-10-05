From Stdlib Require Import Reals List Permutation Lia Lra.
From EllipsoidFitting Require Import GaussianCoordinatePermutationDefinitions
  GaussianCoordinatePermutations GaussianCoordinateWeightDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GaussianPermutationWeights.v from Coquelicot to
   MathComp-Analysis.

   The original did not import Coquelicot. It depended on it only through
   GaussianCoordinateWeightDefinitions, whose port has the same text and
   now reaches the Lebesgue integral through GaussianDefinitions. The names
   used here, gaussian_coordinate_weight, gaussian_coordinate_product_weight
   and finite_polynomial_bound, are finite products and bounds that do not
   involve an integral, so they mean what they meant. Every statement below
   is the original text, word for word, and the proofs are the original
   ones. No statement changed form.

   This module loads no MathComp library itself, so nth is Stdlib's
   List.nth and (i < length xs)%nat is Peano's lt, as in the original. A
   module that imports this one after MathComp and restates these lemmas
   must write List.nth and (i < length xs)%coq_nat to mean the same. *)

Lemma gaussian_coordinate_product_weight_permutation p xs ys :
  Permutation xs ys ->
  gaussian_coordinate_product_weight p xs = gaussian_coordinate_product_weight p ys.
Proof.
  intro H; induction H; simpl.
  - reflexivity.
  - rewrite IHPermutation; reflexivity.
  - ring.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma gaussian_coordinate_product_weight_swap p i xs :
  gaussian_coordinate_product_weight p (swap_adjacent i xs) =
    gaussian_coordinate_product_weight p xs.
Proof. apply gaussian_coordinate_product_weight_permutation, swap_adjacent_permutation. Qed.

Lemma gaussian_coordinate_product_weight_move_last p i xs :
  gaussian_coordinate_product_weight p (move_coordinate_last i xs) =
    gaussian_coordinate_product_weight p xs.
Proof. apply gaussian_coordinate_product_weight_permutation, move_coordinate_last_permutation. Qed.

Lemma finite_polynomial_bound_permutation d C p F transform :
  (forall xs, length xs = d -> Permutation (transform xs) xs) ->
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => F (transform xs)).
Proof.
  intros HT [HC HB]; split; [exact HC|].
  intros xs HL.
  pose proof (HT xs HL) as HP.
  specialize (HB (transform xs) ltac:(rewrite (Permutation_length HP); exact HL)).
  rewrite (gaussian_coordinate_product_weight_permutation p _ _ HP) in HB; exact HB.
Qed.

Lemma finite_polynomial_bound_swap_adjacent d C p F i :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => F (swap_adjacent i xs)).
Proof.
  apply finite_polynomial_bound_permutation; intros xs HL; apply swap_adjacent_permutation.
Qed.

Lemma finite_polynomial_bound_move_last d C p F i :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => F (move_coordinate_last i xs)).
Proof.
  apply finite_polynomial_bound_permutation; intros xs HL; apply move_coordinate_last_permutation.
Qed.

Lemma gaussian_coordinate_product_weight_replace p i value xs :
  (i < length xs)%nat ->
  gaussian_coordinate_product_weight p (replace_coordinate i value xs) *
      gaussian_coordinate_weight p (nth i xs 0) =
  gaussian_coordinate_product_weight p xs * gaussian_coordinate_weight p value.
Proof.
  revert xs; induction i; intros [|x xs] Hi; simpl in *; try lia.
  - ring.
  - specialize (IHi xs ltac:(lia)).
    rewrite !Rmult_assoc, IHi; reflexivity.
Qed.
