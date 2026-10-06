From Stdlib Require Import Reals List Permutation Lia Lra.
From EllipsoidFitting Require Import Analysis.CoordinatePermutationDefinitions
  Analysis.CoordinatePermutations Gaussian.Coordinate.WeightDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Polynomial weights under permutations of the coordinates. The weight
   gaussian_coordinate_product_weight p xs, the product of the
   (1 + Rabs x) ^ p over the coordinates x of xs, does not change when xs is
   permuted (gaussian_coordinate_product_weight_permutation). So the
   polynomial bound finite_polynomial_bound is preserved when the
   coordinates are permuted (finite_polynomial_bound_permutation). *)

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
