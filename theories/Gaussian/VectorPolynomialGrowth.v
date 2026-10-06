From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions GaussianDefinitions
  Gaussian.CoordinateWeightDefinitions Matrix.VectorListDefinitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Polynomial growth of functions of a vector, read on the list of its
   coordinates. The Euclidean norm of x : vector n is at most the sum of
   the absolute values of its S n coordinates (vector_norm_le_coordinate_l1,
   vector_of_list_norm_l1), so 1 + |x| is at most the product weight
   gaussian_coordinate_product_weight 1 of its coordinates
   (vector_norm_product_weight, vector_of_list_norm_product_weight). Hence,
   if |f x| <= C * (1 + |x|) ^ p, then f read on lists through
   vector_of_list satisfies finite_polynomial_bound (S n) C p
   (vector_polynomial_bound_pullback).

   The vectors of Matrix.OperatorDefinitions nest euclidean_product of
   Matrix.EuclideanProduct, so their norm (`|x|)%R is the Euclidean norm.
   vector_growth_pair_bound bounds by |x| + |y| the norm
   sqrt (|x| ^ 2 + |y| ^ 2) of a pair of type euclidean_product U V; a pair
   without this type would get MathComp's max norm. With ssreflect loaded,
   the statements write List.map and List.seq for Stdlib's functions on
   lists. *)

(* On a vector of dimension 0, which is R^o, the norm is the absolute
   value (RabsE of Rstruct). *)
Lemma vector_growth_norm_R (a : R^o) : (`|a|)%R = Rabs a.
Proof. by rewrite RabsE. Qed.

Lemma vector_growth_pair_bound {U V : normedModType R}
    (x : U) (y : V) :
  (`|(x, y) : euclidean_product U V|)%R <= (`|x|)%R + (`|y|)%R.
Proof.
  apply/RleP.
  exact: (euclidean_product_norm_le ((x, y) : euclidean_product U V)).
Qed.

Lemma vector_norm_le_coordinate_l1 n (x : vector n) :
  (`|x|)%R <= coordinate_sum n (fun i => Rabs (vector_entry n x i)).
Proof.
  induction n as [|n IH].
  - change ((`|x : R^o|)%R <= Rabs x).
    rewrite vector_growth_norm_R; lra.
  - destruct x as [a x].
    change ((`|(a, x) : euclidean_product R^o (vector_NormedModule n)|)%R <=
      Rabs a + coordinate_sum n (fun i => Rabs (vector_entry n x i))).
    eapply Rle_trans; [apply vector_growth_pair_bound |].
    rewrite vector_growth_norm_R.
    apply Rplus_le_compat_l; exact (IH x).
Qed.

Lemma vector_growth_coordinate_sum_list n (f : nat -> R) :
  coordinate_sum n f = fold_right Rplus 0 (List.map f (List.seq 0 (S n))).
Proof.
  revert f; induction n as [|n IH]; intro f.
  - simpl; ring.
  - change (f O + coordinate_sum n (fun i => f (S i)) =
      f O + fold_right Rplus 0 (List.map f (List.seq 1 (S n)))).
    rewrite -List.seq_shift List.map_map -IH; reflexivity.
Qed.

Lemma vector_growth_list_abs_sum_nonnegative xs :
  0 <= fold_right Rplus 0 (List.map Rabs xs).
Proof.
  induction xs as [|x xs IH]; simpl; [lra |].
  pose proof (Rabs_pos x); lra.
Qed.

Lemma vector_growth_list_sum_product xs :
  1 + fold_right Rplus 0 (List.map Rabs xs) <=
    gaussian_coordinate_product_weight 1 xs.
Proof.
  induction xs as [|x xs IH]; [simpl; lra |].
  cbn [gaussian_coordinate_product_weight List.map fold_right].
  unfold gaussian_coordinate_weight at 1; rewrite pow_1.
  pose proof (Rabs_pos x).
  pose proof (vector_growth_list_abs_sum_nonnegative xs); nra.
Qed.

Lemma vector_norm_product_weight n (x : vector n) :
  1 + (`|x|)%R <= gaussian_coordinate_product_weight 1 (vector_to_list n x).
Proof.
  pose proof (vector_norm_le_coordinate_l1 n x) as H.
  rewrite vector_growth_coordinate_sum_list in H.
  pose proof (vector_growth_list_sum_product (vector_to_list n x)) as K.
  eapply Rle_trans; [|exact K].
  unfold vector_to_list; rewrite List.map_map; apply Rplus_le_compat_l; exact H.
Qed.

Lemma vector_growth_product_weight_power p xs :
  gaussian_coordinate_product_weight p xs =
    gaussian_coordinate_product_weight 1 xs ^ p.
Proof.
  induction xs as [|x xs IH].
  - simpl; rewrite pow1; reflexivity.
  - cbn [gaussian_coordinate_product_weight].
    unfold gaussian_coordinate_weight; rewrite pow_1 Rpow_mult_distr -IH.
    reflexivity.
Qed.

Lemma vector_of_list_norm_l1 n xs :
  length xs = S n ->
  (`|vector_of_list n xs|)%R <= fold_right Rplus 0 (List.map Rabs xs).
Proof.
  revert xs; induction n as [|n IH]; intros [|a xs] HL; simpl in HL; try lia.
  - destruct xs as [|b xs]; simpl in HL; [|lia].
    change ((`|a : R^o|)%R <= Rabs a + 0).
    rewrite vector_growth_norm_R; lra.
  - change ((`|(a, vector_of_list n xs) :
        euclidean_product R^o (vector_NormedModule n)|)%R <=
      Rabs a + fold_right Rplus 0 (List.map Rabs xs)).
    eapply Rle_trans; [apply vector_growth_pair_bound |].
    rewrite vector_growth_norm_R.
    apply Rplus_le_compat_l; apply IH; lia.
Qed.

Lemma vector_of_list_norm_product_weight n xs :
  length xs = S n ->
  1 + (`|vector_of_list n xs|)%R <= gaussian_coordinate_product_weight 1 xs.
Proof.
  intro HL; pose proof (vector_of_list_norm_l1 n xs HL).
  pose proof (vector_growth_list_sum_product xs); lra.
Qed.

Lemma vector_polynomial_bound_pullback n C p (f : vector n -> R) :
  0 <= C -> (forall x, Rabs (f x) <= C * (1 + (`|x|)%R) ^ p) ->
  finite_polynomial_bound (S n) C p (fun xs => f (vector_of_list n xs)).
Proof.
  intros HC HF; split; [exact HC |].
  intros xs HL; specialize (HF (vector_of_list n xs)).
  pose proof (vector_of_list_norm_product_weight n xs HL) as HP.
  assert (HN : 0 <= (`|vector_of_list n xs|)%R)
    by (apply/RleP; apply normr_ge0).
  assert (HZ : 0 <= 1 + (`|vector_of_list n xs|)%R) by lra.
  pose proof (pow_incr (1 + (`|vector_of_list n xs|)%R)
    (gaussian_coordinate_product_weight 1 xs) p (conj HZ HP)) as HQ.
  rewrite -vector_growth_product_weight_power in HQ; nra.
Qed.
