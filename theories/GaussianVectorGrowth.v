From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions GaussianDefinitions GaussianCoordinateWeightDefinitions VectorCoordinateDefinitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module GaussianVectorGrowth of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/GaussianVectorProofs.v) from Coquelicot to MathComp-Analysis.

   Every lemma keeps its name and its arguments, in the same order. The
   statements change form in four ways, none of which changes their meaning.

   1. Norms. Coquelicot's norm x becomes MathComp's (`|x|)%R. The vectors of
      OperatorDefinitions nest euclidean_product of MatrixEuclideanProduct, so
      the norm of a vector is still the Euclidean norm, as in Coquelicot, and
      the bounds below keep their constants.

   2. Pairs. Coquelicot's norm (x, y) on U * V is the norm of
      prod_NormedModule, sqrt (norm x ^ 2 + norm y ^ 2). MathComp puts the max
      norm on U * V, so vector_growth_pair_bound names the type of the pair,
      (x, y) : euclidean_product U V, whose norm is Coquelicot's formula.

   3. Differences. Coquelicot's minus x y becomes (x - y)%R of MathComp, which
      is also x plus the opposite of y, componentwise on the nested pairs.

   4. Indices and lists. With ssreflect loaded, (i <= n)%nat would mean
      ssrnat's boolean leq, and map, seq and nth would mean MathComp's
      functions on seq. The statements write (i <= n)%coq_nat, which is
      Stdlib's le as in the original, and List.map, List.seq and List.nth,
      which are the functions the original used. *)

(* On a vector of dimension 0, which is R^o, the norm is the absolute
   value. Added by the port: Coquelicot's norm on R is Rabs by definition,
   MathComp's is Num.norm, equal to Rabs by Rstruct's RabsE. *)
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
