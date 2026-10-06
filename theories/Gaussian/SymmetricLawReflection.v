(* Sign symmetry of the standard Gaussian: E_d [F (- xs)] = E_d [F xs] for
   F continuous with a polynomial bound
   (paper_main_gaussian_iterated_reflect). Read on row vectors through
   Gaussian.LawBridge, - xs is list_of_row (- x), and gauss d is invariant
   under x |-> - x (integral_gauss_opp of the library). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.CoordinateWeightDefinitions Gaussian.IteratedExpectationDefinitions
  Gaussian.IteratedExpectation Analysis.CoordinatePermutationContinuity.
Import ListNotations GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Negation of a coordinate list. *)

Lemma paper_main_gaussian_neg_length (xs : list R) :
  List.length (List.map Ropp xs) = List.length xs.
Proof. exact: List.length_map. Qed.

Lemma paper_main_gaussian_neg_weight p (xs : list R) :
  gaussian_coordinate_product_weight p (List.map Ropp xs) =
    gaussian_coordinate_product_weight p xs.
Proof.
elim: xs => [|x xs IH] //=.
by rewrite IH /gaussian_coordinate_weight Rabs_Ropp.
Qed.

Lemma paper_main_gaussian_neg_polynomial_bound d C p F :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => F (List.map Ropp xs)).
Proof.
move=> [HC HF]; split; first exact: HC.
move=> xs Hxs.
rewrite -(paper_main_gaussian_neg_weight p xs).
apply: HF; by rewrite paper_main_gaussian_neg_length.
Qed.

Lemma paper_main_gaussian_neg_forall2 (e : R) xs ys :
  List.Forall2 (fun x y => Rabs (x - y) < e) xs ys ->
  List.Forall2 (fun x y => Rabs (x - y) < e) (List.map Ropp xs) (List.map Ropp ys).
Proof.
elim=> [|x y xs' ys' Hxy _ IH] /=; constructor => //.
by rewrite -Rabs_Ropp; replace (- (- x - - y)) with (x - y) by ring.
Qed.

Lemma paper_main_gaussian_neg_continuous d F :
  finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => F (List.map Ropp xs)).
Proof.
move=> HF.
apply: (finite_joint_continuous_list_map d d (List.map Ropp) F) => //.
- by move=> xs Hxs; rewrite paper_main_gaussian_neg_length.
- by move=> e xs ys _ _ H; exact: paper_main_gaussian_neg_forall2.
Qed.

From mathcomp Require Import matrix.
From GaussianAnalysis Require Import measurable_matrix gauss escape.
From EllipsoidFitting Require Import Gaussian.LawBridge.

Section iterated_reflect.
Local Notation RR := (R : realType).

Lemma paper_main_gaussian_list_of_row_opp d (x : 'rV[RR]_d) :
  List.map Ropp (list_of_row x) = list_of_row (- x)%R.
Proof.
apply: (List.nth_ext _ _ 0 0).
  by rewrite List.length_map !list_of_row_length.
move=> i; rewrite List.length_map list_of_row_length => /ssrnat.ltP id.
have Hi : (i < List.length (List.map Ropp (list_of_row x)))%coq_nat.
  by rewrite List.length_map list_of_row_length; apply/ssrnat.ltP.
rewrite (List.nth_indep _ 0 (- 0) Hi).
have -> : i = Ordinal id by [].
by rewrite List.map_nth !list_of_row_nth mxE.
Qed.

(* The iterated sign symmetry. *)
Theorem paper_main_gaussian_iterated_reflect d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_expectation d (fun xs => F (List.map Ropp xs)) =
    gaussian_iterated_expectation d F.
Proof.
move=> HF HB.
have HFn := paper_main_gaussian_neg_continuous d F HF.
have HBn := paper_main_gaussian_neg_polynomial_bound d C p F HB.
rewrite (proj2 (gaussian_iterated_expectation_gauss_poly _ _ _ _ HFn HBn)).
have [iF ->] := gaussian_iterated_expectation_gauss_poly _ _ _ _ HF HB.
under eq_Rintegral do rewrite paper_main_gaussian_list_of_row_opp.
rewrite /Rintegral; congr fine.
exact: (integral_gauss_opp iF).
Qed.

End iterated_reflect.
