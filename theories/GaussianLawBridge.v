(* The standard Gaussian measure of the library, gauss d on row vectors
   'rV[R]_d (GaussianAnalysis.gauss), agrees at Stdlib's R with the law
   gaussian_product_law d of the statement, on d-tuples: gauss d is the
   image of gaussian_product_law d under the map row_of_tuple, which sends
   a tuple to the row vector of its coordinates. Both measures give a box
   the product of the standard normal measures of its sides (gauss_box and
   gpp_boxes), and a probability on row vectors is determined by its values
   on boxes (gaussE). *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis Require Import measurable_matrix gauss.
From EllipsoidFitting Require Import GaussianProbabilityDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductMeasure.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Row vectors of Stdlib's reals, seen through their realType structure,
   which carries the measurable structure of MathComp-Analysis. *)
Local Notation RR := (R : realType).

Section row_of_tuple.
Variable d : nat.

(* The row vector of the coordinates of a tuple. *)
Definition row_of_tuple (t : d.-tuple (measurableTypeR R)) : 'rV[RR]_d :=
  \row_i (tnth t i : R).

Lemma row_of_tupleE t i : row_of_tuple t 0 i = tnth t i.
Proof. by rewrite mxE. Qed.

Lemma measurable_row_of_tuple :
  measurable_fun [set: d.-tuple (measurableTypeR R)] row_of_tuple.
Proof.
apply/measurable_fun_mxP => i j; under eq_fun do rewrite mxE.
by move=> _ Y mY; exact: (measurable_tnth j measurableT mY).
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ row_of_tuple measurable_row_of_tuple.

End row_of_tuple.

(* gauss d is the image of gaussian_product_law d under row_of_tuple. *)
Theorem gauss_gaussian_product_law d (X : set 'rV[RR]_d) : measurable X ->
  gauss d X = gaussian_product_law d (row_of_tuple d @^-1` X).
Proof.
move=> mX; symmetry.
apply: (@gaussE RR d (distribution (gaussian_product_law d) (row_of_tuple d)) _ X mX).
move=> A mA.
change (gaussian_product_law d
  (row_of_tuple d @^-1` [set x : 'rV[RR]_d | forall i, A i (x 0 i)]) =
  (\prod_(i < d) normal_prob 0 1 (A i))%E).
pose A' (k : nat) : set (measurableTypeR R) := oapp A setT (insub k : option 'I_d).
have A'E (i : 'I_d) : A' i = A i by rewrite /A' valK.
have -> : row_of_tuple d @^-1` [set x : 'rV[RR]_d | forall i, A i (x 0 i)] =
    gpp_box d A'.
  apply/seteqP; split => t /= H.
    move=> k kd; rewrite /A' insubT /= gpp_nthE.
    by have := H (Ordinal kd); rewrite row_of_tupleE (tnth_nth 0%R).
  move=> i; rewrite row_of_tupleE; have := H i (ltn_ord i).
  by rewrite A'E gpp_nthE (tnth_nth 0%R).
have mA' k : measurable (A' k).
  by rewrite /A'; case: insubP => [i _ _ /=|_ /=]; [exact: mA|exact: measurableT].
rewrite gpp_boxes// -prodEFin; apply: eq_bigr => i _.
by rewrite A'E fineK//; apply: fin_num_measure; exact: mA.
Qed.

Section gauss_gaussian_product_law_integral.
Local Open Scope ereal_scope.
Variable d : nat.

Lemma ge0_integral_gauss_gaussian_product_law (f : 'rV[RR]_d -> \bar R) :
  measurable_fun [set: 'rV[RR]_d] f -> (forall x, 0 <= f x) ->
  \int[gauss d]_x f x = \int[gaussian_product_law d]_t f (row_of_tuple d t).
Proof.
move=> mf f0.
rewrite -(@ge0_integral_distribution _ _ _ _ _ (gaussian_product_law d)
  (row_of_tuple d) f)//.
apply: eq_measure_integral => A mA _.
exact: gauss_gaussian_product_law.
Qed.

Lemma integrable_gauss_gaussian_product_law (f : 'rV[RR]_d -> \bar R) :
  measurable_fun [set: 'rV[RR]_d] f ->
  (gauss d).-integrable [set: 'rV[RR]_d] f <->
  (gaussian_product_law d).-integrable setT (f \o row_of_tuple d).
Proof.
move=> mf.
have mfa : measurable_fun [set: 'rV[RR]_d] (fun x => `|f x|).
  by apply: measurableT_comp.
have E := ge0_integral_gauss_gaussian_product_law (fun x => `|f x|) mfa
  (fun x => abse_ge0 (f x)).
have mfr : measurable_fun setT (f \o row_of_tuple d).
  exact: measurableT_comp mf (measurable_row_of_tuple d).
by split=> /integrableP[_ fi]; apply/integrableP; split => //;
  [rewrite -E|rewrite E].
Qed.

Lemma integral_gauss_gaussian_product_law (f : 'rV[RR]_d -> \bar R) :
  (gauss d).-integrable [set: 'rV[RR]_d] f ->
  \int[gauss d]_x f x = \int[gaussian_product_law d]_t f (row_of_tuple d t).
Proof.
move=> fi; have mf := measurable_int _ fi.
rewrite -(@integral_distribution _ _ _ _ _ (gaussian_product_law d)
  (row_of_tuple d) f)//.
  exact: ((integrable_gauss_gaussian_product_law f mf).1 fi).
by apply: eq_measure_integral => A mA _; exact: gauss_gaussian_product_law.
Qed.

End gauss_gaussian_product_law_integral.
