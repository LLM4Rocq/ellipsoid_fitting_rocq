(* The Gaussian laws of the paper and the standard Gaussian measure gauss d
   of the library (GaussianAnalysis.gauss), on row vectors 'rV[R]_d, at
   Stdlib's R.
   - gauss d is the image of gaussian_product_law d of the statement, on
     d-tuples, under row_of_tuple, which sends a tuple to the row vector of
     its coordinates (gauss_gaussian_product_law). Both measures give a box
     the product of the standard normal measures of its sides (gauss_box
     and gpp_boxes), and a probability on row vectors is determined by its
     values on boxes (gaussE).
   - gaussian_iterated_expectation d F, the iterated expectation of a
     function of lists, is the integral of x |-> F (list_of_row x) against
     gauss d when F is continuous and integrable at every level of the
     iteration (gaussian_iterated_expectation_gauss), for instance when it
     grows at most polynomially (gaussian_iterated_expectation_gauss_poly).
   - list_of_row_continuous, list_of_row_bound and list_of_row_derive carry
     the continuity (finite_joint_continuous), the polynomial growth
     (finite_polynomial_bound) and the partial derivatives
     (finite_coordinate_derivative) of F over to x |-> F (list_of_row x), in
     the form that the library uses.
   Together they let a statement about gaussian_iterated_expectation follow
   from a result of the library about gauss d. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import normedtype derive arithmetic_tactic.
From GaussianAnalysis Require Import measurable_matrix gauss gauss_ibp.
From EllipsoidFitting Require Import GaussianProbabilityDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductMeasure.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions
  GaussianProbabilityProductIntegrals GaussianProbabilityProductContinuity
  GaussianCoordinateDefinitions GaussianCoordinateBasics GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinateMarginals
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCoordinateDerivativeDefinitions GaussianCoordinatePolynomialContinuity.
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

(* The coordinates of a row vector, as a tuple and as a list: the inverse
   of row_of_tuple, and the argument of a function of lists. *)
Section list_of_row.
Variable d : nat.

Definition tuple_of_row (x : 'rV[RR]_d) : d.-tuple (measurableTypeR R) :=
  [tuple (x 0 i : R) | i < d].

Definition list_of_row (x : 'rV[RR]_d) : list R := tval (tuple_of_row x).

Lemma tnth_tuple_of_row x i : tnth (tuple_of_row x) i = x 0 i.
Proof. by rewrite tnth_mktuple. Qed.

Lemma list_of_row_length x : length (list_of_row x) = d.
Proof. exact: size_tuple. Qed.

Lemma list_of_row_nth x (i : 'I_d) : List.nth i (list_of_row x) 0%R = x 0 i.
Proof. by rewrite gpp_nthE -tnth_nth tnth_tuple_of_row. Qed.

Lemma list_of_row_of_tuple t : list_of_row (row_of_tuple d t) = tval t.
Proof.
rewrite /list_of_row; congr tval; apply: eq_from_tnth => i.
by rewrite tnth_tuple_of_row row_of_tupleE.
Qed.

Lemma measurable_tuple_of_row : measurable_fun [set: 'rV[RR]_d] tuple_of_row.
Proof.
apply/measurable_fun_tnthP => i.
apply: (eq_measurable_fun (fun x : 'rV[RR]_d => x 0 i)).
  by move=> x _; rewrite /= tnth_tuple_of_row.
exact: measurable_mxentry.
Qed.

End list_of_row.

Arguments tuple_of_row {d}.
Arguments list_of_row {d}.
Arguments list_of_row_length {d}.
Arguments list_of_row_nth {d}.

Section translations.

(* Continuity, growth and partial derivatives of F carry over to the
   function x |-> F (list_of_row x) of row vectors. *)
Lemma list_of_row_continuous d (F : list R -> R) :
  finite_joint_continuous d F -> continuous (fun x : 'rV[RR]_d => F (list_of_row x) : RR).
Proof.
move=> HC x; rewrite /continuous_at.
apply/(@cvgrPdist_lt _ RR _ (nbhs x) (nbhs_filter x)) => e e0.
have [delta Hd] :=
  HC (coordinates_of_list d (list_of_row x)) (mkposreal e (elimT RltP e0)).
have d0 : (0 < pos delta)%R by apply/RltP; exact: cond_pos.
have := @cvgr_dist_lt _ _ _ (nbhs x) (nbhs_filter x) id x cvg_id _ d0.
apply: filterS => y hy /=.
have Lx := list_of_row_length x; have Ly := list_of_row_length y.
have := Hd (coordinates_of_list d (list_of_row y)).
rewrite !coordinates_list_roundtrip //= => H.
rewrite distrC -RabsE; apply/RltP; apply: H.
apply/(coordinates_close_lists d delta _ _ Ly Lx) => i /ltP id.
have -> : i = Ordinal id by [].
rewrite !list_of_row_nth RabsE; apply/RltP.
apply: (Order.POrderTheory.le_lt_trans _ hy); rewrite distrC.
by have := mx_norm_entry_le (x - y) 0 (Ordinal id); rewrite !mxE.
Qed.

Lemma list_of_row_bound d (F : list R -> R) C p : finite_polynomial_bound d C p F ->
  forall x : 'rV[RR]_d, `|F (list_of_row x)| <= C * 2 ^+ (p * d) * (1 + `|x| ^+ (p * d)).
Proof.
move=> [C0 HF] x; move/RleP: C0 => C0.
have := HF (list_of_row x) (list_of_row_length x); rewrite RabsE => /RleP H.
have Hw : gaussian_coordinate_product_weight p (list_of_row x) <= (1 + `|x|) ^+ (p * d).
  have := gaussian_coordinate_product_weight_box p (list_of_row x) `|x|.
  rewrite list_of_row_length RpowE => /(_ _ _)/RleP; apply.
    by apply/RleP; exact: normr_ge0.
  move=> y /in_map_iff [i [<- _]]; rewrite RabsE; apply/RleP.
  exact: mx_norm_entry_le.
apply: (Order.POrderTheory.le_trans H); rewrite -mulrA; apply: ler_wpM2l => //.
exact: (Order.POrderTheory.le_trans Hw (exprn1D_le _ (normr_ge0 x))).
Qed.

Lemma list_of_row_replace d (x : 'rV[RR]_d) (i : 'I_d) (h : R) :
  list_of_row (h *: delta_mx 0 i + x) = replace_coordinate i (h + x 0 i) (list_of_row x).
Proof.
apply: (nth_ext _ _ 0%R 0%R).
  by rewrite replace_coordinate_length !list_of_row_length.
move=> j; rewrite list_of_row_length => /ltP jd.
have -> : j = Ordinal jd by [].
rewrite list_of_row_nth !mxE; case: (eqVneq (Ordinal jd) i) => [<-|ji].
  rewrite replace_coordinate_nth_same; first by rewrite list_of_row_length; apply/ltP.
  by rewrite eqxx /= mulr1.
rewrite replace_coordinate_nth_other.
  by move=> E; move: ji; rewrite -val_eqE /= E eqxx.
by rewrite list_of_row_nth eqxx /= mulr0 add0r.
Qed.

Lemma list_of_row_derive d (F DF : list R -> R) (i : 'I_d) :
  finite_coordinate_derivative d i F DF ->
  forall x : 'rV[RR]_d,
    is_derive x (delta_mx 0 i) (fun x => F (list_of_row x) : RR) (DF (list_of_row x)).
Proof.
move=> HD x; have := HD (list_of_row x) (list_of_row_length x).
rewrite list_of_row_nth => H.
apply: (is_derive_transfer
  (G := fun t : RR => F (replace_coordinate i t (list_of_row x)) : RR)
  (b := x 0 i) (w := 1)).
by move=> h; rewrite list_of_row_replace /GRing.scale /= mulr1.
Qed.

End translations.

Section iterated_expectation.

(* gaussian_iterated_expectation d F is the integral of F, read on the list
   of the coordinates, against gauss d, whenever F is integrable at every
   level of the iterated expectation. *)
Theorem gaussian_iterated_expectation_gauss d (F : list R -> R) :
  finite_joint_continuous d F ->
  gaussian_iterated_integrable d F -> gaussian_iterated_absolutely_integrable d F ->
  (gauss d).-integrable [set: 'rV[RR]_d] (fun x => (F (list_of_row x))%:E) /\
  gaussian_iterated_expectation d F = \int[gauss d]_x F (list_of_row x).
Proof.
move=> HC HI HA.
have mT : measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun t => (F (tval t))%:E).
  by apply/measurable_EFinP; exact: gpp_joint_measurable.
have [iT eT] := gpp_all_sections d F mT HI HA.
have mf : measurable_fun [set: 'rV[RR]_d] (fun x => (F (list_of_row x))%:E).
  exact: (measurableT_comp mT (measurable_tuple_of_row d)).
have Ef : (fun x => (F (list_of_row x))%:E) \o row_of_tuple d =
    (fun t : d.-tuple (measurableTypeR R) => (F (tval t))%:E).
  by apply/funext => t /=; rewrite list_of_row_of_tuple.
have iF : (gauss d).-integrable [set: 'rV[RR]_d] (fun x => (F (list_of_row x))%:E).
  by apply/(@integrable_gauss_gaussian_product_law d _ mf); rewrite Ef.
split => //; rewrite /Rintegral (@integral_gauss_gaussian_product_law d _ iF).
by under eq_integral do rewrite list_of_row_of_tuple; rewrite eT.
Qed.

(* The same for F continuous with polynomial growth. *)
Corollary gaussian_iterated_expectation_gauss_poly d (F : list R -> R) C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  (gauss d).-integrable [set: 'rV[RR]_d] (fun x => (F (list_of_row x))%:E) /\
  gaussian_iterated_expectation d F = \int[gauss d]_x F (list_of_row x).
Proof.
move=> HC HB; have [HI [HA _]] := gaussian_iterated_polynomial_admissible d F C p HC HB.
exact: gaussian_iterated_expectation_gauss.
Qed.

End iterated_expectation.

Section stein.

(* Gaussian integration by parts for the iterated expectation, from
   gauss_ibp of the library. *)
Theorem gaussian_iterated_coordinate_stein_gauss d (i : nat) (F DF : list R -> R) C p D q :
  (i < d)%coq_nat ->
  finite_joint_continuous d F -> finite_joint_continuous d DF ->
  finite_polynomial_bound d C p F -> finite_polynomial_bound d D q DF ->
  finite_coordinate_derivative d i F DF ->
  gaussian_iterated_expectation d DF =
  gaussian_iterated_expectation d (fun xs => List.nth i xs 0 * F xs).
Proof.
move=> idc HCF HCD HF HD HdF; have id : (i < d)%N by apply/ltP.
pose i' := Ordinal id.
have HCxF := finite_joint_continuous_times_coordinate d F i HCF idc.
have HxF := finite_polynomial_bound_times_coordinate d C p F i HF idc.
rewrite (gaussian_iterated_expectation_gauss_poly _ _ _ _ HCD HD).2.
rewrite (gaussian_iterated_expectation_gauss_poly _ _ _ _ HCxF HxF).2.
(* A common polynomial bound for F and DF. *)
have HF' := finite_polynomial_bound_degree_monotone d C p (p + q) F HF
  (Nat.le_add_r p q).
have HD' := finite_polynomial_bound_degree_monotone d D q (p + q) DF HD
  (Nat.le_add_l q p).
have C0 : (0 <= C :> RR) by apply/RleP; case: HF.
have D0 : (0 <= D :> RR) by apply/RleP; case: HD.
set k := ((p + q) * d)%N.
have bF (x : 'rV[RR]_d) :
    `|F (list_of_row x) : RR| <= (C + D) * 2 ^+ k * (1 + `|x| ^+ k).
  apply: (Order.POrderTheory.le_trans (list_of_row_bound _ _ _ _ HF' x)).
  by rewrite -!mulrA ler_wpM2r // ?mulr_ge0 ?addr_ge0 ?exprn_ge0 // lerDl.
have bD (x : 'rV[RR]_d) :
    `|DF (list_of_row x) : RR| <= (C + D) * 2 ^+ k * (1 + `|x| ^+ k).
  apply: (Order.POrderTheory.le_trans (list_of_row_bound _ _ _ _ HD' x)).
  by rewrite -!mulrA ler_wpM2r // ?mulr_ge0 ?addr_ge0 ?exprn_ge0 // lerDr.
rewrite /Rintegral -(gauss_ibp (list_of_row_derive _ _ _ i' HdF)
  (list_of_row_continuous _ _ HCF) (list_of_row_continuous _ _ HCD) bF bD).
congr fine; apply: eq_integral => x _.
by rewrite (_ : i = i') // list_of_row_nth.
Qed.

End stein.
