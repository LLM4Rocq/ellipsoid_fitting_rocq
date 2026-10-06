(* The Gaussian laws of the paper and the standard Gaussian measure gauss d
   of the library (GaussianAnalysis.gauss), on row vectors 'rV[R]_d, at
   Stdlib's R.
   - gauss d is the image of gaussian_product_law d of the statement, on
     d-tuples, under row_of_tuple, which sends a tuple to the row vector of
     its coordinates (gauss_gaussian_product_law). Both measures give a box
     the product of the standard normal measures of its sides (gauss_box
     and gpp_boxes), and a probability on row vectors is determined by its
     values on boxes (gauss_unique).
   - gaussian_iterated_expectation d F, the iterated expectation of a
     function of lists, is the integral of x |-> F (list_of_row x) against
     gauss d when F is continuous and integrable at every level of the
     iteration (gaussian_iterated_expectation_gauss), for instance when it
     grows at most polynomially (gaussian_iterated_expectation_gauss_poly).
     That a continuous function of polynomial growth is integrable at every
     level (gaussian_iterated_polynomial_integrable_gauss) comes from the
     library: x |-> F (list_of_row x) is integrable against gauss d
     (integrable_gauss_poly), and the integral over the first coordinate of
     an integrable function is integrable (Fubini, integrable_fubini_F).
   - list_of_row_continuous, list_of_row_bound and list_of_row_derive carry
     the continuity (finite_joint_continuous), the polynomial growth
     (finite_polynomial_bound) and the partial derivatives
     (finite_coordinate_derivative) of F over to x |-> F (list_of_row x), in
     the form that the library uses; finite_joint_continuous_of_row is the
     converse of list_of_row_continuous.
   - Results of the paper follow in this way from the library: the
     coordinate Stein identities of order one and two
     (gaussian_iterated_coordinate_stein_gauss and
     gaussian_iterated_coordinate_second_stein_gauss, from gauss_ibp and
     gauss_ibp2); the invariance of gaussian_iterated_expectation under a
     permutation of the coordinates (gaussian_iterated_col_perm_gauss, from
     integral_gauss_col_perm), applied to the rotation of a block
     (gaussian_iterated_block_rotation_gauss); and the joint
     continuity of the expectation over the last coordinate
     (gaussian_last_marginal_continuous_gauss, from the continuity of a
     parameter integral, continuity_under_integral_at).
   - In one dimension, gaussian_quadratic_exponential_has_integral_gauss
     gives the Gaussian integral of exp (t x^2) for t < 1/2 from
     integral_normal_expR_sqr of the library. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import normedtype derive sequences exp.
From Stdlib Require Import Lra.
From GaussianAnalysis Require Import measurable_matrix normal_integral gauss.
From GaussianAnalysis Require Import gauss_ibp parameter_integral.
From GaussianAnalysis Require Import chi_square.
From EllipsoidFitting Require Import GaussianProbabilityDefinitions
  GaussianProbabilityProductDefinitions Gaussian.Law.ProductBasics.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.Iterated.Definitions Gaussian.Law.ProductIntegrals
  Analysis.ContinuousTupleMeasurability
  Analysis.CoordinateContinuityDefinitions Gaussian.Coordinate.Tuples
  Analysis.CoordinateTopology Gaussian.Coordinate.WeightDefinitions
  Gaussian.Coordinate.Weights Gaussian.Iterated.SuffixAlgebra
  Gaussian.Iterated.SuffixMarginalDefinitions
  Analysis.CoordinatePermutationDefinitions Analysis.CoordinatePermutations
  Gaussian.Coordinate.DerivativeDefinitions
  Gaussian.Coordinate.PolynomialContinuity
  Analysis.CoordinatePermutationContinuity
  Gaussian.Coordinate.PermutationWeights Gaussian.Law.NormalDensity
  Gaussian.Law.NormalIntegrals.
From EllipsoidFitting Require Import Analysis.RealsBridge.
From EllipsoidFitting Require Gaussian.Line.Mass.
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
apply: (@gauss_unique RR d
  (distribution (gaussian_product_law d) (row_of_tuple d)) _ X mX).
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

Section list_of_row_cons.
Variable d : nat.

(* The coordinates of rV_cons (t, v) are t followed by those of v. *)
Lemma list_of_row_cons (t : R) (v : 'rV[RR]_d) :
  list_of_row (rV_cons (t, v)) = t :: list_of_row v.
Proof.
rewrite /list_of_row -[t :: _]/(tval [tuple of t :: tuple_of_row v]).
congr tval; apply: eq_from_tnth => i; rewrite tnth_tuple_of_row.
case: (unliftP ord0 i) => [j ->|->]; last by rewrite tnth0 rV_cons0.
by rewrite tnthS rV_consS tnth_tuple_of_row.
Qed.

(* The row vector of the first d entries of a list. *)
Definition row_of_list (xs : list R) : 'rV[RR]_d := \row_i (List.nth i xs 0%R : R).

Lemma list_of_row_of_list xs : length xs = d -> list_of_row (row_of_list xs) = xs.
Proof.
move=> Hl; apply: (nth_ext _ _ 0%R 0%R); first by rewrite list_of_row_length.
move=> j; rewrite list_of_row_length => /ltP jd.
have -> : j = Ordinal jd by [].
by rewrite list_of_row_nth mxE.
Qed.

End list_of_row_cons.

Arguments row_of_list d xs : clear implicits.

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

(* The converse of list_of_row_continuous: F is jointly continuous on the
   lists of length d when x |-> F (list_of_row x) is continuous. *)
Lemma finite_joint_continuous_of_row d (F : list R -> R) :
  continuous (fun x : 'rV[RR]_d => F (list_of_row x) : RR) ->
  finite_joint_continuous d F.
Proof.
move=> HC z eps; set xs := coordinates_to_list d z.
have Lxs : length xs = d := coordinates_to_list_length d z.
set x0 := row_of_list d xs.
have e0 : (0 < eps :> RR) by apply/RltP; exact: cond_pos.
have := (@cvgrPdist_lt _ RR _ (nbhs x0) (nbhs_filter x0)
  (fun x : 'rV[RR]_d => F (list_of_row x) : RR) _).1 (HC x0) _ e0 => H.
have /nbhs_ballP[delta /= d0 Hd] : nbhs x0
  [set x : 'rV[RR]_d | `|F (list_of_row x0) - F (list_of_row x) : RR| < eps].
  exact: H.
have d0' : Rlt 0 delta by apply/RltP.
exists (mkposreal delta d0') => w Hw.
set ys := coordinates_to_list d w.
have Lys : length ys = d := coordinates_to_list_length d w.
have bxy : ball x0 delta (row_of_list d ys).
  rewrite -ball_normE /ball_ /=.
  have -> : `|x0 - row_of_list d ys| =
      \big[Num.max/0]_ij `|(x0 - row_of_list d ys) ij.1 ij.2|.
    by rewrite -mx_normrE.
  apply: Order.PreorderTheory.bigmax_lt => // -[i j] _ /=.
  rewrite (ord1 i) /x0 /row_of_list !mxE.
  have jd : (j < d)%coq_nat by apply/ltP.
  have := (coordinates_close_iff d delta w z).1 Hw j jd.
  by rewrite RabsE => /RltP; rewrite distrC.
have := Hd _ bxy; rewrite /= /x0 !list_of_row_of_list // -RabsE => /RltP.
by rewrite Rabs_minus_sym.
Qed.

(* x |-> F (list_of_row x) is integrable against gauss d when F is
   continuous with polynomial growth. *)
Lemma integrable_gauss_list_of_row d (F : list R -> R) C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  (gauss d).-integrable [set: 'rV[RR]_d] (fun x => (F (list_of_row x))%:E).
Proof.
move=> HC HB.
have mF : measurable_fun [set: 'rV[RR]_d] (fun x => F (list_of_row x) : RR).
  exact: continuous_measurable_mx (list_of_row_continuous _ _ HC).
exact: (integrable_gauss_poly mF (list_of_row_bound _ _ _ _ HB)).
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

Let finite_polynomial_bound_Rabs d C p (F : list R -> R) :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => Rabs (F xs)).
Proof. by move=> [C0 HB]; split=> // xs Hxs; rewrite Rabs_Rabsolu; exact: HB. Qed.

(* A continuous function of polynomial growth is integrable at every level
   of the iterated expectation. By induction on d: the sections F (t :: _)
   are such functions, and the outer function t |-> E [F (t :: _)] is the
   integral over the second factor of x |-> F (list_of_row x), which is
   integrable against gauss d.+1 = law of rV_cons under normal_prob 0 1
   \x gauss d, so it is integrable against the normal law by Fubini. *)
Theorem gaussian_iterated_polynomial_integrable_gauss d (F : list R -> R) C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F.
Proof.
elim: d F C => [|d IH] F C HC HB; first by [].
rewrite /=.
have sec t : finite_joint_continuous d (fun xs => F (t :: xs)) /\
    finite_polynomial_bound d (C * gaussian_coordinate_weight p t) p
      (fun xs => F (t :: xs)).
  by split; [exact: finite_joint_continuous_head|exact: finite_polynomial_bound_head].
split=> [t|]; first by case: (sec t) => HC' HB'; exact: (IH _ _ HC' HB').
set g := fun t : R => gaussian_iterated_expectation d (fun xs => F (t :: xs)).
have secE t : (gauss d).-integrable [set: 'rV[RR]_d]
      (fun v => (F (t :: list_of_row v))%:E) /\
    g t = \int[gauss d]_v (F (t :: list_of_row v) : RR).
  case: (sec t) => HC' HB'.
  exact: (gaussian_iterated_expectation_gauss _ _ HC' (IH _ _ HC' HB')
    (IH _ _ (finite_joint_continuous_abs _ _ HC')
      (finite_polynomial_bound_Rabs _ _ _ _ HB'))).
have iF := integrable_gauss_list_of_row _ _ _ _ HC HB.
have iG : (normal_prob 0 1 \x gauss d)%E.-integrable
    [set: measurableTypeR R * 'rV[RR]_d] (fun q => (F (q.1 :: list_of_row q.2))%:E).
  apply: (eq_integrable measurableT _ _ _
    ((integrable_gauss_cons (measurable_int _ iF)).1 iF)).
  by move=> -[t v] _ /=; rewrite list_of_row_cons.
apply/gpb_integrable_iff; rewrite /gaussian_law_integrable.
apply: (eq_integrable measurableT _ _ _ (integrable_fubini_F iG)) => t _.
rewrite /fubini_F /= (secE t).2 /Rintegral fineK //.
exact: (integrable_fin_num measurableT (secE t).1).
Qed.

(* The same for F continuous with polynomial growth. *)
Corollary gaussian_iterated_expectation_gauss_poly d (F : list R -> R) C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  (gauss d).-integrable [set: 'rV[RR]_d] (fun x => (F (list_of_row x))%:E) /\
  gaussian_iterated_expectation d F = \int[gauss d]_x F (list_of_row x).
Proof.
move=> HC HB; apply: gaussian_iterated_expectation_gauss => //.
  exact: (gaussian_iterated_polynomial_integrable_gauss _ _ _ _ HC HB).
exact: (gaussian_iterated_polynomial_integrable_gauss _ _ _ _
  (finite_joint_continuous_abs _ _ HC) (finite_polynomial_bound_Rabs _ _ _ _ HB)).
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

Section second_stein.

(* Second-order Gaussian integration by parts for the iterated expectation,
   from gauss_ibp2 of the library. *)
Theorem gaussian_iterated_coordinate_second_stein_gauss d (i : nat)
    (F DF DDF : list R -> R) C p D q E r :
  (i < d)%coq_nat ->
  finite_joint_continuous d F -> finite_joint_continuous d DDF ->
  finite_polynomial_bound d C p F -> finite_polynomial_bound d D q DF ->
  finite_polynomial_bound d E r DDF ->
  finite_coordinate_derivative d i F DF ->
  finite_coordinate_derivative d i DF DDF ->
  gaussian_iterated_expectation d DDF =
  gaussian_iterated_expectation d
    (fun xs => (List.nth i xs 0 * List.nth i xs 0 - 1) * F xs).
Proof.
move=> idc HCF HCDD HF HD HDD HdF HdDF; have id : (i < d)%N by apply/ltP.
pose i' := Ordinal id.
have HCx := finite_joint_continuous_times_centered_square d F i HCF idc.
have HBx := finite_polynomial_bound_times_centered_square d C p F i HF idc.
rewrite (gaussian_iterated_expectation_gauss_poly _ _ _ _ HCDD HDD).2.
rewrite (gaussian_iterated_expectation_gauss_poly _ _ _ _ HCx HBx).2.
(* A common polynomial bound for F, DF and DDF. *)
have HF' := finite_polynomial_bound_degree_monotone d C p (p + q + r) F HF
  ltac:(by apply/leP; rewrite -addnA leq_addr).
have HD' := finite_polynomial_bound_degree_monotone d D q (p + q + r) DF HD
  ltac:(by apply/leP; apply: (leq_trans (leq_addl p q)); exact: leq_addr).
have HDD' := finite_polynomial_bound_degree_monotone d E r (p + q + r) DDF HDD
  ltac:(by apply/leP; exact: leq_addl).
have C0 : (0 <= C :> RR) by apply/RleP; case: HF.
have D0 : (0 <= D :> RR) by apply/RleP; case: HD.
have E0 : (0 <= E :> RR) by apply/RleP; case: HDD.
set k := ((p + q + r) * d)%N.
have bnd (G : list R -> R) (c : R) : finite_polynomial_bound d c (p + q + r) G ->
    (0 <= c :> RR) -> (c <= C + D + E :> RR) ->
    forall x : 'rV[RR]_d,
      `|G (list_of_row x) : RR| <= (C + D + E) * 2 ^+ k * (1 + `|x| ^+ k).
  move=> HG c0 cle x.
  apply: (Order.POrderTheory.le_trans (list_of_row_bound _ _ _ _ HG x)).
  by rewrite -!mulrA ler_wpM2r // ?mulr_ge0 ?addr_ge0 ?exprn_ge0.
have bF := bnd F C HF' C0 ltac:(by rewrite -addrA lerDl addr_ge0).
have bD := bnd DF D HD' D0 ltac:(by rewrite addrAC lerDr addr_ge0).
have bDD := bnd DDF E HDD' E0 ltac:(by rewrite lerDr addr_ge0).
rewrite /Rintegral -(gauss_ibp2 (list_of_row_derive _ _ _ i' HdF)
  (list_of_row_derive _ _ _ i' HdDF)
  (continuous_measurable_mx (list_of_row_continuous _ _ HCF))
  (list_of_row_continuous _ _ HCDD) bF bD bDD).
congr fine; apply: eq_integral => x _.
by rewrite (_ : i = i') // list_of_row_nth expr2.
Qed.

End second_stein.

Section permutation.

(* The iterated expectation of F is that of F composed with a permutation
   P of the coordinates, when F and the composite are continuous with
   polynomial growth: both are integrals against gauss d, which is invariant
   under permutations of the coordinates (integral_gauss_col_perm). s is the
   same permutation on the columns of a row vector. *)
Theorem gaussian_iterated_col_perm_gauss d (s : 'S_d) (P : list R -> list R)
    (F : list R -> R) C p C' p' :
  (forall x : 'rV[RR]_d, list_of_row (col_perm s x) = P (list_of_row x)) ->
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  finite_joint_continuous d (fun xs => F (P xs)) ->
  finite_polynomial_bound d C' p' (fun xs => F (P xs)) ->
  gaussian_iterated_expectation d F =
    gaussian_iterated_expectation d (fun xs => F (P xs)).
Proof.
move=> HP HC HB HC' HB'.
have [iF eF] := gaussian_iterated_expectation_gauss_poly _ _ _ _ HC HB.
rewrite eF (gaussian_iterated_expectation_gauss_poly _ _ _ _ HC' HB').2.
under [RHS]eq_Rintegral do rewrite -HP.
by rewrite /Rintegral (integral_gauss_col_perm s iF).
Qed.

End permutation.

(* The rotation of a list by e places, skipn e xs ++ firstn e xs, is the
   permutation j |-> (j + e) mod n of the columns of a row vector. *)
Section rotation.
Variable n : nat.

Let rot_ord_proof e (j : 'I_n) : ((j + e) %% n < n)%N.
Proof. by rewrite ltn_mod; exact: (leq_ltn_trans (leq0n _) (ltn_ord j)). Qed.

Definition rot_ord e (j : 'I_n) : 'I_n := Ordinal (rot_ord_proof e j).

Lemma rot_ord_inj e : injective (rot_ord e).
Proof.
move=> j k /(congr1 val) /= /eqP; rewrite eqn_modDr !modn_small ?ltn_ord //.
by move/eqP => jk; exact: val_inj.
Qed.

Definition rot_perm e : 'S_n := perm (rot_ord_inj e).

Let lengthE (s : list R) : length s = size s.
Proof. by elim: s => //= ? ? ->. Qed.

Let skipnE (s : list R) e : List.skipn e s = drop e s.
Proof. by elim: s e => [|a s IH] [|e] //=. Qed.

Let firstnE (s : list R) e : List.firstn e s = take e s.
Proof. by elim: s e => [|a s IH] [|e] //=; rewrite IH. Qed.

Let appE (s t : list R) : (s ++ t)%list = s ++ t.
Proof. by elim: s => //= ? ? ->. Qed.

Let nth_rot_mod (xs : seq R) e j : size xs = n -> (e <= n)%N -> (j < n)%N ->
  nth 0%R (rot e xs) j = nth 0%R xs ((j + e) %% n).
Proof.
move=> sz en jn; rewrite /rot nth_cat size_drop sz; case: ltnP => [jne|nej].
  have ejn : (j + e < n)%N by rewrite addnC -ltn_subRL.
  by rewrite nth_drop (modn_small ejn) addnC.
have -> : (j + e = j - (n - e) + n)%N.
  by rewrite -{2}(subnK en) addnA subnK.
rewrite modnDr modn_small.
  by rewrite ltn_subLR // (leq_trans jn) // leq_addl.
by rewrite nth_take // ltn_subLR // subnK.
Qed.

Lemma list_of_row_rot e (x : 'rV[RR]_n) : (e <= n)%N ->
  list_of_row (col_perm (rot_perm e) x) = rot e (list_of_row x).
Proof.
move=> en; apply: (nth_ext _ _ 0%R 0%R).
  by rewrite !lengthE size_rot -!lengthE !list_of_row_length.
move=> j; rewrite list_of_row_length => /ltP jn.
have -> : j = Ordinal jn by [].
have sz : size (list_of_row x) = n by rewrite -lengthE list_of_row_length.
rewrite list_of_row_nth mxE permE /= !gpp_nthE (nth_rot_mod _ _ _ sz en jn).
by rewrite -(list_of_row_nth x (rot_ord e (Ordinal jn))) gpp_nthE.
Qed.

Theorem gaussian_iterated_block_rotation_gauss e (F : list R -> R) C p C' p' :
  (e <= n)%coq_nat -> finite_joint_continuous n F ->
  finite_polynomial_bound n C p F ->
  finite_joint_continuous n
    (fun xs => F (List.skipn e xs ++ List.firstn e xs)%list) ->
  finite_polynomial_bound n C' p'
    (fun xs => F (List.skipn e xs ++ List.firstn e xs)%list) ->
  gaussian_iterated_expectation n F =
    gaussian_iterated_expectation n
      (fun xs => F (List.skipn e xs ++ List.firstn e xs)%list).
Proof.
move=> /leP en HC HB HC' HB'.
apply: (gaussian_iterated_col_perm_gauss _ (rot_perm e)
  (fun xs => (List.skipn e xs ++ List.firstn e xs)%list) F C p C' p' _ HC HB HC' HB').
by move=> x; rewrite list_of_row_rot // /rot skipnE firstnE appE.
Qed.

End rotation.

Section last_marginal.

(* Continuity in the first d coordinates of the expectation over the last
   one, for F continuous with polynomial growth on d + 1 coordinates. The
   marginal at x : 'rV[RR]_d is the integral of t |-> F (list_of_row x ++ [t])
   against the normal law, continuous in x by continuity_under_integral_at:
   near x0, the integrand is dominated by C (1 + (|x0| + 1)) ^ (p d)
   (1 + |t|) ^ p, which is integrable. *)
Theorem gaussian_last_marginal_continuous_gauss d (F : list R -> R) C p :
  finite_joint_continuous (S d) F -> finite_polynomial_bound (S d) C p F ->
  finite_joint_continuous d (gaussian_last_marginal F).
Proof.
move=> HC HB; have [_ Hb] := HB.
have C0 : (0 <= C :> RR) by apply/RleP; case: HB.
have secC xs : length xs = d ->
    continuous (fun u : RR => F (xs ++ [:: u])%list : RR).
  by move=> Hl t; exact: (finite_joint_continuous_last_section d F xs HC Hl t).
have w0 xs : (0 <= gaussian_coordinate_product_weight p xs :> RR).
  by apply/RleP; exact: gaussian_coordinate_product_weight_nonnegative.
have secB xs : length xs = d -> forall t : RR,
    `|F (xs ++ [:: t])%list : RR| <=
      C * gaussian_coordinate_product_weight p xs * (1 + `|t|) ^+ p.
  move=> Hl t.
  have wE : gaussian_coordinate_product_weight p (xs ++ [:: t])%list =
      gaussian_coordinate_product_weight p xs * pow (1 + Rabs t) p.
    by rewrite gaussian_coordinate_product_weight_append /= Rmult_1_r.
  have := Hb (xs ++ [:: t])%list; rewrite List.length_app Hl /= Nat.add_1_r.
  move=> /(_ erefl); rewrite wE !RabsE RpowE => /RleP H.
  by apply: (Order.POrderTheory.le_trans H); rewrite !RmultE mulrA.
have exf xs : length xs = d ->
    gaussian_law_integrable (fun t => F (xs ++ [:: t])%list).
  move=> Hl; rewrite /gaussian_law_integrable.
  have mf : measurable_fun [set: measurableTypeR R]
      ((fun t : R => F (xs ++ [:: t])%list) : _ -> measurableTypeR R).
    by apply: continuous_measurable_fun; exact: secC.
  apply: (integrable_normal_poly (C := C * gaussian_coordinate_product_weight p xs
    * 2 ^+ p) (k := p) mf) => t.
  apply: (Order.POrderTheory.le_trans (secB xs Hl t)).
  rewrite -(mulrA (C * gaussian_coordinate_product_weight p xs)).
  exact: (ler_wpM2l (mulr_ge0 C0 (w0 _)) (exprn1D_le _ (normr_ge0 t))).
have E : (fun x : 'rV[RR]_d => gaussian_last_marginal F (list_of_row x) : RR) =
    (fun x : 'rV[RR]_d =>
      \int[gaussian_law]_t (F (list_of_row x ++ [:: t])%list : RR)).
  apply/funext => x; rewrite /gaussian_last_marginal /Rintegral.
  have exf' := (gpb_integrable_iff _).1 (exf _ (list_of_row_length x)).
  by have := gpb_law_integral _ exf' => /(congr1 fine) /= ->.
apply: finite_joint_continuous_of_row; rewrite E => x0.
set Rb : RR := `|x0| + 1.
have Rb0 : 0 <= Rb by rewrite /Rb addr_ge0 ?normr_ge0 ?ler01.
have Rb0' : Rle 0 Rb by apply/RleP.
have Rb1 : 0 <= 1 + Rb by rewrite addr_ge0 ?ler01.
have wb x : ball x0 1 x ->
    gaussian_coordinate_product_weight p (list_of_row x) <= (1 + Rb) ^+ (p * d).
  move=> bx; have bx' : `|x| <= Rb.
    move: bx; rewrite -ball_normE /ball_ /= => bx.
    rewrite -[X in `|X|](subKr x0); apply: (Order.POrderTheory.le_trans (ler_normB _ _)).
    by rewrite lerD2l; exact: Order.POrderTheory.ltW.
  have ent y : In y (list_of_row x) -> Rle (Rabs y) Rb.
    move=> /(List.In_nth _ _ 0%R)[i [ilt <-]]; move: ilt.
    rewrite list_of_row_length => /ltP id.
    have -> : i = Ordinal id by [].
    rewrite (list_of_row_nth x (Ordinal id)) RabsE; apply/RleP.
    exact: (Order.POrderTheory.le_trans (mx_norm_entry_le x 0 (Ordinal id)) bx').
  have := gaussian_coordinate_product_weight_box p (list_of_row x) Rb Rb0' ent.
  by rewrite list_of_row_length RpowE => /RleP.
set K : RR := C * (1 + Rb) ^+ (p * d) * 2 ^+ p.
have K0 : 0 <= K.
  by rewrite /K; apply: mulr_ge0; [apply: mulr_ge0 => //; exact: exprn_ge0|exact: exprn_ge0].
apply: (continuity_under_integral_at (X := 'rV[RR]_d) (Y := measurableTypeR R)
  (U := ball x0 1)
  (g := fun t : RR => K * (1 + `|t| ^+ p))).
- exact: measurableT.
- by apply/nbhs_ballP; exists 1; first exact: ltr01.
- by move=> x _; exact: (exf _ (list_of_row_length x)).
- move=> t _.
  have HC' : finite_joint_continuous (d + length [:: t])%coq_nat F.
    by rewrite /= Nat.add_1_r.
  exact: (list_of_row_continuous _ _
    (finite_joint_continuous_suffix d [:: t] F HC') x0).
- have mg : measurable_fun [set: measurableTypeR R]
      (fun t : RR => K * (1 + `|t| ^+ p)).
    apply: measurable_funM => //; apply: measurable_funD => //.
    by apply: measurable_funX; exact: normr_measurable.
  apply: (integrable_normal_poly (C := K) (k := p) mg) => t.
  by rewrite ger0_norm //; apply: mulr_ge0.
- move=> x bx t _; apply: (Order.POrderTheory.le_trans (secB _ (list_of_row_length x) t)).
  rewrite /K -(mulrA (C * (1 + Rb) ^+ (p * d))); apply: ler_pM.
  - exact: (mulr_ge0 C0 (w0 _)).
  - exact: (exprn_ge0 _ (addr_ge0 ler01 (normr_ge0 t))).
  - exact: (ler_wpM2l C0 (wb x bx)).
  - exact: (exprn1D_le _ (normr_ge0 t)).
Qed.

End last_marginal.

Section quadratic.
Local Open Scope R_scope.

Theorem gaussian_quadratic_exponential_has_integral_gauss t :
  t < 1/2 ->
  gaussian_has_integral (fun x => exp (t * (x*x)))
    (gaussian_mass / sqrt (1-2*t)).
Proof.
move=> Ht.
pose f := fun x : R => exp (t * (x * x)).
have fE : f = (fun x => expR (t * x ^+ 2)%R).
  by rewrite /f expF; apply/funext => x; rewrite expr2.
have ts : (2 * t * 1 ^+ 2 < 1)%R.
  rewrite expr1n mulr1; apply/RltP.
  change (Rlt (Rmult (Rplus R1 R1) t) R1); lra.
have E := integral_normal_expR_sqr (oner_neq0 R) ts.
have mf : measurable_fun [set: measurableTypeR R] (fun x => (f x)%:E).
  by apply/measurable_EFinP; rewrite fE; exact: measurable_expR_sqr.
have iN : gaussian_law_integrable f.
  apply/integrableP; split => //.
  have -> : (\int[gaussian_law]_x `|(f x)%:E| = \int[normal_prob 0 1]_x (expR (t * x ^+ 2))%:E)%E.
    by apply: eq_integral => x _; rewrite fE /= ger0_norm // expR_ge0.
  by rewrite E ltry.
have exf : gaussian_integral_exists f := (gpb_integrable_iff f).1 iN.
have Eexp : gaussian_expectation f = (Num.sqrt (1 - 2 * t))^-1%R.
  have := gpb_law_integral f exf.
  have -> : (\int[gaussian_law]_x (f x)%:E = \int[normal_prob 0 1]_x (expR (t * x ^+ 2))%:E)%E.
    by apply: eq_integral => x _; rewrite fE.
  by rewrite E expr1n mulr1 => -[->].
have m0 := Gaussian.Line.Mass.gaussian_mass_positive.
split; first exact: exf.
rewrite -/(gaussian_integral f) RsqrtE.
have -> : gaussian_integral f = gaussian_expectation f * gaussian_mass.
  by rewrite /gaussian_expectation; field; lra.
by rewrite Eexp RdivE [RHS]mulrC.
Qed.

End quadratic.
