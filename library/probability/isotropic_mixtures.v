From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import gauss_linear.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows efron_stein.
From GaussianAnalysis.probability Require Import subgaussian mixture countable_mixture.
From GaussianAnalysis.random_matrix Require Import isotropic_rows.

(**md**************************************************************************)
(* # Isotropic product rows and mixtures                                    *)
(*                                                                           *)
(* Centered variance-one coordinates with a common subgaussian constant K  *)
(* give an isotropic row with directional subgaussian constant 4K. Finite  *)
(* and countable mixtures preserve centering, isotropy and a common        *)
(* directional bound. The resulting mixture need not have independent     *)
(* coordinates. No fourth-moment or symmetry hypothesis is imposed.       *)
(* The row law is supplied by an exact measurable-image identity, rather  *)
(* than by another probability construction. All dimensions, including 0, *)
(* are allowed. Source: reserve estimates in doc/shifted-gaussian.tex.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section coordinate_row.
Context {R : realType} {d : nat}.

Definition coordinate_row (t : d.-tuple (measurableTypeR R)) : 'rV[R]_d :=
  \row_j tnth t j.

Lemma measurable_coordinate_row : measurable_fun setT coordinate_row.
Proof.
apply/measurable_fun_mxP => i j; under eq_fun do rewrite /coordinate_row mxE.
exact: measurable_tnth.
Qed.

Lemma mxdot_coordinate_row (t : d.-tuple (measurableTypeR R)) (y : 'rV[R]_d) :
  mxdot (coordinate_row t) y = \sum_j y 0 j * tnth t j.
Proof.
rewrite /mxdot big_ord1; apply: eq_bigr => j _.
by rewrite /coordinate_row mxE mulrC.
Qed.

End coordinate_row.

Section product_row.
Context {R : realType} {d : nat}.
Variable nu : nat -> probability (measurableTypeR R) R.
Variable P : probability 'rV[R]_d R.
Hypothesis law : forall A, measurable A ->
  P A = tuple_prod nu d (coordinate_row @^-1` A).
Variable K : R.
Hypothesis K0 : 0 < K.
Hypothesis sub : forall j, (j < d)%N -> subgaussian (nu j) (fun x => x) K.
Hypothesis cen : forall j, (j < d)%N -> \int[nu j]_x x = 0.
Hypothesis iso : forall j, (j < d)%N -> \int[nu j]_x x ^+ 2 = 1.

Lemma integral_coordinate_row_law (f : 'rV[R]_d -> \bar R) :
  measurable_fun setT f ->
  (\int[P]_x f x = \int[tuple_prod nu d]_t f (coordinate_row t))%E.
Proof.
move=> mf; rewrite integralE [RHS]integralE.
rewrite (ge0_integral_image measurable_coordinate_row law (measurable_funepos mf)) //.
rewrite (ge0_integral_image measurable_coordinate_row law (measurable_funeneg mf)) //.
by congr (_ - _)%E; apply: eq_integral => t _; rewrite ?funeposE ?funenegE.
Qed.

Theorem product_row_subgaussian (y : 'rV[R]_d) : frobenius y <= 1 ->
  subgaussian P (fun x => mxdot x y) (4*K).
Proof.
move=> y1.
pose a (j : nat) := if insub j is Some i then y 0 i else 0.
have aE (i : 'I_d) : a i = y 0 i by rewrite /a valK.
have s2 : Num.sqrt (3:R)^+2 = 3 by rewrite sqr_sqrtr.
apply: (@subgaussian_of_mgf _ _ _ _ _ (Num.sqrt 3 * K)).
- exact: measurable_mxdot.
- by rewrite mulr_gt0.
- by rewrite !exprMn s2; nra.
- move=> l.
  rewrite (integral_coordinate_row_law
    (f:=fun x => (expR (l*mxdot x y))%:E)).
  + by apply/measurable_EFinP; apply: measurableT_comp => //; apply: measurable_funM => //; exact: measurable_mxdot.
  + have E t : mxdot (coordinate_row t) y = \sum_(i<d) a i * tnth t i.
      by rewrite mxdot_coordinate_row; apply: eq_bigr => i _; rewrite aE.
    under eq_integral do rewrite E.
    apply: le_trans (subgaussian_sum_mgf (K:=fun=>K) a l sub cen) _.
    rewrite lee_fin ler_expR exprMn s2 -mulr_suml.
    have A : \sum_(i<d) a i ^+ 2 = frobenius y ^+ 2.
      rewrite frobenius_sqr /mxdot big_ord1.
      by apply: eq_bigr => i _; rewrite aE expr2.
    rewrite A; have fy0 := frobenius_ge0 y.
    have fy2 : frobenius y ^+ 2 <= 1 by nra.
    have l0 := sqr_ge0 l; have k0 := sqr_ge0 K.
    nra.
Qed.

Let coordinate_integrable j (jd : (j<d)%N) :
  (nu j).-integrable setT (fun x => x%:E).
Proof.
have h := integrable_subgaussian_exprn 1 (sub jd).
by apply: eq_integrable h => // x _; rewrite expr1.
Qed.

Theorem product_row_mean (y : 'rV[R]_d) : \int[P]_x mxdot x y = 0.
Proof.
rewrite /Rintegral (integral_coordinate_row_law (f:=fun x => (mxdot x y)%:E));
  first by apply/measurable_EFinP; exact: measurable_mxdot.
change (\int[tuple_prod nu d]_t mxdot (coordinate_row t) y = 0).
under eq_Rintegral do rewrite mxdot_coordinate_row.
have fi (j : 'I_d) : (nu j).-integrable setT (fun x => (y 0 j*x)%:E).
  have := integrableZl measurableT (y 0 j) (coordinate_integrable (ltn_ord j)).
  by apply: eq_integrable => // x _; rewrite EFinM.
have iP (j : 'I_d) : (tuple_prod nu d).-integrable setT
    (fun t => (y 0 j*tnth t j)%:E).
  exact: integrable_independent_coordinate fi j.
rewrite Rintegral_sum //.
apply: big1 => j _.
rewrite /Rintegral (integral_tuple_prod_coord nu j (measurable_int _ (fi j))).
change (\int[nu j]_x (y 0 j*x) = 0).
by rewrite (RintegralZl _ measurableT (coordinate_integrable (ltn_ord j))) cen ?ltn_ord // mulr0.
Qed.

Theorem product_row_second (y : 'rV[R]_d) :
  \int[P]_x mxdot x y ^+ 2 = frobenius y ^+ 2.
Proof.
have fi (j : 'I_d) : (nu j).-integrable setT (EFin \o (fun x => y 0 j*x)).
  have := integrableZl measurableT (y 0 j) (coordinate_integrable (ltn_ord j)).
  by apply: eq_integrable => // x _; rewrite /= EFinM.
have f2i (j : 'I_d) : (nu j).-integrable setT (fun x => ((y 0 j*x)^+2)%:E).
  have := integrableZl measurableT (y 0 j ^+2)
    (integrable_subgaussian_exprn 2 (sub (ltn_ord j))).
  by apply: eq_integrable => // x _; rewrite exprMn EFinM.
have fc (j : 'I_d) : \int[nu j]_x (y 0 j*x) = 0.
  by rewrite (RintegralZl _ measurableT (coordinate_integrable (ltn_ord j))) cen ?ltn_ord // mulr0.
have [_ e2] := independent_centered_sum_second_moment fi f2i fc.
rewrite /Rintegral (integral_coordinate_row_law
  (f:=fun x => (mxdot x y ^+2)%:E));
  first by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_mxdot.
change (\int[tuple_prod nu d]_t mxdot (coordinate_row t) y ^+2 = frobenius y ^+2).
under eq_Rintegral do rewrite mxdot_coordinate_row.
rewrite e2 frobenius_sqr /mxdot big_ord1.
apply: eq_bigr => j _.
under eq_Rintegral do rewrite exprMn.
rewrite RintegralZl //; first exact: integrable_subgaussian_exprn 2 (sub (ltn_ord j)).
by rewrite iso ?ltn_ord // mulr1 expr2.
Qed.

End product_row.

Section finite_mixture_rows.
Context {R : realType} {d : nat} {I : finType}.
Variables (P : I -> probability 'rV[R]_d R) (w : I -> R).
Variable hw : mixture_weights w.
Variable K : R.
Hypothesis sub : forall i (y : 'rV[R]_d), frobenius y <= 1 ->
  subgaussian (P i) (fun x => mxdot x y) K.
Hypothesis cen : forall i (y : 'rV[R]_d), frobenius y <= 1 ->
  \int[P i]_x mxdot x y = 0.
Hypothesis iso : forall i (y : 'rV[R]_d), frobenius y <= 1 ->
  \int[P i]_x mxdot x y ^+2 = frobenius y ^+2.

Theorem finite_mixture_row_subgaussian (y : 'rV[R]_d) : frobenius y <= 1 ->
  subgaussian (mixture P hw) (fun x => mxdot x y) K.
Proof. by move=> y1; apply: subgaussian_mixture => i; exact: sub. Qed.

Theorem finite_mixture_row_mean (y : 'rV[R]_d) : frobenius y <= 1 ->
  \int[mixture P hw]_x mxdot x y = 0.
Proof.
move=> y1.
have fi i : (P i).-integrable setT (fun x => (mxdot x y)%:E).
  have := integrable_subgaussian_exprn 1 (sub i y1).
  by apply: eq_integrable => // x _; rewrite expr1.
rewrite /Rintegral integral_mixture //.
have E i : (\int[P i]_x (mxdot x y)%:E)%E = 0%E.
  rewrite -(fineK (integrable_fin_num measurableT (fi i))).
  by rewrite -/(\int[P i]_x mxdot x y) cen.
by under eq_bigr do rewrite E mule0; rewrite big1.
Qed.

Theorem finite_mixture_row_second (y : 'rV[R]_d) : frobenius y <= 1 ->
  \int[mixture P hw]_x mxdot x y ^+2 = frobenius y ^+2.
Proof.
move=> y1.
have fi i := integrable_subgaussian_exprn 2 (sub i y1).
have E i : (\int[P i]_x (mxdot x y ^+2)%:E)%E = (frobenius y ^+2)%:E.
  rewrite -(fineK (integrable_fin_num measurableT (fi i))).
  by rewrite -/(\int[P i]_x mxdot x y ^+2) iso.
rewrite /Rintegral integral_mixture //.
under eq_bigr do rewrite E -EFinM.
by rewrite sumEFin -mulr_suml (mixture_weights_sum hw) mul1r.
Qed.

End finite_mixture_rows.

Section countable_mixture_integrals.
Context {R : realType} {e} {T : measurableType e}.
Variables (P : nat -> probability T R) (w : nat -> R).
Variable hw : cmixture_weights w.

Lemma cmixture_weighted_const (c : R) :
  (\sum_(i<oo) (w i)%:E * c%:E = c%:E)%E.
Proof.
under eq_eseriesr do rewrite muleC.
have w0 i : true -> (0 <= (w i)%:E)%E by move=> _; rewrite lee_fin; exact: hw.1.
by rewrite nneseriesZl // hw.2 mule1.
Qed.

Theorem subgaussian_cmixture (X : T -> R) (K : R) :
  (forall i, subgaussian (P i) X K) -> subgaussian (cmixture P hw) X K.
Proof.
move=> sub; have [K0 mX _] := sub 0%N; split=> //.
have mf : measurable_fun setT (fun x => (expR (X x ^+2 / K^+2))%:E).
  by apply/measurable_EFinP; exact: measurable_expR_sqr.
rewrite (ge0_integral_cmixture P hw measurableT mf).
- by move=> x _; rewrite lee_fin expR_ge0.
- apply: le_trans (_ : (\sum_(i<oo) (w i)%:E*2%:E <= 2%:E)%E).
  + apply: lee_nneseries => [i _ _|i _].
    * rewrite mule_ge0 ?lee_fin ?hw.1 //.
      by apply: integral_ge0 => x _; rewrite lee_fin expR_ge0.
    * apply: lee_wpmul2l; first by rewrite lee_fin; exact: hw.1.
      by have [_ _ h] := sub i.
  + by rewrite cmixture_weighted_const.
Qed.

End countable_mixture_integrals.

Section countable_mixture_rows.
Context {R : realType} {d : nat}.
Variables (P : nat -> probability 'rV[R]_d R) (w : nat -> R).
Variable hw : cmixture_weights w.
Variable K : R.
Hypothesis sub : forall i (y : 'rV[R]_d), frobenius y <= 1 ->
  subgaussian (P i) (fun x => mxdot x y) K.
Hypothesis cen : forall i (y : 'rV[R]_d), frobenius y <= 1 ->
  \int[P i]_x mxdot x y = 0.
Hypothesis iso : forall i (y : 'rV[R]_d), frobenius y <= 1 ->
  \int[P i]_x mxdot x y ^+2 = frobenius y ^+2.

Theorem countable_mixture_row_subgaussian (y : 'rV[R]_d) : frobenius y <= 1 ->
  subgaussian (cmixture P hw) (fun x => mxdot x y) K.
Proof. by move=> y1; apply: subgaussian_cmixture => i; exact: sub. Qed.

Theorem countable_mixture_row_second (y : 'rV[R]_d) : frobenius y <= 1 ->
  \int[cmixture P hw]_x mxdot x y ^+2 = frobenius y ^+2.
Proof.
move=> y1.
have mf : measurable_fun setT (fun x : 'rV[R]_d => (mxdot x y ^+2)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_mxdot.
have E i : (\int[P i]_x (mxdot x y ^+2)%:E)%E = (frobenius y ^+2)%:E.
  rewrite -(fineK (integrable_fin_num measurableT (integrable_subgaussian_exprn 2 (sub i y1)))).
  by rewrite -/(\int[P i]_x mxdot x y ^+2) iso.
rewrite /Rintegral (ge0_integral_cmixture P hw measurableT mf).
- by move=> x _; rewrite lee_fin sqr_ge0.
- by under eq_eseriesr do rewrite E; rewrite (cmixture_weighted_const hw).
Qed.

Theorem countable_mixture_row_mean (y : 'rV[R]_d) : frobenius y <= 1 ->
  \int[cmixture P hw]_x mxdot x y = 0.
Proof.
move=> y1.
have mx := measurable_mxdot y.
have mf : measurable_fun setT (fun x : 'rV[R]_d => (mxdot x y)%:E).
  exact/measurable_EFinP.
have m2 : measurable_fun setT (fun x : 'rV[R]_d => (mxdot x y ^+2)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have fi i : (P i).-integrable setT (fun x => (mxdot x y)%:E).
  have := integrable_subgaussian_exprn 1 (sub i y1).
  by apply: eq_integrable => // x _; rewrite expr1.
have E2 i : (\int[P i]_x (mxdot x y ^+2)%:E)%E = (frobenius y ^+2)%:E.
  rewrite -(fineK (integrable_fin_num measurableT (integrable_subgaussian_exprn 2 (sub i y1)))).
  by rewrite -/(\int[P i]_x mxdot x y ^+2) iso.
have absle (z : R) : `|z| <= 1 + z^+2.
  have zn := normr_ge0 z; have zz : `|z|^+2 = z^+2 by rewrite real_normK ?num_real.
  nra.
have abs2 i : (\int[P i]_x `|(mxdot x y)%:E| <= 2%:E)%E.
  apply: le_trans (_ : (\int[P i]_x (1 + mxdot x y ^+2)%:E <= 2%:E)%E).
  - apply: ge0_le_integral => //.
    + exact: measurableT_comp.
    + by apply/measurable_EFinP; apply: measurable_funD => //; exact: measurable_funX.
    + by move=> x _; rewrite abse_EFin lee_fin; exact: absle.
  - under eq_integral do rewrite EFinD.
    rewrite ge0_integralD //.
    + by move=> x _; rewrite lee_fin sqr_ge0.
    + rewrite E2 integral_cst //= probability_setT mule1 -EFinD lee_fin.
      have yn := frobenius_ge0 y; nra.
have fs : (\sum_(i<oo) (w i)%:E * \int[P i]_x `|(mxdot x y)%:E| < +oo)%E.
  apply: le_lt_trans (_ : (\sum_(i<oo) (w i)%:E * 2%:E < +oo)%E).
  - apply: lee_nneseries => [i _ _|i _].
    + rewrite mule_ge0 ?lee_fin ?hw.1 //; apply: integral_ge0 => x _; exact: abse_ge0.
    + apply: lee_wpmul2l => //; by rewrite lee_fin; exact: hw.1.
  - by rewrite (cmixture_weighted_const hw) ltry.
have [_ h] := integral_cmixture hw measurableT mf fi fs.
have E i : (\int[P i]_x (mxdot x y)%:E)%E = 0%E.
  rewrite -(fineK (integrable_fin_num measurableT (fi i))).
  by rewrite -/(\int[P i]_x mxdot x y) cen.
rewrite /Rintegral h.
by under eq_eseriesr do rewrite E mule0; rewrite eseries0.
Qed.

End countable_mixture_rows.

Section fair_choice_example.
Context {R : realType} {d : nat}.

Lemma fair_row_weights : mixture_weights (fun _ : bool => (2:R)^-1).
Proof.
split; first by move=> b; rewrite invr_ge0.
by rewrite big_bool /=; field.
Qed.

(* A fair choice between two isotropic laws need not be a product law. *)
Example fair_choice_second (P : bool -> probability 'rV[R]_d R) (K : R)
    (hs : forall b (y : 'rV[R]_d), frobenius y <= 1 ->
      subgaussian (P b) (fun x => mxdot x y) K)
    (h2 : forall b (y : 'rV[R]_d), frobenius y <= 1 ->
      \int[P b]_x mxdot x y ^+2 = frobenius y ^+2)
    (y : 'rV[R]_d) : frobenius y <= 1 ->
  \int[mixture P fair_row_weights]_x mxdot x y ^+2 = frobenius y ^+2.
Proof. exact: (@finite_mixture_row_second R d _ P
  (fun _ => (2:R)^-1) fair_row_weights K hs h2 y). Qed.

End fair_choice_example.
