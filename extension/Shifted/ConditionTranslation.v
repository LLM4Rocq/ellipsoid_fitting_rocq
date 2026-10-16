(* A deterministic transfer from the uniform condition residual gap to
   translated samples. The matrix in a hypothetical fit may depend on all
   observations; the gap hypothesis is uniform in that matrix and its level. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.matrix Require Import condition_cone centered_translation.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.comparison Require Import gauss_matrix_law.
From GaussianAnalysis.probability Require Import subgaussian_matrix.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Sat Require Import Apriori Universality.
From EllipsoidUniversality.Condition Require Import Unsat.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Shifted Require Import GaussianRows Translations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma translation_pairing_arithmetic (s a b c q u v : R) :
  q = s*a+c -> q+2*u+v = s*b+c -> b*s = a*s+(2*u+v).
Proof. by move=> h1 h2; nra. Qed.

Definition sample_point_matrix n d (x : paper_main_sample n d) : 'M[RR]_(n,d) :=
  gauss_matrix_law.tuple_mx (sample_row_tuple x).

Lemma sample_point_matrixE n d (x : paper_main_sample n d) i j :
  sample_point_matrix x i j = paper_main_point x i j 0.
Proof.
by rewrite /sample_point_matrix /gauss_matrix_law.tuple_mx /sample_row_tuple
  mxE tnth_mktuple mxE.
Qed.

Lemma measurable_sample_point_matrix n d :
  measurable_fun [set: paper_main_sample n d] (@sample_point_matrix n d).
Proof.
exact: measurableT_comp (@gauss_matrix_law.measurable_tuple_mx RR n d)
  (@measurable_sample_row_tuple n d).
Qed.

Lemma sample_feature_translate n d (x : paper_main_sample n d)
    (m : 'cV[RR]_d) (S : 'M[RR]_d) (i : 'I_n) :
  (0 < d)%N -> S \is symmetricmx ->
  mxdot (sample_W (sample_translate m x) i) S = mxdot (sample_W x i) S +
    (2 * mxdot (paper_main_point x i) (S *m m) + mxdot m (S *m m)) /
      Num.sqrt d%:R.
Proof.
move=> d0 Ss.
have sd0 : (0 : RR) < Num.sqrt d%:R by rewrite sqrtr_gt0 ltr0n.
have sdN : Num.sqrt (d%:R : RR) != 0 := lt0r_neq0 sd0.
have h1 := qf_sample_W n d x i S d0.
have h2 := qf_sample_W n d (sample_translate m x) i S d0.
rewrite sample_translate_point !pm_qf_col quadratic_translate_form // in h2.
rewrite pm_qf_col in h1.
apply: (mulIf sdN).
rewrite mulrDl divfK //.
exact: translation_pairing_arithmetic h1 h2.
Qed.

Lemma cond_slice_opnorm_bound d (C : R) (S : 'M[RR]_d) :
  0 < C -> cond_slice C S -> opnorm S <= C.
Proof.
move=> C0 hS.
have Ss : S \is symmetricmx by case: hS => [[h _] _].
apply/(opnorm_symP Ss (ltW C0)) => v.
have /andP[hl hu] := cond_slice_form C0 hS v.
have hv : 0 <= mxdot v (S *m v).
  apply: le_trans hl; apply: mulr_ge0; last exact: mxdot_ge0.
  by rewrite invr_ge0; exact: ltW.
by rewrite ger0_norm.
Qed.

Lemma sample_linear_values_energy n d (x : paper_main_sample n d)
    (v : 'cV[RR]_d) :
  \sum_(i < n) (mxdot (paper_main_point x i) v)^+2 =
    frobenius (sample_point_matrix x *m v)^+2.
Proof.
rewrite frobenius_sqr /mxdot.
apply: eq_bigr => i _.
rewrite big_ord1 expr2.
have he : \sum_(j < d) \sum_(k < 1) paper_main_point x i j k * v j k =
    (sample_point_matrix x *m v) i 0.
  rewrite mxE; apply: eq_bigr => j _.
  by rewrite big_ord1 sample_point_matrixE.
by rewrite he.
Qed.

Theorem translated_condition_gap_obstruction n d (x : paper_main_sample n d)
    (m : 'cV[RR]_d) (C eta : R) :
  (0 < d)%N -> 0 < C ->
  (forall S : 'M[RR]_d, cond_slice C S -> forall b : R,
    eta * n%:R <= \sum_(i < n) (b - mxdot (sample_W x i) S)^+2) ->
  universality_conditioned_fit_event n d C (sample_translate m x) ->
  eta * n%:R * d%:R <=
    4 * C^+2 * (opnorm (sample_point_matrix x))^+2 * (frobenius m)^+2.
Proof.
move=> d0 C0 hgap hfit.
have [S [b [hS hfitS]]] := cond_fit_slice n d (sample_translate m x) C d0 hfit.
have Ss : S \is symmetricmx by case: hS => [[h _] _].
pose z : R := mxdot m (S *m m).
pose sd : R := Num.sqrt d%:R.
have sd0 : 0 < sd by rewrite /sd sqrtr_gt0 ltr0n.
have sdn : sd != 0 := lt0r_neq0 sd0.
have residual i : b - z/sd - mxdot (sample_W x i) S =
    2 / sd * mxdot (paper_main_point x i) (S *m m).
  have h := @sample_feature_translate n d x m S i d0 Ss.
  rewrite hfitS in h.
  rewrite /z /sd h.
  by field.
have hg := hgap S hS (b - z/sd).
have hsum : (\sum_(i < n) (b - z/sd - mxdot (sample_W x i) S)^+2) =
    (2 / sd)^+2 * \sum_(i < n) (mxdot (paper_main_point x i) (S *m m))^+2.
  under eq_bigr do rewrite residual exprMn.
  by rewrite mulr_sumr.
rewrite hsum sample_linear_values_energy in hg.
have hd : (0 : RR) < d%:R by rewrite ltr0n.
have dn : (d%:R : RR) != 0 := lt0r_neq0 hd.
have hs : (2 / sd)^+2 * d%:R = 4.
  rewrite expr_div_n /sd sqr_sqrtr //.
  by field.
have hscaled : eta * n%:R * d%:R <=
    4 * frobenius (sample_point_matrix x *m (S *m m))^+2.
  have hh := ler_wpM2r (ltW hd) hg.
  have he : (2 / sd)^+2 * frobenius (sample_point_matrix x *m (S *m m))^+2 * d%:R =
      4 * frobenius (sample_point_matrix x *m (S *m m))^+2.
    by rewrite mulrAC hs.
  by rewrite he in hh.
have hnorm : frobenius (sample_point_matrix x *m (S *m m)) <=
    opnorm (sample_point_matrix x) * C * frobenius m.
  apply: le_trans (frobenius_mulmx_opnorm _ _) _.
  rewrite -mulrA; apply: ler_wpM2l; first exact: opnorm_ge0.
  apply: le_trans (frobenius_mulmx_opnorm _ _) _.
  apply: ler_wpM2r; first exact: frobenius_ge0.
  exact: cond_slice_opnorm_bound C0 hS.
apply: le_trans hscaled _.
have hnorm0 : 0 <= opnorm (sample_point_matrix x) * C * frobenius m.
  by rewrite !mulr_ge0 ?opnorm_ge0 ?frobenius_ge0 ?ltW.
have hh : frobenius (sample_point_matrix x *m (S *m m))^+2 <=
    (opnorm (sample_point_matrix x) * C * frobenius m)^+2.
  by rewrite lerXn2r ?nnegrE ?frobenius_ge0.
have h40 : (0 : RR) <= 4 by rewrite ler0n.
have h4 := ler_wpM2l h40 hh.
move: h4; rewrite !exprMn.
by have -> : 4 * (opnorm (sample_point_matrix x)^+2 * C^+2 * frobenius m^+2) =
    4 * C^+2 * opnorm (sample_point_matrix x)^+2 * frobenius m^+2 by ring.
Qed.

Definition translation_norm_obstruction n d (m : 'cV[RR]_d) (C eta : R) :
    set (paper_main_sample n d) :=
  [set x | eta * n%:R * d%:R <=
    4 * C^+2 * (opnorm (sample_point_matrix x))^+2 * (frobenius m)^+2].

Lemma measurable_translation_norm_obstruction n d (m : 'cV[RR]_d) (C eta : R) :
  measurable (@translation_norm_obstruction n d m C eta).
Proof.
have mf : measurable_fun [set: paper_main_sample n d] (fun x =>
    (4 * C^+2 * (opnorm (sample_point_matrix x))^+2 * (frobenius m)^+2 : RR)).
  apply: measurable_funM => //; apply: measurable_funM => //.
  apply: measurable_funX; apply: measurable_opnorm.
  move=> i j; exact: measurableT_comp (measurable_mxentry i j)
    (@measurable_sample_point_matrix n d).
rewrite /translation_norm_obstruction -[X in measurable X]setTI.
by apply: measurable_fun_ler.
Qed.

Theorem translated_condition_gap_probability n d
    (P : probability (paper_main_sample n d) R)
    (m : 'cV[RR]_d) (C eta : R) (E : set (paper_main_sample n d)) :
  (0 < d)%N -> 0 < C -> measurable E ->
  (forall x, ~ E x -> forall S : 'M[RR]_d, cond_slice C S -> forall b : R,
    eta * n%:R <= \sum_(i < n) (b - mxdot (sample_W x i) S)^+2) ->
  (P ((sample_translate m) @^-1` universality_conditioned_fit_event n d C) <=
    P E + P (@translation_norm_obstruction n d m C eta))%E.
Proof.
move=> d0 C0 mE hgap.
pose F := (sample_translate m) @^-1` universality_conditioned_fit_event n d C.
pose B := @translation_norm_obstruction n d m C eta.
have mF : measurable F.
  rewrite /F -[X in measurable X]setTI.
  exact: (@measurable_sample_translate n d m) measurableT _
    (measurable_conditioned_fit_event n d C).
have mB : measurable B := @measurable_translation_norm_obstruction n d m C eta.
have sub : F `<=` E `|` B.
  move=> x hx.
  have [xE|xE] := pselect (E x); first by left.
  right; exact: translated_condition_gap_obstruction d0 C0 (hgap x xE) hx.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
  exact: measurableU.
exact: (measureU2 _ mE mB).
Qed.
