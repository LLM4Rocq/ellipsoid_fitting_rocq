(* Gaussian fitting-error limits under arbitrary deterministic shifts.
   The lower bound holds simultaneously for all translations. Combining
   it with the rotation/restriction upper bound also proves convergence
   of the infimum over translations. Both conclusions use the original
   frozen error functional and include the critical density alpha=1/4. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.convex Require Import ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import InProbability.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Shifted Require Import Translations TranslationError
  GaussianExistence GaussianErrorUpper GaussianErrorLower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma probability_tends_to_negligible {disp : measure_display}
    {T : nat -> measurableType disp} (P : forall d, probability (T d) RR)
    (E : forall d, set (T d)) :
  (forall d, measurable (E d)) ->
  paper_main_tends_to (fun d => P d (E d)) 0 -> negligible P E.
Proof.
move=> mE h; apply: negligible_measurable => // eps eps0.
have [D hD] := h eps eps0; exists D => d dD.
have hd := hD d dD; rewrite sube0 gee0_abs ?measure_ge0 // in hd.
exact: ltW hd.
Qed.

Lemma measurable_real_error_tail {disp : measure_display}
    (T : measurableType disp) (X : T -> RR) (l eps : R) :
  measurable_fun setT X -> measurable [set x | eps < `|X x-l|].
Proof.
move=> mX; apply: measurable_set_lt.
apply: (measurableT_comp (f := fun r : RR => `|r|)) => //.
exact: measurable_funB.
Qed.

Lemma cvg_prob_error_probability {disp : measure_display}
    {T : nat -> measurableType disp} (P : forall d, probability (T d) RR)
    (X : forall d, T d -> RR) (l : R) :
  (forall d, measurable_fun setT (X d)) -> cvg_prob P X l ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => P d [set x | eps < `|X d x-l|]) 0.
Proof.
move=> mX h eps eps0; apply: negligible_probability_tends_to.
- by move=> d; apply: measurable_real_error_tail.
- apply: negligibleW; first exact: h _ eps0.
  by exists 0%N => d _ x /= hx; exact: ltW hx.
Qed.

Lemma measurable_gaussian_shift_error_event n d (m : 'cV[R]_d) (e eps : R) :
  measurable (sample_translate m @^-1` universality_error_event n d e eps).
Proof.
rewrite -[X in measurable X]setTI.
exact: measurable_sample_translate (measurable_error_event _ _ _ _).
Qed.

Lemma measurable_translation_error_event n d (e eps : R) :
  measurable [set x : paper_main_sample n d |
    eps < `|translation_fitting_error n d x-e|].
Proof.
apply: measurable_real_error_tail.
exact: measurable_translation_fitting_error_all.
Qed.

Lemma translation_error_eventual_domination (alpha : R) (N : nat -> nat) :
  0 < alpha -> universality_density_tends_to N alpha ->
  exists D : nat, forall d, (D <= d)%N ->
  forall (x : paper_main_sample (N d) d) (m : 'cV[R]_d),
    translation_fitting_error (N d) d x <=
      universality_fitting_error (N d) d (sample_translate m x).
Proof.
move=> a0 hN; have [D hD] := gaussian_density_positive a0 hN.
exists (maxn 1 D) => d; rewrite geq_max => /andP[d0 dD] x m.
exact: (@translation_fitting_error_le (N d) d x m (hD d dD) d0).
Qed.

Theorem gaussian_translation_error_cvg (alpha : R) (N : nat -> nat) :
  0 < alpha -> universality_density_tends_to N alpha ->
  cvg_prob (fun d => gaussian_product_law (N d*d))
    (fun d x => translation_fitting_error (N d) d x)
    (universality_e_star alpha 3%:R).
Proof.
move=> a0 hN; apply/cvg_probP; split => t ht.
- have hu : negligible (fun d => gaussian_product_law (N d*d))
      (fun d => [set x : paper_main_sample (N d) d |
        t <= universality_fitting_error (N d) d
          (sample_translate (0 : 'cV[R]_d) x)]).
    apply: probability_tends_to_negligible.
    + move=> d; exact: measurable_gaussian_shift_error_atleast.
    + exact: (@gaussian_shift_error_atleast alpha N (fun d => 0) t a0 hN ht).
  apply: negligibleW hu _.
  have [D hD] := translation_error_eventual_domination a0 hN.
  exists D => d dD x /= hx.
  exact: le_trans hx (hD d dD x 0).
- apply: probability_tends_to_negligible.
  + move=> d; exact: measurable_translation_error_sublevel.
  + exact: gaussian_translation_error_lower_tail a0 hN ht.
Qed.

Theorem gaussian_shift_error_cvg (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) :
  0 < alpha -> universality_density_tends_to N alpha ->
  cvg_prob (fun d => gaussian_product_law (N d*d))
    (fun d x => universality_fitting_error (N d) d (sample_translate (m d) x))
    (universality_e_star alpha 3%:R).
Proof.
move=> a0 hN; apply/cvg_probP; split => t ht.
- apply: probability_tends_to_negligible.
  + move=> d; exact: measurable_gaussian_shift_error_atleast.
  + exact: (@gaussian_shift_error_atleast alpha N m t a0 hN ht).
- have hl : negligible (fun d => gaussian_product_law (N d*d))
      (fun d => [set x : paper_main_sample (N d) d |
        translation_fitting_error (N d) d x <= t]).
    apply: probability_tends_to_negligible.
    + move=> d; exact: measurable_translation_error_sublevel.
    + exact: gaussian_translation_error_lower_tail a0 hN ht.
  apply: negligibleW hl _.
  have [D hD] := translation_error_eventual_domination a0 hN.
  exists D => d dD x /= hx.
  exact: le_trans (hD d dD x (m d)) hx.
Qed.

Corollary gaussian_shift_error_limit (alpha : R) (N : nat -> nat)
    (m : forall d, 'cV[R]_d) :
  0 < alpha -> universality_density_tends_to N alpha ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => gaussian_product_law (N d*d)
    (sample_translate (m d) @^-1`
      universality_error_event (N d) d (universality_e_star alpha 3%:R) eps)) 0.
Proof.
move=> a0 hN; apply: cvg_prob_error_probability.
- move=> d; exact: measurable_gaussian_shift_error.
- exact: (@gaussian_shift_error_cvg alpha N m a0 hN).
Qed.

Corollary gaussian_translation_error_limit (alpha : R) (N : nat -> nat) :
  0 < alpha -> universality_density_tends_to N alpha ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => gaussian_product_law (N d*d)
    [set x : paper_main_sample (N d) d |
      eps < `|translation_fitting_error (N d) d x-
        universality_e_star alpha 3%:R|]) 0.
Proof.
move=> a0 hN; apply: cvg_prob_error_probability.
- move=> d; exact: measurable_translation_fitting_error_all.
- exact: gaussian_translation_error_cvg a0 hN.
Qed.
