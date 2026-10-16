(* Assembly of S4, including the high-probability uniform lower bound.
   That bound is a complement consequence of the proved infimum lower
   tail. No minimizing translation or matrix is introduced. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions ShiftedErrorStatement.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Shifted Require Import Translations TranslationError
  GaussianErrorUpper GaussianErrorLower GaussianError.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma gaussian_translation_error_uniform_lower (alpha : R) (n : nat -> nat)
    (delta : R) :
  0 < alpha -> universality_density_tends_to n alpha -> 0 < delta ->
  paper_main_tends_to (fun d => gaussian_product_law (n d*d)
    [set x : paper_main_sample (n d) d |
      universality_e_star alpha 3%:R-delta <=
        translation_fitting_error (n d) d x]) 1.
Proof.
move=> a0 hn delta0.
have tl : universality_e_star alpha 3%:R-delta < universality_e_star alpha 3%:R
  by rewrite ltrBlDr ltrDl.
have low := gaussian_translation_error_lower_tail a0 hn tl.
move=> eps eps0.
have ep2 : 0 < eps/2 by rewrite divr_gt0.
have [D hD] := low (eps/2) ep2; exists D=>d dD.
pose t := universality_e_star alpha 3%:R-delta.
pose A : set (paper_main_sample (n d) d) :=
  [set x | t <= translation_fitting_error (n d) d x].
pose B : set (paper_main_sample (n d) d) :=
  [set x | translation_fitting_error (n d) d x <= t].
have mA : measurable A.
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ler=>//.
  exact: measurable_translation_fitting_error_all.
have mB : measurable B := @measurable_translation_error_sublevel (n d) d t.
have incl : ~` A `<=` B.
  move=>x /= nx; apply: ltW; rewrite ltNge; apply/negP=>hx.
  exact: nx hx.
have PB : (gaussian_product_law (n d*d) B <= (eps/2)%:E)%E.
  have hd := hD d dD; rewrite sube0 gee0_abs ?measure_ge0 // in hd.
  exact: ltW hd.
have close := prob_close_one _ _ (gaussian_product_law (n d*d))
  A B (eps/2) mA mB incl PB.
apply: le_lt_trans close _; rewrite lte_fin.
clear -eps0; lra.
Qed.

Theorem shifted_error_theorem : shifted_error_statement.
Proof.
split.
- split.
  + exact: measurable_translation_fitting_error_all.
  + exact: measurable_gaussian_shift_error.
- move=>alpha n a0 hn; split.
  + move=>m; exact: gaussian_shift_error_limit a0 hn.
  + split.
    * exact: gaussian_translation_error_limit a0 hn.
    * split.
      -- move=>t ht; exact: gaussian_translation_error_lower_tail a0 hn ht.
      -- move=>delta delta0; exact: gaussian_translation_error_uniform_lower a0 hn delta0.
Qed.
