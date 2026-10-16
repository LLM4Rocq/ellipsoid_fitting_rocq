(* S1: condition thresholds and the optimal condition number for small
   deterministic Gaussian translations. The sample is a flat tuple of
   independent standard Gaussian coordinates, translated row by row.
   The small-shift hypothesis is written explicitly below. The optimum
   is the existing extended-real infimum; no attainment is asserted.
   Source: doc/shifted-gaussian.tex and the formalization plan, S1.
   These are review drafts, not frozen statements. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From GaussianAnalysis.matrix Require Import euclidean.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions ConditionDefinitions.
From EllipsoidUniversality.Shifted Require Import Translations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition shifted_condition_measurability_statement : Prop :=
  forall n d : nat, forall (m : 'cV[R]_d) (C c eps : R),
  [/\ measurable
      (sample_translate m @^-1` universality_conditioned_fit_event n d C),
    measurable_fun [set: paper_main_sample n d]
      (fun x => data_condition_number n d (sample_translate m x)) &
    measurable [set x : paper_main_sample n d |
      (eps%:E < `|data_condition_number n d (sample_translate m x) - c%:E|)%E]].

(* condition_alpha and condition_star are the frozen fourth-moment-three
   curve and its inverse. Their phase-11 counterparts agree by the proved
   condition_kappa_alpha3 and condition_kappa_star3 compatibility lemmas.
   The strict alternatives leave equality at the threshold open. *)
Definition shifted_condition_threshold_statement : Prop :=
  forall C alpha : R, 1 < C -> 0 < alpha ->
  forall (n : nat -> nat) (m : forall d, 'cV[R]_d),
  universality_density_tends_to n alpha ->
  (forall eta : R, 0 < eta -> exists D : nat, forall d, (D <= d)%N ->
    frobenius (m d) <= eta * Num.sqrt d%:R) ->
  (alpha < condition_alpha C ->
    paper_main_tends_to (fun d => gaussian_product_law (n d*d)
      (sample_translate (m d) @^-1`
        universality_conditioned_fit_event (n d) d C)) 1%R) /\
  (condition_alpha C < alpha ->
    paper_main_tends_to (fun d => gaussian_product_law (n d*d)
      (sample_translate (m d) @^-1`
        universality_conditioned_fit_event (n d) d C)) 0%R).

Definition shifted_condition_number_statement : Prop :=
  forall alpha : R, 0 < alpha -> alpha < 4%:R^-1 ->
  forall (n : nat -> nat) (m : forall d, 'cV[R]_d),
  universality_density_tends_to n alpha ->
  (forall eta : R, 0 < eta -> exists D : nat, forall d, (D <= d)%N ->
    frobenius (m d) <= eta * Num.sqrt d%:R) ->
  (forall eps delta : R, 0 < eps -> 0 < delta ->
    exists D : nat, forall d, (D <= d)%N ->
    exists E : set (paper_main_sample (n d) d),
      [/\ measurable E, (gaussian_product_law (n d*d) E <= delta%:E)%E &
        forall x, ~ E x ->
          (`|data_condition_number (n d) d (sample_translate (m d) x) -
            (condition_star alpha)%:E| <= eps%:E)%E]) /\
  (forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => gaussian_product_law (n d*d)
      [set x : paper_main_sample (n d) d |
        (eps%:E < `|data_condition_number (n d) d (sample_translate (m d) x) -
          (condition_star alpha)%:E|)%E]) 0%R).

Definition shifted_condition_statement : Prop :=
  [/\ shifted_condition_measurability_statement,
    shifted_condition_threshold_statement & shifted_condition_number_statement].
