(* Gaussian fitting error under arbitrary deterministic shifts (S4).
   The frozen universality_fitting_error is minimized over PSD matrices
   of trace d and nonnegative fitted levels. translation_fitting_error is
   its infimum over all translations, not a selected or attained minimum.
   For n,d > 0, the defining infimum is no larger than the error at every
   translation (translation_fitting_error_le in Shifted/TranslationError).

   Both errors converge to e_star(alpha,3) for every alpha > 0, including
   alpha = 1/4, with no restriction on deterministic shift magnitudes.
   The last two conclusions are uniform lower tails, expressed through
   the measurable infimum. No exact-fitting assertion at 1/4 is made.
   This file contains the statements only. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Shifted Require Import Translations TranslationError.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition shifted_error_measurable_statement : Prop :=
  (forall n d : nat,
    measurable_fun [set: paper_main_sample n d]
      (fun x => translation_fitting_error n d x : RR)) /\
  (forall (n d : nat) (m : 'cV[RR]_d),
    measurable_fun [set: paper_main_sample n d]
      (fun x => universality_fitting_error n d (sample_translate m x) : RR)).

Definition shifted_error_limit_statement : Prop :=
  forall (alpha : R) (n : nat -> nat),
    0 < alpha -> universality_density_tends_to n alpha ->
  (forall m : forall d : nat, 'cV[RR]_d,
    forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => gaussian_product_law (n d*d)
      (sample_translate (m d) @^-1`
        universality_error_event (n d) d (universality_e_star alpha 3%:R) eps)) 0) /\
  (forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => gaussian_product_law (n d*d)
      [set x : paper_main_sample (n d) d |
        eps < `|translation_fitting_error (n d) d x-
          universality_e_star alpha 3%:R|]) 0) /\
  (forall t : R, t < universality_e_star alpha 3%:R ->
    paper_main_tends_to (fun d => gaussian_product_law (n d*d)
      [set x : paper_main_sample (n d) d |
        translation_fitting_error (n d) d x <= t]) 0) /\
  (forall delta : R, 0 < delta ->
    paper_main_tends_to (fun d => gaussian_product_law (n d*d)
      [set x : paper_main_sample (n d) d |
        universality_e_star alpha 3%:R-delta <=
          translation_fitting_error (n d) d x]) 1).

Definition shifted_error_statement : Prop :=
  shifted_error_measurable_statement /\ shifted_error_limit_statement.
