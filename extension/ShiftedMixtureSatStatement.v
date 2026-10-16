(* S6: positive definite exact fitting for sparse deterministic shifts.
   Source: doc/shifted-gaussian.tex, sparse non-Gaussian shifts;
   reviews/shifted-gaussian-formalization-plan.md, target S6.

   The proved statement intentionally strengthens the plan by requiring
   no central symmetry. Conditional product structure, centering,
   isotropy, a common sub-Gaussian bound, and the mixture-averaged fourth
   moment suffice. The shift has arbitrary magnitude and may be supported
   on any changing set of o(d) coordinates. The probability limit holds
   for each deterministic shift sequence; no event common to all shifts
   is asserted. No baseline family or interpolation-target hypothesis is
   left in the statement. Finite and countable families are explicit.
   Accepted at commit 51c2e14 and frozen. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis.matrix Require Import coordinate_blocks.
From GaussianAnalysis.analysis Require Import family_reindexing.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Shifted Require Import Translations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition finite_shifted_mixture_sat_statement : Prop :=
  forall kappa K alpha : R,
    1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (n : nat -> nat),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
  universality_density_tends_to n alpha ->
  forall m : forall d, 'cV[RR]_d,
  family_sequence_limit
    (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  (forall d, measurable
    (sample_translate (m d) @^-1` universality_pd_fit_event (n d) d)) /\
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
      (sample_translate (m d) @^-1` universality_pd_fit_event (n d) d)) 1.

Definition countable_shifted_mixture_sat_statement : Prop :=
  forall kappa K alpha : R,
    1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  forall (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (n : nat -> nat),
  countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
  universality_density_tends_to n alpha ->
  forall m : forall d, 'cV[RR]_d,
  family_sequence_limit
    (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  (forall d, measurable
    (sample_translate (m d) @^-1` universality_pd_fit_event (n d) d)) /\
  paper_main_tends_to
    (fun d => countable_mixture_probability (w d) (mu d) (n d) d
      (sample_translate (m d) @^-1` universality_pd_fit_event (n d) d)) 1.

Definition shifted_mixture_sat_statement : Prop :=
  finite_shifted_mixture_sat_statement /\ countable_shifted_mixture_sat_statement.
