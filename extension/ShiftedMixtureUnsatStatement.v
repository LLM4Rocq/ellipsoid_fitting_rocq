(* S5: symmetric product mixtures above the PSD threshold.
   Source: doc/shifted-gaussian.tex, symmetric-mixture nonexistence;
   reviews/shifted-gaussian-formalization-plan.md, target S5.

   One positive margin is chosen from kappa and alpha before K, either
   family, and the sample-size sequence. Symmetry is required only of the
   actual point law after mixing, not of its individual components.
   Outside one Borel exceptional cover, the fitting error minimized over
   all translations is at least that margin, and every nonzero PSD
   quadric with arbitrary linear and constant terms is excluded.
   The universal quadric predicate itself is not asserted to be Borel.
   Finite and countable families are separate conjuncts with the same
   margin. Accepted at commit 51c2e14 and frozen. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis.matrix Require Import psd_part quadric_certificate.
From GaussianAnalysis.probability Require Import symmetric_shift.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Shifted Require Import MixtureRows TranslationError.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition finite_shifted_mixture_unsat_statement (kappa alpha eta : R) : Prop :=
  forall K : R, 0 < K ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K N w mu),
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  mixture_fourth_moment kappa N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (mixture_probability (N d) (w d) (mu d) (n d) d E <= eps%:E)%E &
      forall x, ~ E x ->
        eta <= translation_fitting_error (n d) d x /\
        forall (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
          psdmx Q -> Q != 0 ->
          ~ (forall i : 'I_(n d), quadric_eval Q v c (paper_main_point x i) = 0)].

Definition countable_shifted_mixture_unsat_statement (kappa alpha eta : R) : Prop :=
  forall K : R, 0 < K ->
  forall (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : countable_mixture_family K w mu),
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  countable_fourth_moment kappa w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (countable_mixture_probability (w d) (mu d) (n d) d E <= eps%:E)%E &
      forall x, ~ E x ->
        eta <= translation_fitting_error (n d) d x /\
        forall (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
          psdmx Q -> Q != 0 ->
          ~ (forall i : 'I_(n d), quadric_eval Q v c (paper_main_point x i) = 0)].

Definition shifted_mixture_unsat_statement : Prop :=
  forall kappa alpha : R,
    1 < kappa -> universality_alpha_star kappa < alpha ->
  exists eta : R, 0 < eta /\
    finite_shifted_mixture_unsat_statement kappa alpha eta /\
    countable_shifted_mixture_unsat_statement kappa alpha eta.
