(* The finite-mixture extension of Theorem 1.2 of Koehler and Sohn,
   "Universality and sharp thresholds for ellipsoid fitting" (arXiv
   2608.27372, lines 164-190 of arxiv_v1.tex), over the definitions of
   MixtureDefinitions, UniversalityDefinitions and the frozen
   PaperMainDefinitions: the theorem of notes/mixture-product-universality.md
   (assumptions (M1)-(M3)), in the form of section 4.1 of
   notes/paired-law-plan-v2.md.

   This file holds the statement only.

   Setting. kappa > 1 is the fourth moment of every coordinate under the
   mixture, K > 0 the subgaussian constant of the components, alpha > 0 the
   limit of n/d^2. For every dimension d the points are i.i.d. with the
   mixture of N d product laws with weights w d and coordinate laws
   mu d s j (mixture_family K N w mu, mixture_fourth_moment kappa N w mu);
   N may grow with d. A sample is a tuple of n(d) * d coordinates; the
   probability of a set of samples is mixture_probability (N d) (w d)
   (mu d) (n d) d. n/d^2 -> alpha is universality_density_tends_to, and
   p -> l is paper_main_tends_to. The events are those of
   universality_statement: a positive definite fit of value 1, such a fit
   with condition number at most c, the frozen fit event (S >= 0 with value
   d), and the event that the optimal squared fitting error Gamma_X is
   farther than eps from e*(alpha, kappa). Each claim first asserts that
   the events it measures are measurable.

   mixture_statement, for every kappa > 1, K > 0 and alpha > 0:
   1. Below the threshold, alpha < alpha*(kappa): there is c >= 1,
      depending only on alpha, kappa and K, such that for every family of
      mixtures and every sequence n with n/d^2 -> alpha, with probability
      tending to one there is a positive definite S with x_i^T S x_i = 1
      for every i, and with probability tending to one such an S exists
      with condition number at most c.
   2. Above the threshold, alpha > alpha*(kappa): e*(alpha, kappa) > 0, and
      with probability tending to one there is no S >= 0 with
      x_i^T S x_i = d for every i.
   3. For every alpha > 0, Gamma_X tends to e*(alpha, kappa) in
      probability (KS Theorem 1.7 for these mixtures).

   mixture_interpolation_statement, for every K > 0 and 0 < alpha < 1/2,
   under (M1)-(M2) only (no condition on the fourth moment): there is C,
   depending only on alpha and K, such that for every family of mixtures
   and every n with n/d^2 -> alpha, for every eps > 0 and every large d,
   outside a measurable set of samples of probability at most eps, the
   sample has the interpolation property mixture_interpolation (n d) d C
   (KS Theorem 1.9 for these mixtures; the note's (M12)).

   mixture_theorem_statement is the conjunction of the two.

   Choices, for the reviewer (also in section 4.1 of the plan). The
   components are numbered by natural numbers below N d, with N an
   arbitrary function of d. (M2) is asked of every component, not only of
   those of positive weight. The constants c and C are chosen before the
   families of laws. Part 3 holds for every alpha, as KS Theorem 1.7;
   universality_statement states the error limit above the threshold only.
   The measurability of the interpolation event is not asserted; its
   exceptional set is a measurable set of small probability.

   The arithmetic, the order and the numerals are MathComp's at Stdlib's
   R (ring_scope). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
Open Scope ring_scope.

Definition mixture_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
[/\
(* 1. Below the threshold: a positive definite fit, and one of condition
   number at most c, with probability tending to one. *)
  (alpha < universality_alpha_star kappa ->
   exists c : R, 1 <= c /\
   (forall n d : nat, measurable (universality_pd_fit_event n d)) /\
   (forall n d : nat, measurable (universality_conditioned_fit_event n d c)) /\
   (forall (N : nat -> nat) (w : nat -> nat -> R)
           (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
     forall n : nat -> nat, universality_density_tends_to n alpha ->
       paper_main_tends_to
         (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                     (universality_pd_fit_event (n d) d)) 1 /\
       paper_main_tends_to
         (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                     (universality_conditioned_fit_event (n d) d c)) 1)),
(* 2. Above the threshold: no positive semidefinite fit. *)
  (universality_alpha_star kappa < alpha ->
   0 < universality_e_star alpha kappa /\
   (forall n d : nat, measurable (paper_main_fit_event n d)) /\
   (forall (N : nat -> nat) (w : nat -> nat -> R)
           (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
     forall n : nat -> nat, universality_density_tends_to n alpha ->
       paper_main_tends_to
         (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                     (paper_main_fit_event (n d) d)) 0)) &
(* 3. For every alpha: the optimal squared fitting error tends to
   e*(alpha, kappa) in probability. *)
  ((forall (n d : nat) (eps : R),
      measurable (universality_error_event n d (universality_e_star alpha kappa) eps)) /\
   (forall (N : nat -> nat) (w : nat -> nat -> R)
           (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
     forall n : nat -> nat, universality_density_tends_to n alpha ->
     forall eps : R, 0 < eps ->
       paper_main_tends_to
         (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                     (universality_error_event (n d) d
                        (universality_e_star alpha kappa) eps)) 0))].

Definition mixture_interpolation_statement : Prop :=
forall K alpha : R, 0 < K -> 0 < alpha -> alpha < 2%:R^-1 ->
exists C : R, 0 < C /\
forall (N : nat -> nat) (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (mixture_probability (N d) (w d) (mu d) (n d) d E <= eps%:E)%E &
  forall x, ~ E x -> mixture_interpolation (n d) d C x].

Definition mixture_theorem_statement : Prop :=
  mixture_statement /\ mixture_interpolation_statement.
