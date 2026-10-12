(* The optimal condition number of an exact fit at every fourth moment
   kappa > 1, for finite and countable mixtures of product laws, over the
   definitions of ConditionKappaDefinitions, ConditionDefinitions,
   CountableMixtureDefinitions, MixtureDefinitions, UniversalityDefinitions
   and the frozen PaperMainDefinitions. Item 2 of the section Phase 11 of
   AGENTS.md (the math plan notes/general-fourth-moment-condition-plan.md,
   section 1; the plan notes/phase11-plan.md, section 4): the statements of
   ConditionStatement, which treat kappa = 3, for every kappa > 1.

   This file holds the statement only.

   Setting. kappa > 1 is the fourth moment, K > 0 the subgaussian constant
   of the components and alpha > 0 the limit of n/d^2
   (universality_density_tends_to). The families of laws are those of
   MixtureStatement (finite mixtures, mixture_family K N w mu) and of
   CountableMixtureStatement (countable mixtures,
   countable_mixture_family K w mu), with fourth moment kappa under the
   mixture (mixture_fourth_moment kappa, countable_fourth_moment kappa): the
   fourth moment averaged over the components, as in the frozen
   statements; a single component need not have fourth moment kappa. The
   event that the sample has an exact fit of condition number at most C is
   universality_conditioned_fit_event (n d) d C, and p -> l is
   paper_main_tends_to. alpha(C, kappa) and C_star(alpha, kappa) are those
   of ConditionKappaDefinitions, and alpha*(kappa) is
   universality_alpha_star kappa.

   condition_kappa_statement, for every kappa > 1, K > 0, C > 1 and
   alpha > 0: the event is measurable, and for every finite family of
   fourth moment kappa and every n with n/d^2 -> alpha,
   1. if alpha < alpha(C, kappa), its probability tends to 1;
   2. if alpha > alpha(C, kappa), its probability tends to 0.
   Nothing is asserted at alpha = alpha(C, kappa).

   condition_kappa_number_statement, for every kappa > 1, K > 0 and
   0 < alpha < alpha*(kappa): for every finite family of fourth moment
   kappa, every n with n/d^2 -> alpha, every eps > 0 and delta > 0, and
   every large d, outside a measurable set of samples of probability at
   most delta, the optimal condition number of the sample
   (data_condition_number) is finite and within eps of C_star(alpha,
   kappa): it tends to C_star(alpha, kappa) in probability.

   countable_condition_kappa_statement and
   countable_condition_kappa_number_statement are the same two statements
   for countable families, with countable_mixture_probability in place of
   mixture_probability.

   condition_kappa_theorem_statement is the conjunction of the four.

   Choices, for the reviewer. The four statements are those of
   ConditionStatement with these changes only: the quantifier over
   kappa > 1; mixture_fourth_moment kappa and countable_fourth_moment kappa
   in place of the fourth moment 3; alpha(C, kappa) in place of
   condition_alpha C and C_star(alpha, kappa) in place of condition_star
   alpha; and alpha < alpha*(kappa) in place of alpha < 1/4 in (21), since
   alpha(C, kappa) increases to alpha*(kappa) (ConditionKappaCurveStatement).
   The threshold covers every alpha > 0 away from alpha(C, kappa), alpha >=
   1/2 included. The quantifiers are those of ConditionStatement: there is
   no constant to choose. The bound alpha*(kappa) matters: for
   1 < kappa < 3 the curve can exceed 1/4 (numerically, alpha(10, 2) is
   about 0.253; notes/phase11-plan.md, section 2.1). Nothing is claimed
   uniformly in kappa.

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
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
Open Scope ring_scope.

(* (20) for finite mixtures of fourth moment kappa: the threshold
   alpha(C, kappa) of a fit of condition number at most C. *)
Definition condition_kappa_statement : Prop :=
forall kappa K C alpha : R, 1 < kappa -> 0 < K -> 1 < C -> 0 < alpha ->
(forall n d : nat, measurable (universality_conditioned_fit_event n d C)) /\
(forall (N : nat -> nat) (w : nat -> nat -> R)
        (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  (alpha < condition_kappa_alpha C kappa ->
   paper_main_tends_to
     (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 1) /\
  (condition_kappa_alpha C kappa < alpha ->
   paper_main_tends_to
     (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 0)).

(* (21) for finite mixtures of fourth moment kappa and
   0 < alpha < alpha*(kappa): outside a measurable set of samples of
   probability at most delta, the optimal condition number is within eps of
   C_star(alpha, kappa). *)
Definition condition_kappa_number_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
forall (N : nat -> nat) (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps delta : R, 0 < eps -> 0 < delta ->
exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (mixture_probability (N d) (w d) (mu d) (n d) d E <= delta%:E)%E &
  forall x, ~ E x ->
    (`|data_condition_number (n d) d x -
       (condition_kappa_star alpha kappa)%:E| <= eps%:E)%E].

(* (20) for countable mixtures of fourth moment kappa. *)
Definition countable_condition_kappa_statement : Prop :=
forall kappa K C alpha : R, 1 < kappa -> 0 < K -> 1 < C -> 0 < alpha ->
(forall n d : nat, measurable (universality_conditioned_fit_event n d C)) /\
(forall (w : nat -> nat -> R)
        (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  (alpha < condition_kappa_alpha C kappa ->
   paper_main_tends_to
     (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 1) /\
  (condition_kappa_alpha C kappa < alpha ->
   paper_main_tends_to
     (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 0)).

(* (21) for countable mixtures of fourth moment kappa. *)
Definition countable_condition_kappa_number_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps delta : R, 0 < eps -> 0 < delta ->
exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (countable_mixture_probability (w d) (mu d) (n d) d E <= delta%:E)%E &
  forall x, ~ E x ->
    (`|data_condition_number (n d) d x -
       (condition_kappa_star alpha kappa)%:E| <= eps%:E)%E].

Definition condition_kappa_theorem_statement : Prop :=
  [/\ condition_kappa_statement, condition_kappa_number_statement,
      countable_condition_kappa_statement &
      countable_condition_kappa_number_statement].
