(* Robustness of the optimal condition number at fourth moment three: the
   threshold (20) and the limit (21) of ConditionStatement for i.i.d. points
   of perturbed laws, over the definitions of RobustDefinitions,
   ConditionDefinitions, CountableMixtureDefinitions,
   UniversalityDefinitions and the frozen PaperMainDefinitions. Item R7 of
   phase 10, after section 7.1 of reviews/phase9-release-review.md.

   This file holds the statement only.

   Setting. K > 0 and alpha > 0 as in ConditionStatement. (w, mu) is an
   admissible countable mixture family of fourth moment 3
   (countable_mixture_family K w mu and countable_fourth_moment 3 w mu), and
   nu_d = robust_point_law (w d) (mu d) d is the law of one of its points.
   For a finite family (N, w, mu), extending the weights by zero
   (finite_weights) preserves the point law nu_d; an admissible countable
   family also requires filling the inactive component laws, s >= N d,
   with admissible laws, as fin_cmu of Countable/Theorem.v does, since
   countable_mixture_family asks every component law to be admissible.
   P d is an arbitrary law of a point of R^d, with no moment or tail
   assumption, such that d^2 tv(P d, nu_d) -> 0 (robust_close w mu P), as in
   RobustStatement. The sample consists of n d i.i.d. points of law P d,
   with law robust_sample_law (n d) d (P d), and n d / d^2 -> alpha
   (universality_density_tends_to). p -> l is paper_main_tends_to.

   robust_condition_statement, for every K > 0, C > 1 and alpha > 0: the
   probability that the sample has an exact fit of condition number at most
   C (universality_conditioned_fit_event (n d) d C)
   1. tends to 1 if alpha < alpha_C;
   2. tends to 0 if alpha > alpha_C.
   Nothing is asserted at alpha = alpha_C.

   robust_condition_number_statement, for every K > 0 and 0 < alpha < 1/4:
   for every eps > 0 and delta > 0 and every large d, outside a measurable
   set of samples of probability at most delta, the optimal condition
   number of the sample (data_condition_number) is finite and within eps of
   C_star(alpha): it tends to C_star(alpha) in probability.

   robust_condition_theorem_statement is the conjunction of the two.

   Choices, for the reviewer. The two statements are
   countable_condition_statement and countable_condition_number_statement
   of ConditionStatement with the samples of P d in place of those of the
   family; the measurability of the fit event, part of
   countable_condition_statement, is not repeated. As in RobustStatement,
   the families are countable, which contains the finite ones, the
   closeness is d^2 tv -> 0, and the fourth moment 3 concerns the family,
   not P d. The quantifiers are those of ConditionStatement: there is no
   constant to choose.

   The arithmetic, the order and the numerals are MathComp's at Stdlib's
   R (ring_scope). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences esum trigo.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import RobustDefinitions.

Open Scope ring_scope.

(* (20) for i.i.d. points of laws P d with d^2 tv(P d, nu_d) -> 0: the
   threshold alpha_C of a fit of condition number at most C. *)
Definition robust_condition_statement : Prop :=
forall K C alpha : R, 0 < K -> 1 < C -> 0 < alpha ->
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment 3%:R w mu ->
forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
  robust_close w mu P ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
  (alpha < condition_alpha C ->
   paper_main_tends_to
     (fun d => robust_sample_law (n d) d (P d)
                 (universality_conditioned_fit_event (n d) d C)) 1) /\
  (condition_alpha C < alpha ->
   paper_main_tends_to
     (fun d => robust_sample_law (n d) d (P d)
                 (universality_conditioned_fit_event (n d) d C)) 0).

(* (21) for i.i.d. points of laws P d with d^2 tv(P d, nu_d) -> 0 and
   0 < alpha < 1/4: outside a measurable set of samples of probability at
   most delta, the optimal condition number is within eps of
   C_star(alpha). *)
Definition robust_condition_number_statement : Prop :=
forall K alpha : R, 0 < K -> 0 < alpha -> alpha < 4%:R^-1 ->
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment 3%:R w mu ->
forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
  robust_close w mu P ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps delta : R, 0 < eps -> 0 < delta ->
exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (robust_sample_law (n d) d (P d) E <= delta%:E)%E &
  forall x, ~ E x ->
    (`|data_condition_number (n d) d x - (condition_star alpha)%:E| <=
     eps%:E)%E].

Definition robust_condition_theorem_statement : Prop :=
  robust_condition_statement /\ robust_condition_number_statement.
