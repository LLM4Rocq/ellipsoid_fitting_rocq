(* Robustness of the optimal condition number at every fourth moment
   kappa > 1: the threshold and the limit of ConditionKappaStatement for
   i.i.d. points of perturbed laws, over the definitions of
   RobustDefinitions, ConditionKappaDefinitions, ConditionDefinitions,
   CountableMixtureDefinitions, MixtureDefinitions, UniversalityDefinitions
   and the frozen PaperMainDefinitions. Item 3 of the section Phase 11 of
   AGENTS.md (the math plan notes/general-fourth-moment-condition-plan.md,
   sections 1 and 6; the plan notes/phase11-plan.md, section 4): the
   statements of ConditionRobustStatement, which treat kappa = 3, for every
   kappa > 1, and for finite reference families as well.

   This file holds the statement only.

   Setting. kappa > 1, K > 0 and alpha > 0 as in ConditionKappaStatement.
   The reference family is either countable, (w, mu) with
   countable_mixture_family K w mu and countable_fourth_moment kappa w mu,
   whose point law is nu_d = robust_point_law (w d) (mu d) d; or finite,
   (N, w, mu) with mixture_family K N w mu and
   mixture_fourth_moment kappa N w mu, whose point law is
   nu_d = robust_point_law (finite_weights (N d) (w d)) (mu d) d, the weights
   extended by zero, as in contamination_statement of RobustStatement. P d
   is an arbitrary law of a point of R^d, with no moment or tail
   assumption, such that d^2 tv(P d, nu_d) -> 0 (robust_close, applied to
   the weights finite_weights (N d) (w d) for a finite family). The sample
   consists of n d i.i.d. points of law P d, with law
   robust_sample_law (n d) d (P d), and n d / d^2 -> alpha
   (universality_density_tends_to). p -> l is paper_main_tends_to.

   robust_condition_kappa_statement, for every kappa > 1, K > 0, C > 1 and
   alpha > 0 and a countable reference family: the probability that the
   sample has an exact fit of condition number at most C
   (universality_conditioned_fit_event (n d) d C)
   1. tends to 1 if alpha < alpha(C, kappa);
   2. tends to 0 if alpha > alpha(C, kappa).
   Nothing is asserted at alpha = alpha(C, kappa).

   robust_condition_kappa_number_statement, for every kappa > 1, K > 0 and
   0 < alpha < alpha*(kappa) and a countable reference family: for every
   eps > 0 and delta > 0 and every large d, outside a measurable set of
   samples of probability at most delta, the optimal condition number of
   the sample (data_condition_number) is finite and within eps of
   C_star(alpha, kappa): it tends to C_star(alpha, kappa) in probability.

   finite_robust_condition_kappa_statement and
   finite_robust_condition_kappa_number_statement are the same two
   statements around a finite reference family.

   condition_kappa_robust_theorem_statement is the conjunction of the four.

   Choices, for the reviewer. The first two statements are
   robust_condition_statement and robust_condition_number_statement of
   ConditionRobustStatement with the changes of ConditionKappaStatement:
   the quantifier over kappa > 1, countable_fourth_moment kappa,
   alpha(C, kappa), C_star(alpha, kappa) and alpha < alpha*(kappa). The
   last two state the finite case explicitly. A finite family becomes an
   admissible countable one only if the weights are extended by zero and
   the inactive component laws, s >= N d, are filled with admissible laws,
   as countable_of_finite of Countable/Theorem.v does:
   countable_mixture_family asks every component law to be admissible.
   Extending the weights by zero alone preserves the point law nu_d but
   does not make the family admissible. As in
   ConditionRobustStatement, the measurability of the fit event is not
   repeated, the closeness is d^2 tv -> 0, the fourth moment kappa concerns
   the reference family, not P d, and there is no constant to choose.

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
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import RobustDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.

Open Scope ring_scope.

(* The threshold for i.i.d. points of laws P d with d^2 tv(P d, nu_d) -> 0,
   around a countable family of fourth moment kappa. *)
Definition robust_condition_kappa_statement : Prop :=
forall kappa K C alpha : R, 1 < kappa -> 0 < K -> 1 < C -> 0 < alpha ->
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
  robust_close w mu P ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
  (alpha < condition_kappa_alpha C kappa ->
   paper_main_tends_to
     (fun d => robust_sample_law (n d) d (P d)
                 (universality_conditioned_fit_event (n d) d C)) 1) /\
  (condition_kappa_alpha C kappa < alpha ->
   paper_main_tends_to
     (fun d => robust_sample_law (n d) d (P d)
                 (universality_conditioned_fit_event (n d) d C)) 0).

(* The limit of the optimal condition number for i.i.d. points of laws P d
   with d^2 tv(P d, nu_d) -> 0, around a countable family of fourth moment
   kappa, for 0 < alpha < alpha*(kappa). *)
Definition robust_condition_kappa_number_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
  robust_close w mu P ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps delta : R, 0 < eps -> 0 < delta ->
exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (robust_sample_law (n d) d (P d) E <= delta%:E)%E &
  forall x, ~ E x ->
    (`|data_condition_number (n d) d x -
       (condition_kappa_star alpha kappa)%:E| <= eps%:E)%E].

(* The threshold around a finite family of fourth moment kappa. *)
Definition finite_robust_condition_kappa_statement : Prop :=
forall kappa K C alpha : R, 1 < kappa -> 0 < K -> 1 < C -> 0 < alpha ->
forall (N : nat -> nat) (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
  robust_close (fun d => finite_weights (N d) (w d)) mu P ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
  (alpha < condition_kappa_alpha C kappa ->
   paper_main_tends_to
     (fun d => robust_sample_law (n d) d (P d)
                 (universality_conditioned_fit_event (n d) d C)) 1) /\
  (condition_kappa_alpha C kappa < alpha ->
   paper_main_tends_to
     (fun d => robust_sample_law (n d) d (P d)
                 (universality_conditioned_fit_event (n d) d C)) 0).

(* The limit of the optimal condition number around a finite family of
   fourth moment kappa, for 0 < alpha < alpha*(kappa). *)
Definition finite_robust_condition_kappa_number_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
forall (N : nat -> nat) (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
  robust_close (fun d => finite_weights (N d) (w d)) mu P ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps delta : R, 0 < eps -> 0 < delta ->
exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (robust_sample_law (n d) d (P d) E <= delta%:E)%E &
  forall x, ~ E x ->
    (`|data_condition_number (n d) d x -
       (condition_kappa_star alpha kappa)%:E| <= eps%:E)%E].

Definition condition_kappa_robust_theorem_statement : Prop :=
  [/\ robust_condition_kappa_statement,
      robust_condition_kappa_number_statement,
      finite_robust_condition_kappa_statement &
      finite_robust_condition_kappa_number_statement].
