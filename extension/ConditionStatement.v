(* The optimal condition number of an exact fit at fourth moment three, for
   finite and countable mixtures of product laws, over the definitions of
   ConditionDefinitions, CountableMixtureDefinitions, MixtureDefinitions,
   UniversalityDefinitions and the frozen PaperMainDefinitions: the
   theorem of section 4.1 of notes/phase6-three-extensions.md, (20) and
   (21), in the form of section 4.4 of notes/three-extensions-plan.md.

   This file holds the statement only.

   Setting. K > 0 is the subgaussian constant of the components and
   alpha > 0 the limit of n/d^2 (universality_density_tends_to). The
   families of laws are those of MixtureStatement (finite mixtures,
   mixture_family K N w mu) and of CountableMixtureStatement (countable
   mixtures, countable_mixture_family K w mu), with fourth moment 3 under
   the mixture (mixture_fourth_moment 3, countable_fourth_moment 3): then
   the covariance of the features (x x^T - I) / sqrt d is (2/d) times the
   identity, and the Gaussian curve alpha_C of ConditionDefinitions
   applies. The event that the sample has an exact fit of condition number
   at most C is universality_conditioned_fit_event (n d) d C, the event of
   part 1 of mixture_statement with C in place of c, and p -> l is
   paper_main_tends_to.

   condition_statement, for every K > 0, C > 1 and alpha > 0: the event is
   measurable, and for every finite family of fourth moment 3 and every n
   with n/d^2 -> alpha,
   1. if alpha < alpha_C, its probability tends to 1;
   2. if alpha > alpha_C, its probability tends to 0.
   Nothing is asserted at alpha = alpha_C.

   condition_number_statement, for every K > 0 and 0 < alpha < 1/4: for
   every finite family of fourth moment 3, every n with n/d^2 -> alpha,
   every eps > 0 and delta > 0, and every large d, outside a measurable set
   of samples of probability at most delta, the optimal condition number
   of the sample (data_condition_number) is finite and within eps of
   C_star(alpha): it tends to C_star(alpha) in probability.

   countable_condition_statement and countable_condition_number_statement
   are the same two statements for countable families, with
   countable_mixture_probability in place of mixture_probability.

   condition_theorem_statement is the conjunction of the four.

   Choices, for the reviewer. Every quantifier is universal except the
   dimension D and the exceptional set of (21): there is no constant to
   choose. (21) is stated outside a measurable set of small probability,
   as the interpolation statements are; the measurability of the optimal
   condition number is not asserted (it holds, but the proof does not need
   it). The fourth moment 3 is written as a number. The relation to the
   frozen statements: at kappa = 3, part 1 of mixture_statement gives a
   fit of condition number at most some c below alpha*(3) = 1/4;
   condition_statement locates the threshold for every C, and alpha_C
   increases to 1/4 as C -> oo.

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
Open Scope ring_scope.

(* (20) for finite mixtures of fourth moment 3: the threshold alpha_C of a
   fit of condition number at most C. *)
Definition condition_statement : Prop :=
forall K C alpha : R, 0 < K -> 1 < C -> 0 < alpha ->
(forall n d : nat, measurable (universality_conditioned_fit_event n d C)) /\
(forall (N : nat -> nat) (w : nat -> nat -> R)
        (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment 3%:R N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  (alpha < condition_alpha C ->
   paper_main_tends_to
     (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 1) /\
  (condition_alpha C < alpha ->
   paper_main_tends_to
     (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 0)).

(* (21) for finite mixtures of fourth moment 3 and 0 < alpha < 1/4:
   outside a measurable set of samples of probability at most delta, the
   optimal condition number is within eps of C_star(alpha). *)
Definition condition_number_statement : Prop :=
forall K alpha : R, 0 < K -> 0 < alpha -> alpha < 4%:R^-1 ->
forall (N : nat -> nat) (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment 3%:R N w mu ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps delta : R, 0 < eps -> 0 < delta ->
exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (mixture_probability (N d) (w d) (mu d) (n d) d E <= delta%:E)%E &
  forall x, ~ E x ->
    (`|data_condition_number (n d) d x - (condition_star alpha)%:E| <=
     eps%:E)%E].

(* (20) for countable mixtures of fourth moment 3. *)
Definition countable_condition_statement : Prop :=
forall K C alpha : R, 0 < K -> 1 < C -> 0 < alpha ->
(forall n d : nat, measurable (universality_conditioned_fit_event n d C)) /\
(forall (w : nat -> nat -> R)
        (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment 3%:R w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  (alpha < condition_alpha C ->
   paper_main_tends_to
     (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 1) /\
  (condition_alpha C < alpha ->
   paper_main_tends_to
     (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                 (universality_conditioned_fit_event (n d) d C)) 0)).

(* (21) for countable mixtures of fourth moment 3. *)
Definition countable_condition_number_statement : Prop :=
forall K alpha : R, 0 < K -> 0 < alpha -> alpha < 4%:R^-1 ->
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu -> countable_fourth_moment 3%:R w mu ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps delta : R, 0 < eps -> 0 < delta ->
exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (countable_mixture_probability (w d) (mu d) (n d) d E <= delta%:E)%E &
  forall x, ~ E x ->
    (`|data_condition_number (n d) d x - (condition_star alpha)%:E| <=
     eps%:E)%E].

Definition condition_theorem_statement : Prop :=
  [/\ condition_statement, condition_number_statement,
      countable_condition_statement & countable_condition_number_statement].
