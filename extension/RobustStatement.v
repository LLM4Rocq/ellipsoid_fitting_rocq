(* Robustness of the mixture theorems in total variation, and the
   contamination example that shows its scale, over the definitions of
   RobustDefinitions, CountableMixtureDefinitions, MixtureDefinitions,
   UniversalityDefinitions and the frozen PaperMainDefinitions: the note
   notes/phase6-three-extensions.md, section 3.2, (17), in the form of item
   R1 of notes/optional-items-plan.md. This file holds the statement only.

   Setting. kappa > 1, K > 0 and alpha > 0 as in CountableMixtureStatement:
   (w, mu) is an admissible countable mixture family
   (countable_mixture_family K w mu, countable_fourth_moment kappa w mu;
   a finite family is the countable one with weights zero from N d on), and
   nu_d = robust_point_law (w d) (mu d) d is the law of one of its points.
   P d is an arbitrary law of a point of R^d, with no moment or tail
   assumption, such that d^2 tv(P d, nu_d) -> 0 (robust_close w mu P). The
   sample consists of n d i.i.d. points of law P d, with law
   robust_sample_law (n d) d (P d), and n d / d^2 -> alpha. p -> l is
   paper_main_tends_to.

   robust_statement: the three conclusions of countable_mixture_statement
   hold for these samples, with the same constant c:
   1. below the threshold alpha*(kappa), a positive definite fit, and one
      of condition number at most c, with probability tending to one, c
      depending only on kappa, K and alpha, chosen before the family and
      before P;
   2. above it, no positive semidefinite fit, with probability tending to
      one;
   3. for every alpha, the optimal squared fitting error tends to
      e*(alpha, kappa) in probability.
   robust_interpolation_statement: the interpolation property of
   countable_interpolation_statement, for alpha < 1/2, outside a measurable
   set of samples of small probability, with C chosen before the family
   and before P. As there, the fourth moment is not assumed.

   contamination_statement, the necessity of the scale: below the
   threshold, for a finite family (N, w, mu) and lambda > 0, contaminate
   each point with probability lambda / n d into the zero point
   (contaminated_weights, contaminated_laws of RobustDefinitions). Then
   1. as soon as lambda <= n d, the contaminated point law is at total
      variation distance at most lambda / n d from nu_d: of order d^-2;
   2. the probability of a positive definite fit of value one tends to
      expR (- lambda) < 1, since a zero point has value 0 for every S.

   robust_theorem_statement is the conjunction of the three.

   Choices, for the reviewer. The perturbed laws are arbitrary probabilities
   on R^d; the closeness is d^2 tv -> 0, the note's (17). The conclusions
   are those of CountableMixtureStatement for the samples of the perturbed
   laws, without the measurability of the events and the positivity of
   e*, which those statements already assert. The contamination is a
   finite family with one more component, so that its sample law is the
   frozen mixture_probability; the event is that of a positive definite
   fit of value one, the first event of part 1.

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
From EllipsoidUniversality Require Import RobustDefinitions.

Open Scope ring_scope.

(* (17): the three conclusions of the mixture theorem for i.i.d. points of
   laws P d with d^2 tv(P d, nu_d) -> 0. *)
Definition robust_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
[/\
(* 1. Below the threshold: a positive definite fit, and one of condition
   number at most c, with probability tending to one. *)
  (alpha < universality_alpha_star kappa ->
   exists c : R, 1 <= c /\
   forall (w : nat -> nat -> R)
          (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
   forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
     robust_close w mu P ->
   forall n : nat -> nat, universality_density_tends_to n alpha ->
     paper_main_tends_to
       (fun d => robust_sample_law (n d) d (P d)
                   (universality_pd_fit_event (n d) d)) 1 /\
     paper_main_tends_to
       (fun d => robust_sample_law (n d) d (P d)
                   (universality_conditioned_fit_event (n d) d c)) 1),
(* 2. Above the threshold: no positive semidefinite fit. *)
  (universality_alpha_star kappa < alpha ->
   forall (w : nat -> nat -> R)
          (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
   forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
     robust_close w mu P ->
   forall n : nat -> nat, universality_density_tends_to n alpha ->
     paper_main_tends_to
       (fun d => robust_sample_law (n d) d (P d)
                   (paper_main_fit_event (n d) d)) 0) &
(* 3. For every alpha: the optimal squared fitting error tends to
   e*(alpha, kappa) in probability. *)
  (forall (w : nat -> nat -> R)
          (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
   forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
     robust_close w mu P ->
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall eps : R, 0 < eps ->
     paper_main_tends_to
       (fun d => robust_sample_law (n d) d (P d)
                   (universality_error_event (n d) d
                      (universality_e_star alpha kappa) eps)) 0)].

(* The interpolation property for i.i.d. points of laws P d with
   d^2 tv(P d, nu_d) -> 0, for alpha < 1/2. *)
Definition robust_interpolation_statement : Prop :=
forall K alpha : R, 0 < K -> 0 < alpha -> alpha < 2%:R^-1 ->
exists C : R, 0 < C /\
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu ->
forall P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R,
  robust_close w mu P ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (robust_sample_law (n d) d (P d) E <= eps%:E)%E &
  forall x, ~ E x -> mixture_interpolation (n d) d C x].

(* The contamination example: below the threshold, the contaminated laws
   are at total variation distance at most lambda / n d from the family,
   and the probability of a fit tends to expR (- lambda). *)
Definition contamination_statement : Prop :=
forall kappa K alpha lambda : R, 1 < kappa -> 0 < K -> 0 < alpha ->
  alpha < universality_alpha_star kappa -> 0 < lambda ->
forall (N : nat -> nat) (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
  (forall d : nat, lambda <= (n d)%:R ->
     ((n d)%:R%:E *
      robust_tv d
        (robust_point_law (contaminated_weights lambda (n d) (N d) (w d))
           (contaminated_laws (N d) (mu d)) d)
        (robust_point_law (finite_weights (N d) (w d)) (mu d) d)
      <= lambda%:E)%E) /\
  paper_main_tends_to
    (fun d => mixture_probability (N d).+1
                (contaminated_weights lambda (n d) (N d) (w d))
                (contaminated_laws (N d) (mu d)) (n d) d
                (universality_pd_fit_event (n d) d))
    (expR (- lambda)).

Definition robust_theorem_statement : Prop :=
  [/\ robust_statement, robust_interpolation_statement &
      contamination_statement].
