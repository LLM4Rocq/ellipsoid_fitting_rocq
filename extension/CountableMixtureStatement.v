(* The finite-mixture theorem (MixtureStatement) for countably many
   components, over the definitions of CountableMixtureDefinitions,
   MixtureDefinitions, UniversalityDefinitions and the frozen
   PaperMainDefinitions: the theorem of section 3.1 of
   notes/phase6-three-extensions.md, in the form of section 4.2 of
   notes/three-extensions-plan.md.

   This file holds the statement only.

   Setting. As in MixtureStatement, with a family of countable mixtures in
   place of a family of finite mixtures: kappa > 1 is the fourth moment of
   every coordinate under the mixture, K > 0 the subgaussian constant of
   the components, alpha > 0 the limit of n/d^2. For every dimension d the
   points are i.i.d. with the mixture of the product laws of the
   components s = 0, 1, 2, ..., with weights w d and coordinate laws
   mu d s j (countable_mixture_family K w mu, countable_fourth_moment kappa
   w mu); infinitely many weights may be positive. The probability of a set
   of samples is countable_mixture_probability (w d) (mu d) (n d) d. The
   events, the measurability conjuncts, the limits n/d^2 -> alpha
   (universality_density_tends_to) and p -> l (paper_main_tends_to) are
   those of MixtureStatement.

   countable_mixture_statement and countable_interpolation_statement are
   mixture_statement and mixture_interpolation_statement, word for word,
   with these families and this probability:
   1. below the threshold alpha*(kappa), a positive definite fit with
      probability tending to one, and one of condition number at most c,
      with c >= 1 depending only on alpha, kappa and K;
   2. above the threshold, e*(alpha, kappa) > 0 and no fit S >= 0 with
      x_i^T S x_i = d, with probability tending to one;
   3. for every alpha > 0, the optimal squared fitting error tends to
      e*(alpha, kappa) in probability;
   and, for 0 < alpha < 1/2 under (M1)-(M2) only, the interpolation
   property mixture_interpolation (n d) d C outside a measurable set of
   samples of small probability, with C depending only on alpha and K.

   countable_theorem_statement is the conjunction of the two.

   Choices, for the reviewer. The constants c, e*(alpha, kappa),
   alpha*(kappa) and C are those of the finite theorem, and c and C are
   chosen before the families of laws. Nothing is assumed about the decay
   of the weights: the proof truncates each dimension at its own index.
   (M2) is asked of every component, as in mixture_family. A finite family
   is a countable one, with weights zero from N d on and any component law
   there, and with the same probabilities of sets of samples, so these
   statements contain the frozen ones; the frozen ones stay as they are.

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
Open Scope ring_scope.

Definition countable_mixture_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
[/\
(* 1. Below the threshold: a positive definite fit, and one of condition
   number at most c, with probability tending to one. *)
  (alpha < universality_alpha_star kappa ->
   exists c : R, 1 <= c /\
   (forall n d : nat, measurable (universality_pd_fit_event n d)) /\
   (forall n d : nat, measurable (universality_conditioned_fit_event n d c)) /\
   (forall (w : nat -> nat -> R)
           (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
     forall n : nat -> nat, universality_density_tends_to n alpha ->
       paper_main_tends_to
         (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                     (universality_pd_fit_event (n d) d)) 1 /\
       paper_main_tends_to
         (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                     (universality_conditioned_fit_event (n d) d c)) 1)),
(* 2. Above the threshold: no positive semidefinite fit. *)
  (universality_alpha_star kappa < alpha ->
   0 < universality_e_star alpha kappa /\
   (forall n d : nat, measurable (paper_main_fit_event n d)) /\
   (forall (w : nat -> nat -> R)
           (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
     forall n : nat -> nat, universality_density_tends_to n alpha ->
       paper_main_tends_to
         (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                     (paper_main_fit_event (n d) d)) 0)) &
(* 3. For every alpha: the optimal squared fitting error tends to
   e*(alpha, kappa) in probability. *)
  ((forall (n d : nat) (eps : R),
      measurable (universality_error_event n d (universality_e_star alpha kappa) eps)) /\
   (forall (w : nat -> nat -> R)
           (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
     countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
     forall n : nat -> nat, universality_density_tends_to n alpha ->
     forall eps : R, 0 < eps ->
       paper_main_tends_to
         (fun d => countable_mixture_probability (w d) (mu d) (n d) d
                     (universality_error_event (n d) d
                        (universality_e_star alpha kappa) eps)) 0))].

Definition countable_interpolation_statement : Prop :=
forall K alpha : R, 0 < K -> 0 < alpha -> alpha < 2%:R^-1 ->
exists C : R, 0 < C /\
forall (w : nat -> nat -> R)
       (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  countable_mixture_family K w mu ->
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%nat ->
exists E : set (paper_main_sample (n d) d), [/\ measurable E,
  (countable_mixture_probability (w d) (mu d) (n d) d E <= eps%:E)%E &
  forall x, ~ E x -> mixture_interpolation (n d) d C x].

Definition countable_theorem_statement : Prop :=
  countable_mixture_statement /\ countable_interpolation_statement.
