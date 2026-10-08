(* Exact fitting for the paired law (notes/paired-dependent-sat.md), over
   the definitions of PairedDefinitions, MixtureDefinitions,
   UniversalityDefinitions and the frozen PaperMainDefinitions: the
   corollary of the finite-mixture theorem (MixtureStatement) for the
   paired law, over its whole range -1 <= eps <= 7/3, with eps allowed to
   depend on d (notes/mixture-product-universality.md, section 5; the plan
   notes/paired-law-plan-v2.md, section 4.1).

   This file holds the statement only.

   Setting. alpha > 0 is the limit of n/d^2. For every dimension d,
   eps d is a parameter in [-1, 7/3] and the n(d) points of R^d are i.i.d.:
   their coordinates come in independent pairs (2k, 2k + 1) with density
   1 + eps d h(x) h(y) against the product of two uniform laws on
   [-sqrt 3, sqrt 3], the last coordinate of an odd d being uniform. mu is
   any law with paired_uniform_spec, that is the uniform law. The
   probability of a set of samples is paired_probability (eps d) mu (n d)
   d. The coordinates have mean 0, variance 1 and fourth moment 9/5, so the
   threshold is alpha*(9/5) and the limiting error e*(alpha, 9/5). The
   events, the measurability conjuncts and the limits are those of
   mixture_statement.

   paired_statement, for every alpha > 0:
   1. If alpha < alpha*(9/5), there is c >= 1, depending only on alpha,
      such that for every sequence eps in [-1, 7/3], every uniform law mu
      and every n with n/d^2 -> alpha, with probability tending to one there
      is a positive definite S with x_i^T S x_i = 1 for every i, and one
      with condition number at most c.
   2. If alpha > alpha*(9/5), e*(alpha, 9/5) > 0 and, with probability
      tending to one, there is no S >= 0 with x_i^T S x_i = d for every i.
   3. Gamma_X tends to e*(alpha, 9/5) in probability.
   4. If alpha < 1/2, there is C, depending only on alpha, such that for
      every eps, mu and n as above, for every e > 0 and every large d,
      outside a measurable set of samples of probability at most e, the
      sample has the interpolation property mixture_interpolation (n d) d C.

   Choices, for the reviewer. eps may depend on d; a fixed eps is the
   constant sequence. The range [-1, 7/3] is closed: it is the range where
   the pair density is nonnegative. The constants c and C are chosen before
   eps, mu and n. 9/5 is written as a number; that it is the fourth moment
   of the coordinates is a lemma of the proof.

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
From EllipsoidUniversality Require Import MixtureDefinitions PairedDefinitions.
Open Scope ring_scope.

Definition paired_statement : Prop :=
forall alpha : R, 0 < alpha ->
[/\
(* 1. Below the threshold. *)
  (alpha < universality_alpha_star (9%:R / 5%:R) ->
   exists c : R, 1 <= c /\
   (forall n d : nat, measurable (universality_pd_fit_event n d)) /\
   (forall n d : nat, measurable (universality_conditioned_fit_event n d c)) /\
   (forall eps : nat -> R, (forall d : nat, - 1 <= eps d <= 7%:R / 3%:R) ->
    forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => paired_probability (eps d) mu (n d) d
                    (universality_pd_fit_event (n d) d)) 1 /\
      paper_main_tends_to
        (fun d => paired_probability (eps d) mu (n d) d
                    (universality_conditioned_fit_event (n d) d c)) 1)),
(* 2. Above the threshold. *)
  (universality_alpha_star (9%:R / 5%:R) < alpha ->
   0 < universality_e_star alpha (9%:R / 5%:R) /\
   (forall n d : nat, measurable (paper_main_fit_event n d)) /\
   (forall eps : nat -> R, (forall d : nat, - 1 <= eps d <= 7%:R / 3%:R) ->
    forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => paired_probability (eps d) mu (n d) d
                    (paper_main_fit_event (n d) d)) 0)),
(* 3. The optimal squared fitting error. *)
  ((forall (n d : nat) (e : R),
      measurable (universality_error_event n d
                    (universality_e_star alpha (9%:R / 5%:R)) e)) /\
   (forall eps : nat -> R, (forall d : nat, - 1 <= eps d <= 7%:R / 3%:R) ->
    forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
    forall e : R, 0 < e ->
      paper_main_tends_to
        (fun d => paired_probability (eps d) mu (n d) d
                    (universality_error_event (n d) d
                       (universality_e_star alpha (9%:R / 5%:R)) e)) 0)) &
(* 4. The interpolation estimate. *)
  (alpha < 2%:R^-1 ->
   exists C : R, 0 < C /\
   forall eps : nat -> R, (forall d : nat, - 1 <= eps d <= 7%:R / 3%:R) ->
   forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall e : R, 0 < e -> exists D : nat, forall d : nat, (D <= d)%nat ->
   exists E : set (paper_main_sample (n d) d), [/\ measurable E,
     (paired_probability (eps d) mu (n d) d E <= e%:E)%E &
     forall x, ~ E x -> mixture_interpolation (n d) d C x])].
