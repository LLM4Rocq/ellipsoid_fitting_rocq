(* Exact fitting for the latent-sign law (LatentSignDefinitions), over the
   definitions of LatentSignDefinitions, PairedDefinitions,
   MixtureDefinitions, UniversalityDefinitions and the frozen
   PaperMainDefinitions: the corollary of the finite-mixture theorem
   (MixtureStatement) for the law (1/2) lam_s^(x) d + (1/2) lam_(-s)^(x) d,
   lam_a = (1 + a h) mu, a mixture of two product laws, over the whole
   range 0 <= s <= 1, with s allowed to depend on d (AGENTS.md, section
   "Phase 7", item 3).

   This file holds the statement only.

   Setting. alpha > 0 is the limit of n/d^2. For every dimension d,
   s d is a parameter in [0, 1] and the n(d) points of R^d are i.i.d.: a
   hidden sign, + or - with probability 1/2, is drawn for each point, and
   given the signs the coordinates are independent, those of a point with
   the sign + of law (1 + s d h) mu and those of a point with the sign - of
   law (1 - s d h) mu, where mu is the uniform law on [-sqrt 3, sqrt 3]
   (any law with paired_uniform_spec). The probability of a set of
   samples is latent_probability (s d) mu (n d) d. The coordinates have
   mean 0, variance 1 and fourth moment 9/5 under the law of a point (the
   fourth moments 9/5 + 8 s / 35 and 9/5 - 8 s / 35 of the two components
   average to 9/5), so the threshold is alpha*(9/5) and the limiting error
   e*(alpha, 9/5). The events, the measurability conjuncts and the limits
   are those of mixture_statement and paired_statement.

   latent_sign_statement, for every alpha > 0:
   1. If alpha < alpha*(9/5), there is c >= 1, depending only on alpha,
      such that for every sequence s in [0, 1], every uniform law mu and
      every n with n/d^2 -> alpha, with probability tending to one there
      is a positive definite S with x_i^T S x_i = 1 for every i, and one
      with condition number at most c.
   2. If alpha > alpha*(9/5), e*(alpha, 9/5) > 0 and, with probability
      tending to one, there is no S >= 0 with x_i^T S x_i = d for every i.
   3. Gamma_X tends to e*(alpha, 9/5) in probability.
   4. If alpha < 1/2, there is C, depending only on alpha, such that for
      every s, mu and n as above, for every e > 0 and every large d,
      outside a measurable set of samples of probability at most e, the
      sample has the interpolation property mixture_interpolation (n d) d C.

   Choices, for the reviewer. s may depend on d; a fixed s is the constant
   sequence. The range [0, 1] is closed: for s > 1 the factor 1 - s h is
   negative where h is near 1, and the sign of s is immaterial, since
   s and -s give the same law. The constants c and C are chosen before s,
   mu and n, hence uniform over s in [0, 1]. 9/5 is written as a number;
   that it is the fourth moment of the coordinates is a lemma of the
   proof.

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
From EllipsoidUniversality Require Import LatentSignDefinitions.
Open Scope ring_scope.

Definition latent_sign_statement : Prop :=
forall alpha : R, 0 < alpha ->
[/\
(* 1. Below the threshold. *)
  (alpha < universality_alpha_star (9%:R / 5%:R) ->
   exists c : R, 1 <= c /\
   (forall n d : nat, measurable (universality_pd_fit_event n d)) /\
   (forall n d : nat, measurable (universality_conditioned_fit_event n d c)) /\
   (forall s : nat -> R, (forall d : nat, 0 <= s d <= 1) ->
    forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => latent_probability (s d) mu (n d) d
                    (universality_pd_fit_event (n d) d)) 1 /\
      paper_main_tends_to
        (fun d => latent_probability (s d) mu (n d) d
                    (universality_conditioned_fit_event (n d) d c)) 1)),
(* 2. Above the threshold. *)
  (universality_alpha_star (9%:R / 5%:R) < alpha ->
   0 < universality_e_star alpha (9%:R / 5%:R) /\
   (forall n d : nat, measurable (paper_main_fit_event n d)) /\
   (forall s : nat -> R, (forall d : nat, 0 <= s d <= 1) ->
    forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => latent_probability (s d) mu (n d) d
                    (paper_main_fit_event (n d) d)) 0)),
(* 3. The optimal squared fitting error. *)
  ((forall (n d : nat) (e : R),
      measurable (universality_error_event n d
                    (universality_e_star alpha (9%:R / 5%:R)) e)) /\
   (forall s : nat -> R, (forall d : nat, 0 <= s d <= 1) ->
    forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
    forall e : R, 0 < e ->
      paper_main_tends_to
        (fun d => latent_probability (s d) mu (n d) d
                    (universality_error_event (n d) d
                       (universality_e_star alpha (9%:R / 5%:R)) e)) 0)) &
(* 4. The interpolation estimate. *)
  (alpha < 2%:R^-1 ->
   exists C : R, 0 < C /\
   forall s : nat -> R, (forall d : nat, 0 <= s d <= 1) ->
   forall mu : probability (measurableTypeR R) R, paired_uniform_spec mu ->
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall e : R, 0 < e -> exists D : nat, forall d : nat, (D <= d)%nat ->
   exists E : set (paper_main_sample (n d) d), [/\ measurable E,
     (latent_probability (s d) mu (n d) d E <= e%:E)%E &
     forall x, ~ E x -> mixture_interpolation (n d) d C x])].
