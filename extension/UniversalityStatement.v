(* Theorem 1.2 of Koehler and Sohn, "Universality and sharp thresholds for
   ellipsoid fitting" (arXiv 2608.27372, lines 164-190 of arxiv_v1.tex),
   over the definitions of UniversalityDefinitions and of the frozen
   PaperMainDefinitions.

   This file holds the statement only. Nothing proves it yet; the
   feasibility study extension/README.md says what a proof would need.

   Setting. kappa > 1 is the common fourth moment of the coordinates, K > 0
   their subgaussian constant, alpha > 0 the limit of n/d^2. For every
   dimension d, nu d j is the law of coordinate j of a point; the family may
   depend on d, and every nu d j (j < d) is a universality_coordinate_law
   with the same kappa and K, as the paper allows (lines 166-171). A
   sample is a tuple of n(d)*d coordinates under
   universality_sample_law (nu d) (n d) d, read as the n(d) points
   x_1, ..., x_n of R^d. The probabilities are universality_probability;
   n/d^2 -> alpha is universality_density_tends_to, and p -> l is the
   elementary limit paper_main_tends_to.

   Each claim first asserts that the events it measures are measurable
   sets of samples, for every n and d, so that their probabilities are
   probabilities and not values of the measure on arbitrary sets; those
   assertions are conclusions to prove, not hypotheses.

   1. Theorem 1.2 (i), below the threshold. If alpha < alpha*(kappa) then
      there is a constant c >= 1, depending only on alpha, kappa and K,
      such that for every admissible family of laws and every sequence n
      with n/d^2 -> alpha, with probability tending to one there is a
      positive definite S with x_i^T S x_i = 1 for every i, and with
      probability tending to one such an S exists with condition number at
      most c (lm I <= S <= c lm I for some lm > 0). The second limit implies
      the first; both are stated, as the paper states the fit and then its
      conditioning.
   2. Theorem 1.2 (ii), above the threshold. If alpha > alpha*(kappa) then
      e*(alpha, kappa) > 0, and for every admissible family of laws and
      every sequence n with n/d^2 -> alpha: with probability tending to
      one there is no S >= 0 with x_i^T S x_i = d for every i (the frozen
      fit event, equal for d >= 1 to the paper's fit with value 1 up to the
      scaling S |-> d S); and the optimal squared fitting error Gamma_X
      converges in probability to e*(alpha, kappa): for every eps > 0,
      the probability of |Gamma_X - e*(alpha, kappa)| > eps tends to 0.

   Choices, for the reviewer (also in extension/README.md). The limit
   hypothesis is the paper's convergence n/d^2 -> alpha, not the
   limsup/liminf conditions of MainStatement; the paper's conclusions for
   one alpha on each side of the threshold are what the limits of the
   error need. The threshold is the scalar formula alpha*(kappa) =
   E_kappa(omega_kappa), with the variational form as a second definition.
   The condition number c of the paper's "lambda_max(R)/lambda_min(R) =
   O(1)" is a constant chosen after alpha, kappa and K and before the laws
   and the sequence. The subgaussian norm is read as
   E exp (X^2 / K^2) <= 2.

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
Open Scope ring_scope.

Definition universality_statement : Prop :=
forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
(* Theorem 1.2 (i): a well-conditioned positive definite fit below the
   threshold, with a condition number depending only on alpha, kappa, K. *)
((alpha < universality_alpha_star kappa ->
  exists c : R, 1 <= c /\
  (forall n d : nat, measurable (universality_pd_fit_event n d)) /\
  (forall n d : nat, measurable (universality_conditioned_fit_event n d c)) /\
  (forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j : nat, (j < d)%nat -> universality_coordinate_law kappa K (nu d j)) ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => universality_probability (nu d) (n d) d (universality_pd_fit_event (n d) d)) 1 /\
      paper_main_tends_to
        (fun d => universality_probability (nu d) (n d) d
                    (universality_conditioned_fit_event (n d) d c)) 1)) /\
(* Theorem 1.2 (ii): no positive semidefinite fit above the threshold, and
   the optimal squared fitting error tends to e*(alpha, kappa) > 0. *)
 (universality_alpha_star kappa < alpha ->
  0 < universality_e_star alpha kappa /\
  (forall n d : nat, measurable (paper_main_fit_event n d)) /\
  (forall (n d : nat) (eps : R),
    measurable (universality_error_event n d (universality_e_star alpha kappa) eps)) /\
  (forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j : nat, (j < d)%nat -> universality_coordinate_law kappa K (nu d j)) ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => universality_probability (nu d) (n d) d (paper_main_fit_event (n d) d)) 0 /\
      forall eps : R, 0 < eps ->
        paper_main_tends_to
          (fun d => universality_probability (nu d) (n d) d
                      (universality_error_event (n d) d (universality_e_star alpha kappa) eps)) 0))).
