(* The three main statements of the paper (arXiv 2608.10184v1): thm:main
   (lines 141-147), thm:conditioned (lines 151-157) and cor:alternative
   (lines 164-170), over the definitions of PaperMainDefinitions.

   This file holds the statement only. MainTheorem proves it.

   Setting. d is the dimension and n : nat -> nat an arbitrary sequence of
   sample sizes. A sample is a tuple of n(d)*d independent standard normal
   coordinates under gaussian_product_law (n(d)*d), read as the n(d)
   points x_1, ..., x_n of R^d. p(n, d) = paper_main_probability is the
   probability of an event of samples. The density is n(d)/d^2; limsup <,
   limsup <= and liminf > are written out as eventual bounds, and p -> l as
   the elementary limit (PaperMainDefinitions, part 5).

   Each conjunct first asserts that the events it measures are measurable
   sets of samples, for every n and d, so that their probabilities are
   probabilities and not values of the measure on arbitrary sets; that
   assertion is a conclusion to prove, not a hypothesis.

   1. thm:main. (a) If limsup n/d^2 < 1/4 then p(n, d) -> 1. (b) If
      liminf n/d^2 > 1/4 then p(n, d) -> 0. Here p(n, d) is the probability
      that some S >= 0 satisfies x_i^T S x_i = d for every i.
   2. thm:conditioned. For every alpha* < 1/4 there are constants
      0 < lambda_- <= lambda_+ depending only on alpha* such that, if
      limsup n/d^2 <= alpha*, then with probability tending to one there is
      one S with x_i^T S x_i = d for every i, Tr S = d and
      lambda_- I <= S <= lambda_+ I.
   3. cor:alternative. Let E be the event that some real weights y with
      sum_i y_i = 0 make sum_i y_i x_i x_i^T positive definite. If
      limsup n/d^2 < 1/4 then P(E) -> 0; if liminf n/d^2 > 1/4 then
      P(E) -> 1.

   The arithmetic, the order and the numerals are MathComp's at Stdlib's
   R (ring_scope): 1 / 4%:R is the real number 1/4. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
Open Scope ring_scope.

Definition main_statement : Prop :=
(* thm:main: the sharp ellipsoid fitting transition, both phases. *)
((forall n d : nat, measurable (paper_main_fit_event n d)) /\
 (forall n : nat -> nat,
   (paper_main_limsup_lt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 1) /\
   (paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 0))) /\
(* thm:conditioned: well-conditioned fits of trace d below the threshold,
   with constants depending only on alpha*. *)
(forall alpha : R, alpha < 1 / 4%:R ->
  exists lm lp : R, 0 < lm /\ lm <= lp /\
  (forall n d : nat, measurable (paper_main_conditioned_event n d lm lp)) /\
  (forall n : nat -> nat,
    paper_main_limsup_le (paper_main_density n) alpha ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d (paper_main_conditioned_event (n d) d lm lp)) 1)) /\
(* cor:alternative: the threshold for balanced positive definite
   combinations, both limits. *)
((forall n d : nat, measurable (paper_main_balanced_pd_event n d)) /\
 (forall n : nat -> nat,
   (paper_main_limsup_lt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_balanced_pd_event (n d) d)) 0) /\
   (paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_balanced_pd_event (n d) d)) 1))).
