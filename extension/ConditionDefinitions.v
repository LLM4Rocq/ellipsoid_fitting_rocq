(* The glossary of the condition-number theorem at fourth moment three: the
   threshold of n/d^2 for an exact fit of condition number at most C, and
   the limit of the optimal condition number of an exact fit
   (notes/phase6-three-extensions.md, section 4.1; its Gaussian companion
   notes/gaussian-condition-number-theorem.md, sections 1 to 4; the plan
   notes/three-extensions-plan.md, section 4.3). Every definition is
   concrete and is meant to be read by the reviewer; the comment of
   ConditionStatement reads the statement. This module reuses
   universality_m, universality_s and universality_conditioned_fit_event
   of UniversalityDefinitions.

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope. nu is the semicircle law on [-sqrt 2, sqrt 2], of density
   sqrt (2 - x^2) / pi (universality_semicircle_density): the limit of the
   empirical law of the eigenvalues of G / sqrt d, G a standard Gaussian
   symmetric d x d matrix (diagonal variance 1, off-diagonal variance
   1/2). m(w) = int (x - w)_+ dnu(x) is universality_m w and
   v(w) = int (x - w)_+^2 dnu(x) is universality_s w. sup and inf are the
   least upper bound and the greatest lower bound of a set of reals
   (MathComp-Analysis); they are used below on nonempty sets bounded on
   the relevant side, for C > 1 and 0 < alpha < 1/4. ereal_inf is the
   greatest lower bound of a set of extended reals, +oo for the empty set.
   The condition number of a positive definite S is
   lambda_max(S) / lambda_min(S).

   1. t_C, for C > 1. The function t |-> m(-t) - C m(C t) is strictly
      increasing on [0, sqrt 2 / C], negative at 0 and positive at
      sqrt 2 / C, so it has a unique zero t_C in (0, sqrt 2 / C), the note's
      (4). It is written as the least upper bound of the t in
      [0, sqrt 2 / C] with m(-t) <= C m(C t), which is the interval
      [0, t_C]. t_C minimizes F_C(t) = v(-t) + v(C t) =
      int dist(x, [t, C t])^2 dnu(x) over t >= 0 (a lemma of the proof).
   2. alpha_C = 1/2 - v(-t_C) - v(C t_C), the note's (19). It is the limit
      of |Pi_C G|_F^2 / d^2, Pi_C the projection onto the cone of positive
      semidefinite matrices of condition number at most C, and the
      threshold of n/d^2 for an exact fit of condition number at most C.
      C |-> alpha_C is continuous and strictly increasing on (1, oo), from
      0 to 1/4 (lemmas of the proof).
   3. C_star(alpha), for 0 < alpha < 1/4: the inverse of C |-> alpha_C,
      written as the greatest lower bound of the C > 1 with
      alpha <= alpha_C. It is the C > 1 with alpha_C = alpha.
   4. The optimal condition number of a sample: the greatest lower bound of
      the reals c such that the sample has an exact fit of condition
      number at most c, that is some S and lm > 0 with
      lm I <= S <= c lm I and x_i^T S x_i = 1 for every i
      (universality_conditioned_fit_event n d c). It is an extended real,
      +oo when the sample has no positive definite fit.

   The module contains definitions only: no lemma, no Axiom, no Parameter,
   no Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. t_C: the unique t in (0, sqrt 2 / C) with m(-t) = C m(C t), written
   as the least upper bound of the t in [0, sqrt 2 / C] with
   m(-t) <= C m(C t). *)
Definition condition_t (C : R) : R :=
  sup [set t : R | 0 <= t <= Num.sqrt 2%:R / C /\
                   universality_m (- t) <= C * universality_m (C * t)].

(* 2. alpha_C = 1/2 - v(-t_C) - v(C t_C). *)
Definition condition_alpha (C : R) : R :=
  2%:R^-1 - universality_s (- condition_t C)
          - universality_s (C * condition_t C).

(* 3. C_star(alpha), the inverse of C |-> alpha_C on (0, 1/4): the greatest
   lower bound of the C > 1 with alpha <= alpha_C. *)
Definition condition_star (alpha : R) : R :=
  inf [set C : R | 1 < C /\ alpha <= condition_alpha C].

(* 4. The optimal condition number of an exact fit of the sample x: the
   greatest lower bound of the c such that some positive definite S of
   condition number at most c has x_i^T S x_i = 1 for every i; +oo if
   there is no such S. *)
Definition data_condition_number (n d : nat) (x : paper_main_sample n d) :
    \bar R :=
  ereal_inf [set c%:E | c in [set c : R |
    universality_conditioned_fit_event n d c x]].
