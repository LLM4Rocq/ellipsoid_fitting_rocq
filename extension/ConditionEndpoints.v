(* The endpoint behavior of the condition-number curve at fourth moment
   three: the expansions (11) and (13) of
   notes/gaussian-condition-number-theorem.md to the orders used, and the
   note's (34) and (35) (notes/phase6-three-extensions.md, section 4.7), in
   the form of item R4 of notes/optional-items-plan.md. Over the frozen
   definitions condition_alpha and condition_star of ConditionDefinitions,
   so that they describe the limits of condition_theorem.

   This file holds the statement only.

   Notation. alpha_C = condition_alpha C for C > 1, the threshold of n/d^2
   for an exact fit of condition number at most C, and
   C_star(alpha) = condition_star alpha for 0 < alpha < 1/4, the inverse
   of C |-> alpha_C, the limit of the optimal condition number. pi is
   MathComp's pi.

   condition_endpoints_statement is the conjunction of four parts.
   1. Near C = 1, the note's (11): with u = C - 1,
      alpha_C = (8 / (9 pi^2)) u^2 (1 - u) + O(u^4): there are K > 0 and
      u0 > 0 with |alpha_C - (8 / (9 pi^2)) u^2 (1 - u)| <= K u^4 for
      1 < C < 1 + u0.
   2. As C -> oo, the leading term of the note's (13):
      alpha_C = 1/4 - 8 / (3 pi C) + o(1 / C), that is
      C (1/4 - alpha_C) -> 8 / (3 pi).
   3. Near alpha = 0, the note's (34):
      C_star(alpha) = 1 + (3 pi / (2 sqrt 2)) sqrt alpha
                      + (9 pi^2 / 16) alpha + O(alpha^(3/2)):
      there are K > 0 and a0 > 0 such that the difference is at most
      K alpha sqrt alpha in absolute value for 0 < alpha < a0.
   4. Near alpha = 1/4, the note's (35):
      C_star(alpha) ~ 8 / (3 pi (1/4 - alpha)), that is
      (1/4 - alpha) C_star(alpha) -> 8 / (3 pi) as alpha -> 1/4 from below.

   Choices, for the reviewer. The O(.) terms of parts 1 and 3 are explicit
   inequalities with constants that exist; the asymptotic equivalences of
   parts 2 and 4 are limits written with eps and delta. As in the note,
   these limits are sequential: they concern the limits alpha_C and
   C_star(alpha) of condition_theorem, not a joint limit in the dimension.
   The finer terms of (13) and (14), in C^(-7/5), are not stated.

   The arithmetic, the order and the numerals are MathComp's at Stdlib's
   R (ring_scope). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences trigo.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
Open Scope ring_scope.

(* 1. With u = C - 1: alpha_C = (8 / (9 pi^2)) u^2 (1 - u) + O(u^4). *)
Definition condition_alpha_near_one : Prop :=
  exists K u0 : R, 0 < K /\ 0 < u0 /\
  forall C : R, 1 < C -> C < 1 + u0 ->
    `|condition_alpha C -
      8%:R / (9%:R * pi ^+ 2) * (C - 1) ^+ 2 * (1 - (C - 1))|
      <= K * (C - 1) ^+ 4.

(* 2. C (1/4 - alpha_C) -> 8 / (3 pi) as C -> oo. *)
Definition condition_alpha_near_infinity : Prop :=
  forall eps : R, 0 < eps -> exists C0 : R, 1 < C0 /\
  forall C : R, C0 <= C ->
    `|C * (4%:R^-1 - condition_alpha C) - 8%:R / (3%:R * pi)| <= eps.

(* 3. (34): C_star(alpha) = 1 + (3 pi / (2 sqrt 2)) sqrt alpha
   + (9 pi^2 / 16) alpha + O(alpha^(3/2)). *)
Definition condition_star_near_zero : Prop :=
  exists K a0 : R, 0 < K /\ 0 < a0 /\
  forall alpha : R, 0 < alpha -> alpha < a0 ->
    `|condition_star alpha -
      (1 + 3%:R * pi / (2%:R * Num.sqrt 2%:R) * Num.sqrt alpha
         + 9%:R * pi ^+ 2 / 16%:R * alpha)|
      <= K * alpha * Num.sqrt alpha.

(* 4. (35): (1/4 - alpha) C_star(alpha) -> 8 / (3 pi) as alpha -> 1/4. *)
Definition condition_star_near_quarter : Prop :=
  forall eps : R, 0 < eps -> exists delta : R, 0 < delta /\
  forall alpha : R, 4%:R^-1 - delta < alpha -> alpha < 4%:R^-1 ->
    `|(4%:R^-1 - alpha) * condition_star alpha - 8%:R / (3%:R * pi)| <= eps.

Definition condition_endpoints_statement : Prop :=
  [/\ condition_alpha_near_one, condition_alpha_near_infinity,
      condition_star_near_zero & condition_star_near_quarter].
