(* The condition-number curve at every fourth moment kappa > 1: its root,
   its variational value, its integral formula, its range, its inverse and
   its value at kappa = 3, over the definitions of ConditionKappaDefinitions,
   ConditionDefinitions, UniversalityDefinitions and the frozen
   PaperMainDefinitions. Item 1 of the section Phase 11 of AGENTS.md (the
   math plan notes/general-fourth-moment-condition-plan.md, sections 1 to 3;
   the plan notes/phase11-plan.md, section 4).

   This file holds the statement only.

   Setting. kappa > 1 and c = (kappa - 3) / 2 > -1. For C > 1, F, the root
   u = u_{C,kappa}, the cutoff ell = ell_{C,kappa}, the curve
   alpha(C, kappa), the inverse C_star(alpha, kappa) and the value of the
   variational problem are those of ConditionKappaDefinitions.
   alpha*(kappa) is universality_alpha_star kappa, the frozen threshold of
   UniversalityDefinitions (the threshold of an exact positive
   semidefinite fit, with no condition on the condition number).

   condition_kappa_curve_statement, for every kappa > 1:
   (a) the root: for every C > 1, 0 < u < sqrt 2,
       -sqrt 2 < ell < u, F(u) = 0, and u is the only zero of F in
       [0, sqrt 2];
   (b) the variational value: for every C > 1, alpha(C, kappa) is the value
       of the variational problem (condition_kappa_value C kappa), the least
       upper bound of V_c(q) over the measurable profiles q with
       t <= q <= C t for some t >= 0;
   (c) the integral formula: for every C > 1, alpha(C, kappa) is
       1 / (3 pi) times the Lebesgue integral of (2 - z^2)^(3/2) over the
       interval [ell, u], written Num.sqrt (2 - z^2) ^+ 3;
   (d) the range: for every C > 1, 0 < alpha(C, kappa) < alpha*(kappa);
       C |-> alpha(C, kappa) is strictly increasing and continuous on
       (1, oo); it tends to 0 as C decreases to 1 and to alpha*(kappa) as
       C tends to oo (with the bounds of the range, the one-sided
       inequalities below are these limits);
   (e) the inverse: for every 0 < alpha < alpha*(kappa), the number
       C_star = C_star(alpha, kappa) satisfies C_star > 1 and
       alpha(C_star, kappa) = alpha, and for every C > 1,
       alpha < alpha(C, kappa) if and only if C_star < C;
   (f) kappa = 3: for every C > 1, alpha(C, 3) = condition_alpha C, and
       for every 0 < alpha < 1/4, C_star(alpha, 3) = condition_star alpha
       (ConditionDefinitions). alpha*(3) = 1/4 is universality_alpha_star3
       of Gaussian/Threshold.v.

   Choices, for the reviewer.
   - Every claim is restricted to its stated domain: C > 1, kappa > 1 and
     0 < alpha < alpha*(kappa) (0 < alpha < 1/4 in (f)). Outside them the
     definitions are total, through the conventions of sup and inf, and
     nothing is claimed; in particular (f) does not assert the equality of
     the total definitions at C <= 1 or alpha >= 1/4.
   - Continuity and the limits are written with explicit epsilons, as in
     ConditionEndpoints, and continuity is asserted on the open interval
     (1, oo) only.
   - (b) uses everywhere bounds t <= q <= C t; that the same value arises
     when the bounds hold only almost everywhere under nu is a supporting
     lemma, not part of the statement (condition_kappa_value_ae and
     condition_kappa_alpha_ae of ConditionKappa/Curve.v). The arcsine
     evaluation A(u) - A(ell), with A(z) = arcsin(z / sqrt 2) / (2 pi)
     + z (5 - z^2) sqrt (2 - z^2) / (12 pi), is a supporting lemma too
     (condition_kappa_alpha_arcsine of ConditionKappa/Integral.v).
   - The statement makes no claim on the dependence in kappa
     (monotonicity, uniformity as kappa decreases to 1) or on the rates at
     the endpoints.

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
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
Open Scope ring_scope.

(* (a) The root u and the cutoff ell, for C > 1. *)
Definition condition_kappa_root (kappa : R) : Prop :=
  forall C : R, 1 < C ->
  [/\ 0 < condition_kappa_u C kappa < Num.sqrt 2%:R,
      - Num.sqrt 2%:R < condition_kappa_ell C kappa < condition_kappa_u C kappa,
      condition_kappa_F C kappa (condition_kappa_u C kappa) = 0 &
      forall u : R, 0 <= u <= Num.sqrt 2%:R -> condition_kappa_F C kappa u = 0 ->
        u = condition_kappa_u C kappa].

(* (b) alpha(C, kappa) is the value of the variational problem. *)
Definition condition_kappa_variational (kappa : R) : Prop :=
  forall C : R, 1 < C ->
    condition_kappa_alpha C kappa = condition_kappa_value C kappa.

(* (c) alpha(C, kappa) = (1 / (3 pi)) int_[ell, u] (2 - z^2)^(3/2) dz. *)
Definition condition_kappa_integral (kappa : R) : Prop :=
  forall C : R, 1 < C ->
    condition_kappa_alpha C kappa =
    (3%:R * pi)^-1 *
    \int[lebesgue_measure]_(z in [set z : R | condition_kappa_ell C kappa <= z
                                              <= condition_kappa_u C kappa])
       (Num.sqrt (2%:R - z ^+ 2) ^+ 3).

(* (d) The range: 0 < alpha(C, kappa) < alpha*(kappa), strict increase and
   continuity on (1, oo), the limits 0 at 1 and alpha*(kappa) at oo. *)
Definition condition_kappa_range (kappa : R) : Prop :=
  [/\ forall C : R, 1 < C ->
        0 < condition_kappa_alpha C kappa < universality_alpha_star kappa,
      forall C C' : R, 1 < C -> C < C' ->
        condition_kappa_alpha C kappa < condition_kappa_alpha C' kappa,
      forall C : R, 1 < C -> forall eps : R, 0 < eps ->
        exists2 delta : R, 0 < delta &
        forall C' : R, 1 < C' -> `|C' - C| < delta ->
          `|condition_kappa_alpha C' kappa - condition_kappa_alpha C kappa| < eps,
      forall eps : R, 0 < eps -> exists2 delta : R, 0 < delta &
        forall C : R, 1 < C -> C < 1 + delta -> condition_kappa_alpha C kappa < eps &
      forall eps : R, 0 < eps -> exists2 C0 : R, 1 < C0 &
        forall C : R, C0 <= C ->
          universality_alpha_star kappa - condition_kappa_alpha C kappa < eps].

(* (e) The inverse C_star(alpha, kappa), for 0 < alpha < alpha*(kappa). *)
Definition condition_kappa_inverse (kappa : R) : Prop :=
  forall alpha : R, 0 < alpha -> alpha < universality_alpha_star kappa ->
  [/\ 1 < condition_kappa_star alpha kappa,
      condition_kappa_alpha (condition_kappa_star alpha kappa) kappa = alpha &
      forall C : R, 1 < C ->
        alpha < condition_kappa_alpha C kappa <->
        condition_kappa_star alpha kappa < C].

(* (f) kappa = 3: the curve and the inverse of ConditionDefinitions. *)
Definition condition_kappa_three : Prop :=
  (forall C : R, 1 < C -> condition_kappa_alpha C 3%:R = condition_alpha C) /\
  (forall alpha : R, 0 < alpha -> alpha < 4%:R^-1 ->
     condition_kappa_star alpha 3%:R = condition_star alpha).

Definition condition_kappa_curve_statement : Prop :=
  (forall kappa : R, 1 < kappa ->
   [/\ condition_kappa_root kappa, condition_kappa_variational kappa,
       condition_kappa_integral kappa, condition_kappa_range kappa &
       condition_kappa_inverse kappa]) /\
  condition_kappa_three.
