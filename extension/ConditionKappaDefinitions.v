(* The glossary of the condition-number theorem at every fourth moment
   kappa > 1: the curve alpha(C, kappa), the threshold of n/d^2 for an
   exact fit of condition number at most C; its inverse C_star(alpha,
   kappa); and the constrained semicircle variational problem whose value
   the curve is
   (notes/general-fourth-moment-condition-plan.md, section 2; the plan
   notes/phase11-plan.md, section 4). Every definition is concrete and is
   meant to be read by the reviewer; the comments of
   ConditionKappaCurveStatement, ConditionKappaStatement and
   ConditionKappaRobustStatement read the statements. This module reuses
   universality_m, universality_s and the semicircle integral of
   UniversalityDefinitions.
   The statements also reuse universality_conditioned_fit_event,
   universality_alpha_star, data_condition_number (ConditionDefinitions),
   robust_point_law and finite_weights (RobustDefinitions).

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope. nu is the semicircle law on [-sqrt 2, sqrt 2], of density
   sqrt (2 - z^2) / pi (universality_semicircle_density): the limit of the
   empirical law of the eigenvalues of G / sqrt d, G a standard Gaussian
   symmetric d x d matrix (diagonal variance 1, off-diagonal variance 1/2).
   int f dnu is universality_semicircle_integral f. m(w) = int (z - w)_+ dnu
   is universality_m w and v(w) = int (z - w)_+^2 dnu is universality_s w.
   sup and inf are the least upper bound and the greatest lower bound of a
   set of reals (MathComp-Analysis), 0 for a set that is empty or unbounded
   on that side. They are used below on sets that are nonempty and bounded
   on the relevant side for C > 1, kappa > 1 and 0 < alpha <
   alpha*(kappa), and the statements claim nothing outside these domains.
   c = (kappa - 3) / 2 > -1 is the excess of the fourth moment over the
   Gaussian value 3, halved.

   1. The root and the two cutoffs, for kappa > 1 and C > 1. With
      r = c / (1 + c) = (kappa - 3) / (kappa - 1) < 1,
        L(u) = (u + r (C - 1)^2 m(u)) / C   and   F(u) = m(-L(u)) - C m(u).
      F is continuous and strictly increasing on [0, sqrt 2], negative at 0
      and positive at sqrt 2, so it has a unique zero u_{C,kappa} in
      (0, sqrt 2) (a conjunct of the curve statement). It is written as the
      least upper bound of the u in [0, sqrt 2] with F(u) <= 0, which is
      the interval [0, u_{C,kappa}]; the definition needs no existence
      assumption. ell_{C,kappa} = L(u_{C,kappa}), and
      -sqrt 2 < ell_{C,kappa} < u_{C,kappa}. They are the two clipping
      points of the optimal profile of part 4: with
      mu = (C - 1) m(u) / (1 + c) and t = (u - ell) / (C - 1), the profile
      q(z) = min (max (z - c mu, t), C t) has int q dnu = mu, and
      ell = t + c mu, u = C t + c mu (supporting lemmas of item S2, not
      conjuncts of the curve statement).
   2. The curve. J(w) = v(w) + w m(w) and
        alpha(C, kappa) = J(ell_{C,kappa}) - J(u_{C,kappa}),
      which equals 1 / (3 pi) times the integral of (2 - z^2)^(3/2) over
      [ell, u], since J'(w) = -(2 - w^2)^(3/2) / (3 pi) on [-sqrt 2, sqrt 2]
      (a conjunct of the curve statement). For fixed kappa,
      C |-> alpha(C, kappa) is continuous and strictly increasing on
      (1, oo), from 0 to alpha*(kappa) = universality_alpha_star kappa.
      At kappa = 3, c = r = 0. Two conjuncts of the curve statement relate
      the curve to ConditionDefinitions: alpha(C, 3) = condition_alpha C
      for C > 1, and C_star(alpha, 3) = condition_star alpha for
      0 < alpha < 1/4. The cutoff identities u = C t_C and ell = t_C are
      supporting lemmas (item S4), not conjuncts.
   3. C_star(alpha, kappa), for 0 < alpha < alpha*(kappa): the inverse of
      C |-> alpha(C, kappa), written as the greatest lower bound of the
      C > 1 with alpha <= alpha(C, kappa), as condition_star is. It is the
      C > 1 with alpha(C, kappa) = alpha.
   4. The variational problem. For a profile q : R -> R,
        V_c(q) = 2 int z q(z) dnu(z) - int q^2 dnu - c (int q dnu)^2.
      The integrals are those of universality_semicircle_integral. A
      profile is admissible for C when it is Borel measurable
      (measurable_fun on measurableTypeR R) and t <= q(z) <= C t for every
      real z, for some t >= 0: a profile of condition ratio at most C,
      q = 0 included (t = 0). It is bounded, so the three integrals of V_c
      are finite. The value is the least upper bound of V_c over the
      admissible profiles. Conjunct (b) of the curve statement asserts only
      that it equals alpha(C, kappa) for C > 1 and kappa > 1; that it is
      attained at the profile of part 1 is a supporting lemma (item S2).
      This is the limit problem of the Gaussian side: (1/d) times the
      maximum of
      2 <G / sqrt d, T_kappa S> - |S|_F^2 - c |diag S|_F^2 over the
      symmetric S of condition number at most C, T_kappa the map
      cone_map kappa of Gaussian/Cones.v; that limit is a step of the
      proof, not a definition.

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

(* 1. The root and the two cutoffs. *)

(* L(u) = (u + r (C - 1)^2 m(u)) / C, with r = (kappa - 3) / (kappa - 1). *)
Definition condition_kappa_L (C kappa u : R) :=
  (u + (kappa - 3%:R) / (kappa - 1) * (C - 1) ^+ 2 * universality_m u) / C.

(* F(u) = m(-L(u)) - C m(u). *)
Definition condition_kappa_F (C kappa u : R) :=
  universality_m (- condition_kappa_L C kappa u)%R - C * universality_m u.

(* u_{C,kappa}: the unique zero of F in (0, sqrt 2), written as the least
   upper bound of the u in [0, sqrt 2] with F(u) <= 0. *)
Definition condition_kappa_u (C kappa : R) :=
  sup [set u : R | 0 <= u <= Num.sqrt 2%:R /\
                   condition_kappa_F C kappa u <= 0].

(* ell_{C,kappa} = L(u_{C,kappa}). *)
Definition condition_kappa_ell (C kappa : R) :=
  condition_kappa_L C kappa (condition_kappa_u C kappa).

(* 2. The curve. *)

(* J(w) = v(w) + w m(w). *)
Definition condition_kappa_J (w : R) :=
  universality_s w + w * universality_m w.

(* alpha(C, kappa) = J(ell_{C,kappa}) - J(u_{C,kappa}). *)
Definition condition_kappa_alpha (C kappa : R) :=
  condition_kappa_J (condition_kappa_ell C kappa)
  - condition_kappa_J (condition_kappa_u C kappa).

(* 3. C_star(alpha, kappa), the inverse of C |-> alpha(C, kappa) on
   (0, alpha*(kappa)): the greatest lower bound of the C > 1 with
   alpha <= alpha(C, kappa). *)
Definition condition_kappa_star (alpha kappa : R) :=
  inf [set C : R | 1 < C /\ alpha <= condition_kappa_alpha C kappa].

(* 4. The variational problem. *)

(* V_c(q) = 2 int z q(z) dnu(z) - int q^2 dnu - c (int q dnu)^2, with
   c = (kappa - 3) / 2. *)
Definition condition_kappa_objective (kappa : R) (q : R -> R) :=
  2%:R * universality_semicircle_integral (fun z => z * q z)
  - universality_semicircle_integral (fun z => q z ^+ 2)
  - (kappa - 3%:R) / 2%:R * universality_semicircle_integral q ^+ 2.

(* The admissible profiles for C: q is measurable and, for some t >= 0,
   t <= q(z) <= C t for every z. *)
Definition condition_kappa_profile (C : R) (q : R -> R) : Prop :=
  measurable_fun [set: measurableTypeR R]
    (q : measurableTypeR R -> measurableTypeR R) /\
  exists2 t : R, 0 <= t & forall z : R, t <= q z <= C * t.

(* The value of the problem: the least upper bound of V_c over the
   admissible profiles for C. *)
Definition condition_kappa_value (C kappa : R) :=
  sup [set condition_kappa_objective kappa q | q in condition_kappa_profile C].
