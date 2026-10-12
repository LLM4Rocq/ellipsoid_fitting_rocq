(* The optimal profile, the curve alpha(C, kappa) and its inverse, at
   Stdlib's R: items S2 and S3 of phase 11 (notes/phase11-plan.md, sections
   3.2 and 5; the math plan notes/general-fourth-moment-condition-plan.md,
   section 3; lane C). The definitions are those of
   ConditionKappaDefinitions; the root is item S1 (Scalar).

   Setting. kappa > 1, c = (kappa - 3) / 2 > -1, a0 = min(1, 1 + c), C > 1;
   m, v, u = u_{C,kappa}, ell = ell_{C,kappa}, J and V_c as in
   ConditionKappaDefinitions.

   Results to prove here.
   - S2. With mu = (C - 1) m(u) / (1 + c), t = (u - ell) / (C - 1) and
     p(z) = min (max (z - c mu, t), C t): t > 0, int p dnu = mu,
     ell = t + c mu and u = C t + c mu; p is admissible and maximizes V_c
     over the admissible profiles (the residual balance m(-ell) = C m(u)
     for the first-order inequality, and
     int h^2 dnu + c (int h dnu)^2 >= a0 int h^2 dnu for both signs of c);
     alpha(C, kappa) = V_c(p) = J(ell) - J(u) = condition_kappa_value C
     kappa. The dual form and its window: interface I2 below.
   - S3. C |-> alpha(C, kappa) is continuous and strictly increasing on
     (1, oo), with limit 0 at 1 and limit alpha*(kappa) at oo (through
     universality_alpha_star_variationalE of Gaussian/Threshold.v and the
     equivalence of the quadratic and ratio forms);
     0 < alpha(C, kappa) < alpha*(kappa) < 1/2; the inverse C_star(alpha,
     kappa) and its order characterization; the analogues of
     condition_alpha_left and condition_alpha_right of Condition/Curve.v.
     These are interface I3, used by items D1 and D2 (Sat, Unsat, lane B)
     and A1 (Theorem).

   Interface I2 (used by item M4, GaussianLimit, lane A). The dual function
   below is
     condition_kappa_dual C kappa mu
       = 1/2 + c (1 + c) mu^2 - inf_(t >= 0) (v(-t - c mu) + v(C t + c mu)),
   the limit of (1/d) (|Pi_K(H - c mu I)|_F^2 + c d mu^2) for
   H = G / sqrt d, K = cond_cone C. The inner infimum is the clipping energy
   of the semicircle law shifted by c mu: int dist(z - c mu, [t, C t])^2
   dnu(z) = v(-t - c mu) + v(C t + c mu), since nu is symmetric. Item S2
   proves, for C > 1 and kappa > 1:
   - some mu* with 0 <= mu* <= 1 / (sqrt 2 a0) and
     condition_kappa_dual C kappa mu* = condition_kappa_alpha C kappa
     (mu* = (C - 1) m(u) / (1 + c), the mean of p);
   - if kappa <= 3 (c <= 0), condition_kappa_dual C kappa mu <=
     condition_kappa_alpha C kappa for every real mu;
   - if 3 <= kappa (c >= 0), condition_kappa_alpha C kappa <=
     condition_kappa_dual C kappa mu for every real mu.
   So alpha(C, kappa) is the maximum of the dual over mu for c < 0 and its
   minimum for c > 0; at c = 0 the dual does not depend on mu. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* The dual function of interface I2: with c = (kappa - 3) / 2,
   1/2 + c (1 + c) mu^2 - inf_(t >= 0) (v(-t - c mu) + v(C t + c mu)). *)
Definition condition_kappa_dual (C kappa mu : R) :=
  2%:R^-1 + (kappa - 3%:R) / 2%:R * (1 + (kappa - 3%:R) / 2%:R) * mu ^+ 2
  - inf [set universality_s (- t - (kappa - 3%:R) / 2%:R * mu)%R
             + universality_s (C * t + (kappa - 3%:R) / 2%:R * mu)%R
         | t in [set t : R | 0 <= t]].
