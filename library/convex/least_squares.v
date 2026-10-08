From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.

(**md**************************************************************************)
(* # Constrained least squares with features, and regular features            *)
(*                                                                            *)
(* The objects of the Lindeberg argument of Koehler and Sohn (Universality    *)
(* and sharp thresholds for ellipsoid fitting, arXiv 2608.27372, section      *)
(* 2.2): n features Z_1, ..., Z_n in 'rV[R]_N, the ridge-regularized least    *)
(* squares objective in (theta, b), its infimum over theta in a convex set D  *)
(* with an optional barrier B, and the regular features of their Definition   *)
(* 2.5. Features are n-tuples, so that their law is tuple_prod of             *)
(* probability/lindeberg.v; <x, y> is mxdot x y and |x|^2 is mxdot x x.       *)
(*                                                                            *)
(* ```                                                                        *)
(* ls_objective Z lambda beta theta b == F_Z(theta, b; beta), the average     *)
(*                     (2 n)^-1 sum_i (b - <Z_i, theta>)^2 plus the ridge     *)
(*                     term beta (lambda |theta|^2 + b^2)                     *)
(* ls_loss Z P theta b == sum_(i in P) (b - <Z_i, theta>)^2                   *)
(* ls_ridge Z P s lambda beta theta b == s ls_loss Z P theta b                *)
(*                     + beta (lambda |theta|^2 + b^2)                        *)
(* ls_barrier_objective Z P s lambda beta gamma B theta b ==                  *)
(*                     ls_ridge Z P s lambda beta theta b + gamma B theta;    *)
(*                     with P the indices other than i and s = (2 n)^-1, the  *)
(*                     leave-one-out objective F^(i) of the paper             *)
(* ls_barrier_value Z lambda beta D gamma B == Phi_Z(D, B; beta, gamma), the  *)
(*                     infimum of F_Z(theta, b; beta) + gamma B theta over    *)
(*                     theta in D and b real                                  *)
(* ls_value Z lambda beta D == Phi_Z(D; beta), the infimum of                 *)
(*                     F_Z(theta, b; beta) over theta in D and b real;        *)
(*                     Phi_Z(D) is ls_value Z lambda 0 D, for any lambda      *)
(* regular_feature K tau Sigma mu == the law mu on 'rV[R]_N is a              *)
(*                     (K, tau)-regular feature with covariance Sigma:        *)
(*                     lambda = opnorm Sigma > 0, (F1)                        *)
(*                     E <Z, theta>^4 <= K^4 lambda^2 |theta|^4, mean 0,      *)
(*                     E <Z, theta> <Z, theta'> = theta Sigma theta'^T and    *)
(*                     (F2) Var (Z T Z^T) <= tau^2 |T|_F^2 for T symmetric    *)
(* ```                                                                        *)
(*                                                                            *)
(* The paper's lambda is the operator norm opnorm Sigma; the definitions take *)
(* it as a parameter, so that they do not depend on a law.                    *)
(*                                                                            *)
(* Planned results (stage 1 of phase 5):                                      *)
(* - The values are nonnegative when B >= 0 on D, and at most                 *)
(*   F_Z(theta, b; beta) + gamma B theta for every theta in D and b;          *)
(*   ls_barrier_value with gamma = 0 is ls_value, and ls_value is             *)
(*   nondecreasing in beta.                                                   *)
(* - Z |-> Phi_Z(D, B; beta, gamma) and Z |-> Phi_Z(D; beta) are measurable   *)
(*   functions of the n-tuple Z (they are upper semicontinuous), for every D, *)
(*   B >= 0 continuous on D, and beta, gamma >= 0.                            *)
(* - A regular feature has finite fourth moments of its linear forms, so      *)
(*   that Z |-> F_Z(theta, b; beta) and Z |-> Phi_Z are integrable for the    *)
(*   law of n independent copies.                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section least_squares.
Context {R : realType} {N : nat}.
Implicit Types (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).

Definition ls_objective n (Z : n.-tuple 'rV[R]_N) (lambda beta : R)
    (theta : 'rV[R]_N) (b : R) : R :=
  (n%:R *+ 2)^-1 * \sum_(i < n) (b - mxdot (tnth Z i) theta) ^+ 2 +
  beta * (lambda * mxdot theta theta + b ^+ 2).

Definition ls_loss n (Z : n.-tuple 'rV[R]_N) (P : pred 'I_n)
    (theta : 'rV[R]_N) (b : R) : R :=
  \sum_(i < n | P i) (b - mxdot (tnth Z i) theta) ^+ 2.

Definition ls_ridge n (Z : n.-tuple 'rV[R]_N) (P : pred 'I_n)
    (s lambda beta : R) (theta : 'rV[R]_N) (b : R) : R :=
  s * ls_loss Z P theta b + beta * (lambda * mxdot theta theta + b ^+ 2).

Definition ls_barrier_objective n (Z : n.-tuple 'rV[R]_N) (P : pred 'I_n)
    (s lambda beta gamma : R) B (theta : 'rV[R]_N) (b : R) : R :=
  ls_ridge Z P s lambda beta theta b + gamma * B theta.

Definition ls_barrier_value n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) D
    (gamma : R) B : R :=
  inf [set ls_objective Z lambda beta theta b + gamma * B theta |
       theta in D & b in [set: R]].

Definition ls_value n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) D : R :=
  inf [set ls_objective Z lambda beta theta b | theta in D & b in [set: R]].

End least_squares.

Section regular_feature.
Context {R : realType} {N : nat}.
Local Open Scope ereal_scope.

Definition regular_feature (K tau : R) (Sigma : 'M[R]_N)
    (mu : probability 'rV[R]_N R) : Prop :=
  [/\ (0 < opnorm Sigma)%R,
      forall theta : 'rV[R]_N,
        'E_mu[fun z => (mxdot z theta ^+ 4)%R] <=
          (K ^+ 4 * opnorm Sigma ^+ 2 * mxdot theta theta ^+ 2)%:E,
      forall theta : 'rV[R]_N, 'E_mu[fun z => mxdot z theta] = 0,
      forall theta theta' : 'rV[R]_N,
        'E_mu[fun z => (mxdot z theta * mxdot z theta')%R] =
          (mxdot (theta *m Sigma) theta')%:E &
      forall T : 'M[R]_N, T \is symmetricmx ->
        'V_mu[fun z => mxdot z (z *m T)] <= (tau ^+ 2 * frobenius T ^+ 2)%:E].

End regular_feature.
