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
(* Main results, for lambda, beta, gamma >= 0 and B >= 0 on D:                *)
(* - ls_objective_ge0: F_Z(theta, b; beta) >= 0.                              *)
(* - ls_barrier_value_le, ls_barrier_value_ge0: Phi_Z(D, B; beta, gamma) is   *)
(*   at most F_Z(theta, b; beta) + gamma B theta for every theta in D and     *)
(*   every real b, and it is nonnegative.                                     *)
(* - ls_value_barrierE: Phi_Z(D; beta) is the value with a barrier of weight  *)
(*   0; ls_value_le and ls_value_ge0 are the same bounds for it.              *)
(* - ls_barrier_value_mono, ls_value_mono: the values are nondecreasing in    *)
(*   beta.                                                                    *)
(* Over an empty D both values are 0 (ls_barrier_value_empty).                *)
(*                                                                            *)
(* Elsewhere in the library. The values are measurable functions of the       *)
(* n-tuple Z when D is nonempty, convex and relatively open and B >= 0 is     *)
(* continuous on D (measurable_ls_barrier_value in barrier_lindeberg.v,       *)
(* measurable_ls_value in ridge_comparison.v), and so is the minimizer        *)
(* (measurable_ls_min, probability/measurable_minimizer.v). For a regular     *)
(* feature, the fourth moments of the linear forms are finite and every       *)
(* measurable g with |g z| <= a + b |z|^4 is integrable (reg_int4,            *)
(* reg_integrable in feature_moments.v); under the hypotheses of Theorem 2.9, *)
(* Phi_Z(D, B; beta, gamma) is integrable for n independent regular features  *)
(* (int_Phi, barrier_lindeberg.v). Gaussian features are regular              *)
(* (gauss_regular_feature, gauss_feature.v).                                  *)
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

Section least_squares_values.
Context {R : realType} {N : nat}.
Implicit Types (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).

Lemma ls_objective_ge0 n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) th b :
  0 <= lambda -> 0 <= beta -> 0 <= ls_objective Z lambda beta th b.
Proof.
move=> l0 b0; rewrite /ls_objective; apply: addr_ge0.
  rewrite mulr_ge0 ?invr_ge0 ?mulrn_wge0 ?ler0n //.
  by rewrite sumr_ge0 // => j _; rewrite sqr_ge0.
by rewrite mulr_ge0 ?addr_ge0 ?sqr_ge0 ?mulr_ge0 ?mxdot_ge0.
Qed.

(* Phi_Z(D; beta) is the value with a barrier of weight 0. *)
Lemma ls_value_barrierE n (Z : n.-tuple 'rV[R]_N) (lambda beta : R)
    (D : set 'rV[R]_N) (B : 'rV[R]_N -> R) :
  ls_value Z lambda beta D = ls_barrier_value Z lambda beta D 0 B.
Proof.
rewrite /ls_value /ls_barrier_value; congr inf; apply/seteqP.
by split => _ [th Dth [b _ <-]]; exists th => //; exists b => //;
  rewrite mul0r addr0.
Qed.

Lemma ls_barrier_value_empty n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) D
    (gamma : R) B :
  ~ (D !=set0) -> ls_barrier_value Z lambda beta D gamma B = 0.
Proof.
move=> D0; rewrite /ls_barrier_value -[RHS]inf0; congr inf.
apply/seteqP; split; last exact: sub0set.
by move=> y [th Dth _]; apply: D0; exists th.
Qed.

Lemma ls_barrier_value_le n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) D
    (gamma : R) B th b :
  0 <= lambda -> 0 <= beta -> 0 <= gamma -> (forall z, D z -> 0 <= B z) ->
  D th ->
  ls_barrier_value Z lambda beta D gamma B <=
    ls_objective Z lambda beta th b + gamma * B th.
Proof.
move=> l0 b0 g0 B0 Dth; rewrite /ls_barrier_value.
have lb : has_lbound [set ls_objective Z lambda beta th' b' + gamma * B th' |
    th' in D & b' in [set: R]].
  exists 0 => _ [th' Dth' [b' _ <-]].
  by rewrite addr_ge0 ?ls_objective_ge0 // mulr_ge0 ?B0.
by apply: (ge_inf lb); exists th => //; exists b.
Qed.

Lemma ls_barrier_value_ge0 n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) D
    (gamma : R) B :
  0 <= lambda -> 0 <= beta -> 0 <= gamma -> (forall z, D z -> 0 <= B z) ->
  0 <= ls_barrier_value Z lambda beta D gamma B.
Proof.
move=> l0 b0 g0 B0.
have [[th Dth]|D0] := pselect (D !=set0); last first.
  by rewrite ls_barrier_value_empty // lexx.
rewrite /ls_barrier_value; apply: lb_le_inf.
  exists (ls_objective Z lambda beta th 0 + gamma * B th), th => //.
  by exists 0.
move=> _ [th' Dth' [b' _ <-]].
by rewrite addr_ge0 ?ls_objective_ge0 // mulr_ge0 ?B0.
Qed.

Lemma ls_barrier_value_mono n (Z : n.-tuple 'rV[R]_N) (lambda beta beta' : R)
    D (gamma : R) B :
  0 <= lambda -> 0 <= beta -> beta <= beta' -> 0 <= gamma ->
  (forall z, D z -> 0 <= B z) ->
  ls_barrier_value Z lambda beta D gamma B <=
    ls_barrier_value Z lambda beta' D gamma B.
Proof.
move=> l0 b0 bb g0 B0.
have [[th Dth]|D0] := pselect (D !=set0); last first.
  by rewrite !ls_barrier_value_empty // lexx.
have Fle th' b' :
    ls_objective Z lambda beta th' b' <= ls_objective Z lambda beta' th' b'.
  have q0 : 0 <= lambda * mxdot th' th' + b' ^+ 2.
    by rewrite addr_ge0 ?sqr_ge0 // mulr_ge0 // mxdot_ge0.
  by rewrite /ls_objective lerD2l (ler_wpM2r q0 bb).
have lb : has_lbound [set ls_objective Z lambda beta th' b' + gamma * B th' |
    th' in D & b' in [set: R]].
  exists 0 => _ [th' Dth' [b' _ <-]].
  by rewrite addr_ge0 ?ls_objective_ge0 // mulr_ge0 ?B0.
rewrite /ls_barrier_value; apply: lb_le_inf.
  exists (ls_objective Z lambda beta' th 0 + gamma * B th), th => //.
  by exists 0.
move=> _ [th' Dth' [b' _ <-]].
apply: le_trans (ge_inf lb _) _; first by exists th' => //; exists b'.
by rewrite lerD2r Fle.
Qed.

Lemma ls_value_le n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) D th b :
  0 <= lambda -> 0 <= beta -> D th ->
  ls_value Z lambda beta D <= ls_objective Z lambda beta th b.
Proof.
pose B0f : 'rV[R]_N -> R := fun=> 0.
move=> l0 b0 Dth; rewrite (ls_value_barrierE Z lambda beta D B0f).
have z0 : (0 : R) <= 0 := lexx 0.
have B0 z : D z -> 0 <= B0f z by move=> _; exact: lexx.
by have := ls_barrier_value_le Z b l0 b0 z0 B0 Dth; rewrite mul0r addr0.
Qed.

Lemma ls_value_ge0 n (Z : n.-tuple 'rV[R]_N) (lambda beta : R) D :
  0 <= lambda -> 0 <= beta -> 0 <= ls_value Z lambda beta D.
Proof.
pose B0f : 'rV[R]_N -> R := fun=> 0.
move=> l0 b0; rewrite (ls_value_barrierE Z lambda beta D B0f).
have z0 : (0 : R) <= 0 := lexx 0.
have B0 z : D z -> 0 <= B0f z by move=> _; exact: lexx.
by apply: ls_barrier_value_ge0.
Qed.

Lemma ls_value_mono n (Z : n.-tuple 'rV[R]_N) (lambda beta beta' : R) D :
  0 <= lambda -> 0 <= beta -> beta <= beta' ->
  ls_value Z lambda beta D <= ls_value Z lambda beta' D.
Proof.
pose B0f : 'rV[R]_N -> R := fun=> 0.
move=> l0 b0 bb.
rewrite (ls_value_barrierE Z lambda beta D B0f).
rewrite (ls_value_barrierE Z lambda beta' D B0f).
have z0 : (0 : R) <= 0 := lexx 0.
have B0 z : D z -> 0 <= B0f z by move=> _; exact: lexx.
by apply: ls_barrier_value_mono.
Qed.

End least_squares_values.

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
