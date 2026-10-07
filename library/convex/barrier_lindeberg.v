From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype derive realfun exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.
From GaussianAnalysis Require Import lindeberg self_concordant least_squares.
From GaussianAnalysis Require Import minimizers.

(**md**************************************************************************)
(* # Universality of barrier-regularized least squares                        *)
(*                                                                            *)
(* Theorem 2.9 of Koehler and Sohn (arXiv 2608.27372, lines 1282-1344, proof  *)
(* lines 1637-2116 and 3809-4225), in the paper's abstract feature form, for  *)
(* two laws of features with the same covariance: replacing n independent    *)
(* features of law mu by n independent features of law nu changes the        *)
(* expectation of the barrier-regularized least squares value                 *)
(* Phi_Z(D, B; beta, gamma) (ls_barrier_value) by little, and both values     *)
(* concentrate. The Gaussian case of the paper is the corollary for nu the    *)
(* centered Gaussian law with covariance Sigma, which is a regular feature.   *)
(*                                                                            *)
(* Planned results (stage 1 of phase 5). Below, mu and nu are                 *)
(* (K, tau)-regular features on 'rV[R]_N with the same covariance Sigma,      *)
(* lambda = opnorm Sigma, D is nonempty, convex and relatively open with      *)
(* directions V, B >= 0 is a self-concordant function on D, beta and          *)
(* gamma > 0, W and G have laws tuple_prod (fun=> mu) n and                   *)
(* tuple_prod (fun=> nu) n, and                                               *)
(*   Lref = (1 + 1/beta) (1 + inf_{theta in D} (lambda |theta|^2              *)
(*          + gamma B theta)).                                                *)
(* - The telescoping of lindeberg_replacement (probability/lindeberg.v) for   *)
(*   an integrable functional F and per-coordinate bounds b_i that depend on  *)
(*   the other coordinates: |E_mu F - E_nu F| <= sum_i E_{hybrid i} b_i,      *)
(*   where hybrid i has the law mu for the coordinates < i and nu for those   *)
(*   > i.                                                                     *)
(* - Proposition 2.14, (2.21)-(2.22): with S the size                         *)
(*   lambda |theta^(i)|^2 + (b^(i))^2 of the leave-one-out minimizer,         *)
(*   beta S <= (2 n)^-1 sum_{j <> i} <Z_j, theta_ref>^2                       *)
(*             + beta lambda |theta_ref|^2 + gamma B theta_ref,               *)
(*   and E_i r_i(Z_i)^4 <= C S^2.                                             *)
(* - Lemma 4.1: the Hessian H^(i) is at least                                 *)
(*   2 beta (lambda |u|^2 + u_b^2) + gamma D^2 B[u, u]; the blocks of its     *)
(*   inverse are bounded by C / (beta lambda), C / (beta sqrt lambda) and     *)
(*   C / beta.                                                                *)
(* - Lemma 4.2: for n gamma >= n0 and |r_i(z)| <= (n gamma)^(1/4), the exact  *)
(*   and the quadratic insertion updates have local norm at most              *)
(*   C r_i(z)^2 / (n gamma), the quadratic update is feasible, and the        *)
(*   Taylor remainder is at most C gamma^(-1/2) n^(-3/2) |r_i(z)|^3.          *)
(* - Proposition 2.14, (2.23): for n gamma >= n0,                             *)
(*   E_i |Delta_i(Z_i) - r_i(Z_i)^2 / (2 (n + l_i(Z_i)))|                     *)
(*     <= C gamma^(-1/2) n^(-3/2) (1 + S^2).                                  *)
(* - Proposition 2.16: E_i l_i(Z_i) is the same for mu and nu, and            *)
(*   E_i |l_i(Z_i) - E_i l_i|^2 <= C beta^-2 (dim V) (tau / lambda + 1)^2.    *)
(* - Theorem 2.9, (2.12): there are C and n0, depending only on K, such that  *)
(*   if n gamma >= n0, then                                                   *)
(*   |E Phi_W(D, B; beta, gamma) - E Phi_G(D, B; beta, gamma)|                *)
(*     <= C Lref^2 ((n gamma)^(-1/2) + sqrt (dim V) (tau / lambda + 1) / n).  *)
(* - Theorem 2.9, (2.13): Var Phi_W + Var Phi_G <= C Lref^2 / n, by           *)
(*   Efron-Stein for tuple_prod.                                              *)
(* - Theorem 2.9, (2.14): for t > 0, Phi_W and Phi_G are each within          *)
(*   C Lref^2 ((n gamma)^(-1/2) + sqrt (dim V) (tau / lambda + 1) / n) + t    *)
(*   of E Phi_G, except on events of probability at most C Lref^2 / (n t^2)   *)
(*   (Chebyshev).                                                             *)
(* - (2.10): for S : 'M[R]_(k, N) with S != 0, the law of x *m S with x of    *)
(*   law gauss k is a (3^(1/4), sqrt 2 opnorm (S^T S))-regular feature with   *)
(*   covariance S^T S; so Theorem 2.9 holds with nu the Gaussian law with     *)
(*   the covariance of mu, as the paper states it.                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
