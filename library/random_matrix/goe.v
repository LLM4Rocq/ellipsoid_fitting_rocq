From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals ereal.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.

(**md**************************************************************************)
(* # The Gaussian orthogonal ensemble                                         *)
(*                                                                            *)
(* For a of law gauss (d * d), goe_mx a is the symmetric matrix W = (A + A^T) *)
(* / sqrt (2 d) with A = vec_mx a: the entries W_ij, i <= j, are independent  *)
(* centered normal with variance 1 / d off the diagonal and 2 / d on it. This *)
(* normalization has the semicircle law of radius 2 (semicircle_prob 2 of     *)
(* probability/semicircle_law.v) as limit of its spectrum. The Gaussian       *)
(* features of Koehler and Sohn at kappa = 3 (arXiv 2608.27372, lines         *)
(* 1004-1086) have the same law up to mxvec. This file is part of item G7 of  *)
(* phase 5.                                                                   *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - Gaussian integration by parts for W: E[W_ij F (W)] = (1 / d) E[d_ij F    *)
(*   (W) + d_ji F (W)] for F of class C^1 with derivatives of polynomial      *)
(*   growth (from gauss_ibp).                                                 *)
(* - The Schwinger-Dyson equation for the moments t_k = \tr (W^k) / d: E      *)
(*   t_(k+1) = (k / d) E t_(k-1) + \sum_(r < k) E[t_r t_(k-1-r)].             *)
(* - Var t_k = O(1 / d^2), by the Gaussian Poincare inequality.               *)
(* - E t_k tends to the k-th moment of semicircle_prob 2 (a Catalan number    *)
(*   for k even, 0 for k odd).                                                *)
(* - A crude bound on the operator norm: the probability that opnorm W >= 3   *)
(*   is at most exp (- c d) for some c > 0 (gauss_opnorm_tail of              *)
(*   comparison/escape.v).                                                    *)
(*                                                                            *)
(* ```                                                                        *)
(* goe_mx a == the GOE matrix (A + A^T) / sqrt (2 d) of a row vector a of     *)
(*             size d * d, A = vec_mx a                                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section goe.
Context {R : realType}.

(* The GOE matrix (A + A^T) / sqrt (2 d) of a row vector of size d * d. *)
Definition goe_mx d (a : 'rV[R]_(d * d)) : 'M[R]_d :=
  (Num.sqrt (2 * d%:R))^-1 *: (vec_mx a + (vec_mx a)^T).

Lemma goe_mx_sym d (a : 'rV[R]_(d * d)) : (goe_mx a)^T = goe_mx a.
Proof. by rewrite /goe_mx linearZ /= linearD /= trmxK addrC. Qed.

End goe.
