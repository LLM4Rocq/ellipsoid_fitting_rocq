From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun exp.
From GaussianAnalysis Require Import euclidean self_concordant least_squares.

(**md**************************************************************************)
(* # Removing the barrier                                                     *)
(*                                                                            *)
(* Lemma 2.11 of Koehler and Sohn (arXiv 2608.27372, lines 1386-1441): the    *)
(* cost of a theta-self-concordant barrier B >= 0 in the least squares value  *)
(* is controlled by the contraction toward a reference point.                 *)
(*                                                                            *)
(* Planned results (stage 1 of phase 5), for D relatively open and convex     *)
(* with directions V, B >= 0 a theta-self-concordant barrier on D, a          *)
(* reference point (theta_ref, b_ref) with theta_ref in D, beta >= 0,         *)
(* gamma > 0 and 0 < eps < 1, and every n-tuple of features Z:                *)
(* - Lemma 2.11:                                                              *)
(*   0 <= Phi_Z(D, B; beta, gamma) - Phi_Z(D; beta)                           *)
(*     <= eps F_Z(theta_ref, b_ref; beta) + gamma B theta_ref                 *)
(*        + gamma theta ln (1 / eps).                                         *)
(* - (2.15): for two tuples W and G,                                          *)
(*   |Phi_W(D; beta) - Phi_G(D; beta)|                                        *)
(*     <= |Phi_W(D, B; beta, gamma) - Phi_G(D, B; beta, gamma)|               *)
(*        + eps (F_W + F_G)(theta_ref, b_ref; beta) + 2 gamma B theta_ref     *)
(*        + 2 gamma theta ln (1 / eps).                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
