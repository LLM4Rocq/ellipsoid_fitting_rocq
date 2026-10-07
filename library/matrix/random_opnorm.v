From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm nets.
From GaussianAnalysis.probability Require Import lindeberg symmetrization.

(**md**************************************************************************)
(* # The operator norm of a sum of independent random symmetric matrices      *)
(*                                                                            *)
(* A bound by nets and a scalar Bernstein inequality, used for Lemma 4.3 of   *)
(* Koehler and Sohn (arXiv 2608.27372, lines 4604-4615) in place of the       *)
(* matrix Bernstein inequality that the paper cites.                          *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs):    *)
(* - For Z symmetric and S positive semidefinite, |<Z, S>| <= opnorm Z tr S,  *)
(*   where <., .> is the Frobenius product; so on the positive semidefinite   *)
(*   matrices of trace at most tau, the linear forms S |-> <Z, S> are         *)
(*   bounded by tau opnorm Z.                                                 *)
(* - Let Z_1, ..., Z_n be independent random symmetric d x d matrices         *)
(*   (tuple_prod of laws on 'M[R]_d) such that for every v with |v| <= 1 the  *)
(*   variable v^T Z_k v is centered and subexponential with constant L:       *)
(*   E exp (|v^T Z_k v| / L) <= 2. Then                                       *)
(*     E opnorm (Z_1 + ... + Z_n) <= C L (sqrt (n d) + d)                     *)
(*   with an absolute constant C. Proof: opnorm_net_sym on a 1/4-net of the   *)
(*   unit ball with at most (18 e)^d points (unit_ball_net), Bernstein's      *)
(*   inequality for each point of the net (lane A, probability/), a union     *)
(*   bound and the integration of the tail.                                   *)
(* - The same bound for the Rademacher sums                                   *)
(*   E rademacher_mean (opnorm (eps_1 Z_1 + ... + eps_n Z_n)), since each     *)
(*   eps_k Z_k satisfies the same hypothesis.                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
