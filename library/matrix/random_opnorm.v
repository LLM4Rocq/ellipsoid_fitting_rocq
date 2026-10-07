From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm nets.
From GaussianAnalysis.probability Require Import lindeberg symmetrization.

(**md**************************************************************************)
(* # The operator norm of a sum of independent random matrices                *)
(*                                                                            *)
(* A bound by nets and the moment generating function of sums of independent  *)
(* subexponential variables, used for Lemma 4.3 of Koehler and Sohn (arXiv    *)
(* 2608.27372, lines 4604-4615) in place of the matrix Bernstein inequality   *)
(* that the paper cites; it gives the bound without the logarithmic factor.   *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs):    *)
(* - For S positive semidefinite and any square A,                            *)
(*   |<A, S>| <= opnorm ((A + A^T) / 2) tr S, where <., .> is the Frobenius   *)
(*   product.                                                                 *)
(* - A maximal inequality: for finitely many random variables Y_v and         *)
(*   l > 0, E max_v |Y_v| <= (ln (2 N) + ln M) / l if N is their number and   *)
(*   E exp (l Y_v) and E exp (- l Y_v) are at most M (from e^y >= 1 + y).     *)
(* - Let x have law tuple_prod mu n and let Y : T -> 'M[R]_d be measurable,   *)
(*   such that for every v with |v| <= 1 and every k the variable             *)
(*   v^T Y v is centered and subexponential with constant L under mu k:       *)
(*   E exp (|v^T Y v| / L) <= 2. Then, for every sign vector s,               *)
(*     E opnorm (sym (sum_k s_k Y(x_k))) <= C L (sqrt (n d) + d)              *)
(*   with an absolute constant C. Proof: opnorm_net_sym on a 1/4-net of the   *)
(*   unit ball with at most (18 e)^d points (net_exists), the moment          *)
(*   generating function of the sum (subexponential_sum_mgf of                *)
(*   subgaussian.v) at each point of the net, and the maximal inequality.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
