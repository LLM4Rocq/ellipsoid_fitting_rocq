From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From GaussianAnalysis.matrix Require Import psd_factorization.
From GaussianApplications Require Import PsdRankDefinitions PsdLiftDefinitions.

(**md**************************************************************************)
(* # PSD rank of matching matrices: the statement of the corollary            *)
(*                                                                            *)
(* The corollary of phase 14 (AGENTS.md, section Phase 14, target T14, batch  *)
(* 1; the plan notes/phase14-plan.md, section 2). The statement of a Rocq     *)
(* formalization of the credited argument of the corollary 'Unshifted rank    *)
(* and exact lifts' (Corollary cor:exact-lift) of 'Exponential PSD rank of    *)
(* positively shifted matching matrices' (family 126 of the OpenAI math       *)
(* collection, revision 1581d4cbd, source/sections/introduction.tex, lines    *)
(* 74-114), proved in phase 14 from the main theorem (psd_rank_statement of   *)
(* PsdRankStatement.v). This file holds the statement only; its definitions   *)
(* are in PsdLiftDefinitions.v and PsdRankDefinitions.v, and                  *)
(* psd_factorization is in library/matrix/psd_factorization.v.                *)
(*                                                                            *)
(* psd_lift_statement: for every realType R there are a positive integer K    *)
(* and n0 such that, for every even n >= n0 and every r,                      *)
(* - every real PSD factorization of A_n(0) of size r,                        *)
(* - every real PSD factorization of T_n(0) of size r, and                    *)
(* - every exact semidefinite lift of size r of the perfect matching polytope *)
(* has 2^n <= r^K, that is r >= 2^(n/K).                                      *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - One statement, with one K and one n0 for the three claims, as the        *)
(*   manuscript's one pair of constants c0 and n1.                            *)
(* - K comes after R, as in psd_rank_statement (the user's decision D7): a    *)
(*   corollary of a statement with K after R can only claim, for every R, a   *)
(*   K. n0 comes after K and depends formally on R and K.                     *)
(* - 2^n <= r^K is the manuscript's rank >= 2^(c0 n) with c0 = 1/K, in        *)
(*   natural numbers, as in psd_rank_statement. As there, no minimum is       *)
(*   defined: the bound applies to every factorization and every lift, hence  *)
(*   to the least size, the manuscript's PSD rank and lift size.              *)
(* - A_n(0) is shifted_matching_mx at rho = 0. It has no positive shift, and  *)
(*   A_4(0) is the zero matrix; the bound is claimed for large n only.        *)
(* - The Lean development of the collection proves another claim for lifts:   *)
(*   the size of an affine lift grows faster than every power of n.           *)
(* Lean: affine_lift_lower_bound (AffineLift.lean, line 11)                   *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition psd_lift_statement : Prop :=
  forall R : realType, exists K : nat, (0 < K)%N /\
  exists n0 : nat, forall n : nat, ~~ odd n -> (n0 <= n)%N ->
  forall r : nat,
  [/\ psd_factorization (@shifted_matching_mx n R 0) r -> (2 ^ n <= r ^ K)%N,
      psd_factorization (@matching_slack_mx n R) r -> (2 ^ n <= r ^ K)%N &
      semidefinite_lift R n r -> (2 ^ n <= r ^ K)%N].
