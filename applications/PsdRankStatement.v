From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From GaussianAnalysis.matrix Require Import psd_factorization.
From GaussianApplications Require Import PsdRankDefinitions.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the statement                     *)
(*                                                                            *)
(* The PSD main statement of phase 13 (AGENTS.md, section Phase 13, batch 3;  *)
(* the plan notes/phase13-plan.md, section 2), proved in phase 14. The        *)
(* statement of a Rocq formalization of the credited argument of the main     *)
(* theorem (Theorem thm:main) of 'Exponential PSD rank of positively shifted  *)
(* matching matrices' (family 126 of the OpenAI math collection, revision     *)
(* 1581d4cbd, source/sections/introduction.tex, lines 25-44). This file holds *)
(* the statement only; its definitions are in PsdRankDefinitions.v, and       *)
(* psd_factorization is in library/matrix/psd_factorization.v.                *)
(*                                                                            *)
(* psd_rank_statement: for every realType R there is a positive integer K     *)
(* such that, for every 0 < rho < 1, there is n0 such that every real PSD     *)
(* factorization of A_n(rho), for every even n >= n0, has a size r with 2^n   *)
(* <= r^K, that is r >= 2^(n/K). A real PSD factorization of size r is a      *)
(* family of positive semidefinite F U and G M in 'M[R]_r with A_n(rho)_(U,M) *)
(* = tr (F U G M) for every odd set U and every perfect matching M.           *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - No minimum is defined: the bound applies to every factorization, hence   *)
(*   to the least size, the manuscript's PSD rank.                            *)
(* - 2^n <= r^K is the manuscript's rank >= 2^(c n) with c = 1/K, in natural  *)
(*   numbers: from rank >= 2^(c n) and an integer K >= 1/c, r^K >= 2^(c K n)  *)
(*   >= 2^n.                                                                  *)
(* - K comes after R and before rho, as the user decided (D7): it is uniform  *)
(*   in rho, as the manuscript's c, and may depend formally on R. n0 depends  *)
(*   on rho, and formally on R and K.                                         *)
(* - rho = 1 is excluded, as in the manuscript: A_n(1) has a PSD              *)
(*   factorization of size 'C(n, 2) (PsdRank/Model.v,                         *)
(*   shifted_matching_one_factorization). rho = 0 is excluded too, as in the  *)
(*   manuscript's theorem.                                                    *)
(* - The size r = 0 needs no exclusion: for n >= 2 even, the entries are at   *)
(*   least rho > 0 (PsdRank/Model.v, shifted_matching_mx_ge), so a            *)
(*   factorization has a positive size once A_n(rho) has an entry.            *)
(* - The Lean development of the collection proves another claim: the least   *)
(*   size of a factorization of the unshifted slack matrix of the perfect     *)
(*   matching polytope, with edge rows, grows faster than every power of n.   *)
(* Lean: MainClaim (Model.lean, line 46)                                      *)
(* Lean: main (Main.lean, line 53)                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition psd_rank_statement : Prop :=
  forall R : realType, exists K : nat, (0 < K)%N /\
  forall rho : R, 0 < rho < 1 ->
  exists n0 : nat, forall n : nat, ~~ odd n -> (n0 <= n)%N ->
  forall r : nat, psd_factorization (@shifted_matching_mx n R rho) r ->
  (2 ^ n <= r ^ K)%N.
