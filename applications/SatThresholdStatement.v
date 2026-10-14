From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean topology normedtype sequences.
From GaussianApplications Require Import
  SatVarianceDefinitions SatThresholdDefinitions.

(**md**************************************************************************)
(* # The satisfiability threshold of random k-SAT: the statement              *)
(*                                                                            *)
(* Target T9 of phase 13 (AGENTS.md, section Phase 13; the plan               *)
(* notes/phase13-plan.md, section 2). The statement of a Rocq formalization   *)
(* of the credited argument of the main theorem (Theorem thm:main) of 'A      *)
(* Limiting Satisfiability Threshold for Every Fixed Clause Size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/introduction.tex). This file holds the statement only; its *)
(* definition sat_prob is in SatThresholdDefinitions.v, over the frozen       *)
(* definitions of SatVarianceDefinitions.v. The Lean counterpart, in          *)
(* lean/OAI/Probability/RandomSAT of the collection:                          *)
(* Lean: HasLimitingThreshold (Model.lean, line 38)                           *)
(* Lean: main (Main.lean, line 122)                                           *)
(*                                                                            *)
(* sat_threshold_statement: for every realType R and every k >= 3 there is    *)
(* alpha > 0 such that P_n(floor(c n)) tends to 1 as n tends to infinity for  *)
(* every 0 <= c < alpha, and tends to 0 for every c > alpha. P_n(m) =         *)
(* sat_prob R n k m.                                                          *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - No assertion is made at c = alpha, as in the manuscript and in the Lean  *)
(*   statement.                                                               *)
(* - floor(c n) is Num.truncn (c * n%:R); Num.truncn x is the largest natural *)
(*   number at most x for x >= 0, as the Lean floor of natural numbers.       *)
(* - The limits are MathComp-Analysis's convergence of sequences in R, for    *)
(*   the topology of R (numFieldTopology).                                    *)
(* - alpha may depend on k and, formally, on R, as the constant of T7 does;   *)
(*   the manuscript's alpha_k depends on k only. The quantifiers are those of *)
(*   the Lean statement.                                                      *)
(* - k = 1 and k = 2 are excluded, as in the manuscript.                      *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition sat_threshold_statement : Prop :=
  forall (R : realType) (k : nat), (3 <= k)%N ->
  exists alpha : R, 0 < alpha /\
  (forall c : R, 0 <= c -> c < alpha ->
     sat_prob R n k (Num.truncn (c * n%:R)) @[n --> \oo] --> (1 : R)) /\
  (forall c : R, alpha < c ->
     sat_prob R n k (Num.truncn (c * n%:R)) @[n --> \oo] --> (0 : R)).
