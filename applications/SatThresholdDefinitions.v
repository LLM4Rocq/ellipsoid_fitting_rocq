From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From GaussianApplications Require Import SatVarianceDefinitions.

(**md**************************************************************************)
(* # The satisfiability threshold of random k-SAT: the definitions            *)
(*                                                                            *)
(* Target T9 of phase 13 (AGENTS.md, section Phase 13; the plan               *)
(* notes/phase13-plan.md, section 2). The definition of the statement of      *)
(* SatThresholdStatement.v, from 'A Limiting Satisfiability Threshold for     *)
(* Every Fixed Clause Size' (family 235 of the OpenAI math collection,        *)
(* revision 1581d4cbd, source/sections/introduction.tex). The clauses, their  *)
(* uniform law and the satisfiability of prefixes are those of                *)
(* SatVarianceDefinitions.v, frozen with target T7 of phase 12 at 0d5afba.    *)
(* The Lean counterpart, in lean/OAI/Probability/RandomSAT of the collection: *)
(* Lean: properSATProbability (Model.lean, line 33)                           *)
(*                                                                            *)
(* sat_prob R n k m is P_n(m) of the manuscript: the probability that m       *)
(* independent uniform proper signed k-clauses on n variables, drawn with     *)
(* replacement, are simultaneously satisfiable. It is the average, over all   *)
(* m-tuples of clauses (sat_mean), of the indicator that some assignment      *)
(* satisfies every clause of the tuple (prefix_sat t m, the prefix of length  *)
(* m being the whole tuple).                                                  *)
(*                                                                            *)
(* - For m = 0 it is 1: the empty formula is satisfiable.                     *)
(* - For n < k and m >= 1 there is no clause, hence no m-tuple of clauses,    *)
(*   and it is 0 by MathComp's convention 0^-1 = 0, as in the Lean model. The *)
(*   limits of the statement only see n >= k.                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*   sat_prob R n k m == P_n(m), the probability that m independent uniform   *)
(*                       proper signed k-clauses on n variables, drawn with   *)
(*                       replacement, are simultaneously satisfiable          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition sat_prob (R : realType) (n k m : nat) : R :=
  sat_mean (fun t : m.-tuple (clause n k) => (prefix_sat t m)%:R).
