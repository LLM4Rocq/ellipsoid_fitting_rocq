From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean topology normedtype sequences.
From GaussianApplications Require Import
  SatVarianceDefinitions SatThresholdDefinitions SatThresholdStatement.
From GaussianApplications.RandomSAT Require Import Threshold.

(**md**************************************************************************)
(* # The satisfiability threshold of random k-SAT: the theorem                *)
(*                                                                            *)
(* Target T9 of phase 13. sat_threshold_theorem proves                        *)
(* sat_threshold_statement of SatThresholdStatement.v with alpha = sat_alpha  *)
(* k, the limit of the centers E V_n / n of Tails.v, which lies between       *)
(* sat_a0 k = 1 / (8 e^2 k) and 2^k + 1 (sat_alpha_ge, sat_alpha_le). The     *)
(* limits are sat_subcritical and sat_supercritical of RandomSAT/Threshold.v; *)
(* the headers of the files of RandomSAT describe the proof.                  *)
(*                                                                            *)
(* A Rocq formalization of the credited argument of the main theorem (Theorem *)
(* thm:main) of 'A Limiting Satisfiability Threshold for Every Fixed Clause   *)
(* Size' (family 235 of the OpenAI math collection, revision 1581d4cbd,       *)
(* source/sections/introduction.tex), along the route of the Lean development *)
(* of the collection, in lean/OAI/Probability/RandomSAT:                      *)
(* Lean: main (Main.lean, line 122)                                           *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Theorem sat_threshold_theorem : sat_threshold_statement.
Proof.
move=> R k k3; exists (sat_alpha k); split; first exact: sat_alpha_gt0.
by split=> c; [exact: sat_subcritical | exact: sat_supercritical].
Qed.
