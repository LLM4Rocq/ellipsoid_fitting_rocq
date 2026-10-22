From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From GaussianApplications Require Import PsdRankStatement PsdLiftStatement.
From GaussianApplications Require Import PsdRankTheorem.
From GaussianApplications.PsdRank Require Import Lift.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the corollary on exact lifts      *)
(*                                                                            *)
(* Item A7 of phase 14 (AGENTS.md, section Phase 14; the plan                 *)
(* notes/phase14-plan.md, T14). psd_lift_theorem proves psd_lift_statement of *)
(* PsdLiftStatement.v, the corollary 'Unshifted rank and exact lifts' of      *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/introduction.tex, lines 74-114), a Rocq formalization of   *)
(* the credited argument: psd_lift_from_rank of PsdRank/Lift.v applied to     *)
(* psd_rank_theorem of PsdRankTheorem.v. The file follows no Lean module.     *)
(******************************************************************************)

Theorem psd_lift_theorem : psd_lift_statement.
Proof. exact: psd_lift_from_rank psd_rank_theorem. Qed.
