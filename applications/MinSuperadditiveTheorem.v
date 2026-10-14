From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import topology normedtype sequences exp.
From GaussianAnalysis.analysis Require Import min_superadditive.
From GaussianApplications Require Import MinSuperadditiveStatement.

(**md**************************************************************************)
(* # Convergence from approximate minimum inequalities: the theorem           *)
(*                                                                            *)
(* Target T12 of phase 13 (AGENTS.md, section Phase 13):                      *)
(* min_superadditive_theorem proves min_superadditive_statement of            *)
(* MinSuperadditiveStatement.v, from the library file                         *)
(* analysis/min_superadditive.v: the finite-size bound is                     *)
(* min_superadditive_tail, the convergence min_superadditive_cvgn and the     *)
(* bound of the limit min_superadditive_lim_ge, with the bound of the         *)
(* statement, written out, turned into bounded_fun. A Rocq formalization of   *)
(* the credited argument of the lemma 'Balanced comparisons' of 'A Limiting   *)
(* Satisfiability Threshold for Every Fixed Clause Size' (family 235 of the   *)
(* OpenAI math collection, revision 1581d4cbd,                                *)
(* source/sections/convergence.tex), along the strong induction of the Lean   *)
(* development of the collection, in lean/OAI/Probability/RandomSAT:          *)
(* Lean: summable_min_convergence (Convergence.lean, line 141)                *)
(******************************************************************************)

Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Theorem min_superadditive_theorem : min_superadditive_statement.
Proof.
move=> R u A beta N A0 b0 hsum hnext E.
split=> [s n Ns s2 ssn|[M hM]].
  exact: (min_superadditive_tail A0 b0 hsum hnext Ns s2 ssn).
have bu : bounded_fun u.
  exists M; split; first by rewrite num_real.
  by move=> M' MM' n _ /=; apply: le_trans (hM n) (ltW MM').
split; first exact: (min_superadditive_cvgn A0 b0 hsum hnext bu).
by move=> s Ns s2; exact: (min_superadditive_lim_ge A0 b0 hsum hnext bu Ns s2).
Qed.
