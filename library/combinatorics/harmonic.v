From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals exp.

(**md**************************************************************************)
(* # A bound on the harmonic numbers                                          *)
(*                                                                            *)
(* The n-th harmonic number H_n = sum_(i < n) 1 / (i + 1) is at most 1 + ln n *)
(* for every n >= 1, over any realType.                                       *)
(*                                                                            *)
(* The general statement of this file is a compiled Prop definition, for      *)
(* review with batch 1 of phase 14 (AGENTS.md, section Phase 14, step 0,      *)
(* items 5 and 6). It will be proved by the lemma of the same name without    *)
(* the suffix _statement.                                                     *)
(*                                                                            *)
(* - harmonic_ln_statement R: for every n > 0, sum_(i < n) 1 / (i + 1) <= 1 + *)
(*   ln n in R. The proof will apply ln (1 + x) <= x (le_ln1Dx of exp.v) at x *)
(*   = -1 / (i + 1), which gives 1 / (i + 1) <= ln (i + 1) - ln i for i >= 1, *)
(*   and telescope.                                                           *)
(*                                                                            *)
(* This is a Rocq formalization of the harmonic bound that the trace estimate *)
(* of the lemma on local averaging of 'Exponential PSD rank of positively     *)
(* shifted matching matrices' uses without proof (family 126 of the OpenAI    *)
(* math collection, revision 1581d4cbd, source/sections/local-averaging.tex,  *)
(* lines 177-185: the sum of 1/j for j from 1 to g* + 1 is O(log(h + 2))). It *)
(* follows no Lean module of the collection. MathComp-Analysis defines the    *)
(* terms of the harmonic series, harmonic in sequences.v, not their partial   *)
(* sums; the statement writes the sum.                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition harmonic_ln_statement (R : realType) : Prop :=
  forall n : nat, (0 < n)%N ->
  \sum_(i < n) (i.+1%:R)^-1 <= 1 + ln (n%:R : R).
