From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import sequences exp.
From GaussianApplications Require Import SatVarianceDefinitions.

(**md**************************************************************************)
(* # Capped variance of random k-SAT: the statement                           *)
(*                                                                            *)
(* Target T7 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The statement of a Rocq formalization   *)
(* of the credited argument of the proposition 'Polynomial concentration' of  *)
(* 'A limiting satisfiability threshold for every fixed clause size' (family  *)
(* 235 of the OpenAI math collection, revision 1581d4cbd,                     *)
(* source/sections/concentration.tex), with the lemmas before it and the      *)
(* proposition of source/sections/forcing.tex. This file holds the statement  *)
(* only; its definitions are those of SatVarianceDefinitions.v. The Lean      *)
(* counterpart, in lean/OAI/Probability/RandomSAT of the collection:          *)
(* Lean: variance_capped (Concentration.lean, line 80)                        *)
(*                                                                            *)
(* Setting. R is any realType and k >= 3. V_n is the length of the longest    *)
(* satisfiable prefix, capped at L_k n = 2^(k+1) n, of a tuple of L_k n       *)
(* independent uniform proper signed k-clauses on n variables, and            *)
(* sat_capped_var n k is its variance (SatVarianceDefinitions.v).             *)
(*                                                                            *)
(* sat_variance_statement, for every R and every k >= 3: there is C > 0 such  *)
(* that Var(V_n) <= C n^(1 + 2/k) for every n >= k + 1, the power being powR. *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - The manuscript writes Var(V_n) = O_k(n^(1 + 2/k)); here the constant C   *)
(*   depends on k (and formally on R) only, and the bound holds for every n   *)
(*   >= k + 1, the range of the Lean theorem, not only for large n.           *)
(* - V_n is defined directly as the largest satisfiable prefix length up to   *)
(*   the cap, on exactly L_k n clauses, as the user decided: it is min(H_n -  *)
(*   1, L_k n), with H_n the first unsatisfiable index, without an extra      *)
(*   clause, and it covers the tuples whose every prefix is satisfiable.      *)
(* - The Lean theorem bounds the variance of a lifetime defined by a          *)
(*   recursion over the clause process, with the constant varianceConstant k  *)
(*   n (n^(1/k))^2; the statement here is the manuscript's.                   *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition sat_variance_statement : Prop :=
  forall (R : realType) (k : nat), (3 <= k)%N ->
  exists C : R, 0 < C /\
  forall n : nat, (k.+1 <= n)%N ->
    sat_capped_var R n k <= C * n%:R `^ (1 + 2 / k%:R).
