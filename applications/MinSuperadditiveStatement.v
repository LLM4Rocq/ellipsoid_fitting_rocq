From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import topology normedtype sequences exp.

(**md**************************************************************************)
(* # Convergence from approximate minimum inequalities: the statement         *)
(*                                                                            *)
(* Target T12 of phase 13 (AGENTS.md, section Phase 13; the plan              *)
(* notes/phase13-plan.md, section 2). The statement of a Rocq formalization   *)
(* of the credited argument of the lemma 'Balanced comparisons'               *)
(* (lem:balanced-comparison) of 'A Limiting Satisfiability Threshold for      *)
(* Every Fixed Clause Size' (family 235 of the OpenAI math collection,        *)
(* revision 1581d4cbd, source/sections/convergence.tex). This file holds the  *)
(* statement only; it unfolds to MathComp and MathComp-Analysis (powR, cvgn,  *)
(* limn) and to no definition of the library. The convergence is that of the  *)
(* topology and the norm of R (numFieldTopology, numFieldNormedType). The     *)
(* Lean counterparts, in lean/OAI/Probability/RandomSAT of the collection:    *)
(* Lean: balanced_tail_bound (Convergence.lean, line 123)                     *)
(* Lean: summable_min_convergence (Convergence.lean, line 141)                *)
(*                                                                            *)
(* Setting. R is any realType, u : nat -> R, A >= 0, beta > 0 and N is a      *)
(* natural number. The powers are powR. For all sizes r, s >= N that are      *)
(* comparable, r <= 3 s and s <= 3 r, u (r + s) >= min(u r, u s) - A min(r,   *)
(* s)^(-beta); and for every s >= N, u (s + 1) >= u s - A s^(-beta).          *)
(*                                                                            *)
(* min_superadditive_statement: with E = 3^beta / ((3/2)^beta - 1),           *)
(*                                                                            *)
(* - for every s >= max(N, 2) and every n >= s^2, u n >= u s - A (1 + E)      *)
(*   s^(-beta);                                                               *)
(* - if u is bounded, it converges, and its limit is at least u s - A (1 + E) *)
(*   s^(-beta) for every s >= max(N, 2).                                      *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - E is the constant of the Lean development (the user's decision D10 of 14 *)
(*   October 2026). It is (4/3)^beta times the constant B = (3/2)^beta / (1 - *)
(*   (2/3)^beta) of the manuscript, so the bound is weaker than the           *)
(*   manuscript's; it suffices for the satisfiability threshold.              *)
(* - The sum comparison is assumed only for comparable sizes, as in the       *)
(*   manuscript; the Lean lemma assumes it for all r, s >= N. Its induction   *)
(*   splits q blocks of size about s into floor(q/2) and q - floor(q/2)       *)
(*   blocks, whose sizes are comparable when s >= 2.                          *)
(* - The neighbor step cannot be dropped: u n = 1 for even n and 0 for odd n  *)
(*   satisfies the sum comparison with A = 0 and diverges.                    *)
(* - The finite-size bound needs no boundedness. Boundedness, written out     *)
(*   (there is M with |u n| <= M for every n), is assumed for the convergence *)
(*   only; the manuscript assumes it throughout.                              *)
(* - The manuscript's sequence starts at an index n_0 >= 1. Here u is defined *)
(*   on all of nat and the hypotheses start at N, which may be 0; the error   *)
(*   term at size 0 is 0, since powR gives 0^x = 0 for x != 0. So for N = 0   *)
(*   the neighbor step at size 0 requires u 1 >= u 0, which the manuscript    *)
(*   never imposes. Nothing is lost by taking N >= 1: from N = 0 to N = 1 the *)
(*   hypotheses get weaker, and the conclusion, which only concerns sizes s   *)
(*   >= 2 with s >= N, does not change.                                       *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Definition min_superadditive_statement : Prop :=
  forall (R : realType) (u : nat -> R) (A beta : R) (N : nat),
  0 <= A -> 0 < beta ->
  (forall r s, (N <= r)%N -> (N <= s)%N -> (r <= 3 * s)%N -> (s <= 3 * r)%N ->
     Num.min (u r) (u s) - A * (minn r s)%:R `^ (- beta) <= u (r + s)%N) ->
  (forall s, (N <= s)%N -> u s - A * s%:R `^ (- beta) <= u s.+1) ->
  let E := 3 `^ beta / ((3 / 2) `^ beta - 1) in
  (forall s n, (N <= s)%N -> (2 <= s)%N -> (s * s <= n)%N ->
     u s - A * (1 + E) * s%:R `^ (- beta) <= u n) /\
  ((exists M : R, forall n, `|u n| <= M) -> cvgn u /\
     forall s, (N <= s)%N -> (2 <= s)%N ->
       u s - A * (1 + E) * s%:R `^ (- beta) <= limn u).
