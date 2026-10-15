From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import sequences exp.

(**md**************************************************************************)
(* # Bounds on binomial coefficients                                          *)
(*                                                                            *)
(* Estimates of binomial coefficients: in nat, with no field, bounds on the   *)
(* central binomial coefficient and comparisons near the center; over a       *)
(* realType, a bound on the partial sums of a row of Pascal's triangle.       *)
(*                                                                            *)
(* Item X of phase 13 (AGENTS.md, section Phase 13), for the local averaging  *)
(* and the expander lemma of phase 14: a Rocq formalization of the binomial   *)
(* estimates of 'Exponential PSD rank of positively shifted matching          *)
(* matrices' (family 126 of the OpenAI math collection, revision 1581d4cbd).  *)
(* They are the central binomial estimates and the identity of                *)
(* source/sections/local-averaging.tex (equations local:central-ratio and     *)
(* local:binomial-ratio, lines 155-176), and the partial binomial sums of     *)
(* source/sections/parity.tex (lines 60-67). The manuscript uses the          *)
(* estimates without proof and leaves their constants unspecified; the        *)
(* statements below fix the constants that the audit of the manuscript        *)
(* (reviews/phase13-psd-audit.md, Part 2) checked. It follows no Lean module  *)
(* of the collection.                                                         *)
(*                                                                            *)
(* The statements are Prop definitions named after their future lemmas with   *)
(* the suffix _statement, for review with batch 3 of phase 13; nothing is     *)
(* proved yet. The squared forms avoid square roots, and no statement         *)
(* computes a large numeral.                                                  *)
(*                                                                            *)
(* - central_bin_le_statement: (3 n + 1) C(2n, n)^2 <= 16^n for every n.      *)
(* - central_bin_ge_statement: 16^n <= 4 n C(2n, n)^2 for n > 0. With the     *)
(*   previous bound, 4^n / (2 sqrt n) <= C(2n, n) <= 4^n / sqrt(3 n + 1).     *)
(* - half_bin_ge_statement: 4^h <= 2 (h + 1) C(h, floor(h/2))^2 for every h,  *)
(*   odd or even.                                                             *)
(* - leq_bin_half_statement: C(n, k) <= C(n, floor(n/2)) for all n and k.     *)
(* - bin_near_half_statement: if h >= 6 T and |2 g - h| <= 2 T, that is |g -  *)
(*   h/2| <= T, then C(h, floor(h/2)) <= 2^(T+1) C(h, g).                     *)
(* - bin_sqr_central_statement: C(u, j)^2 C(2u, u) = C(2j, j) C(2(u - j), u - *)
(*   j) C(2u, 2j) for j <= u.                                                 *)
(* - bin_sqr_ratio_statement: C(u, j)^4 (j + 1) (u - j + 1) <= 4 (u + 1)      *)
(*   C(2u, 2j)^2 for j <= u: the bound local:binomial-ratio of the manuscript *)
(*   with C = 2, squared.                                                     *)
(* - bin_partial_sum_statement: for every realType and M <= N, sum_(j <= M)   *)
(*   C(N, j) <= (e N / M)^M, where both sides are 1 for M = 0. The bound on   *)
(*   one coefficient is bin_le_expR of matrix/nets.v. In the expander lemma,  *)
(*   with N = 100 a, it gives (20 e)^(5 a) at M = 5 a and (100 e a / w)^w at  *)
(*   M = w, the two crude chains of the audit.                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The central binomial coefficient, from above and from below. *)
Definition central_bin_le_statement : Prop :=
  forall n : nat, ((3 * n).+1 * 'C(2 * n, n) ^ 2 <= 16 ^ n)%N.

Definition central_bin_ge_statement : Prop :=
  forall n : nat, (0 < n)%N -> (16 ^ n <= 4 * n * 'C(2 * n, n) ^ 2)%N.

(* The middle coefficient of every row, from below. *)
Definition half_bin_ge_statement : Prop :=
  forall h : nat, (4 ^ h <= 2 * h.+1 * 'C(h, h./2) ^ 2)%N.

(* Unimodality: the middle coefficient is the largest of its row. *)
Definition leq_bin_half_statement : Prop :=
  forall n k : nat, ('C(n, k) <= 'C(n, n./2))%N.

(* Near the middle, at distance at most T from h/2 with h >= 6 T, a
   coefficient is at least 2^-(T+1) times the middle one. *)
Definition bin_near_half_statement : Prop :=
  forall h g T : nat, (6 * T <= h)%N ->
  (h <= 2 * (g + T))%N -> (2 * g <= h + 2 * T)%N ->
  ('C(h, h./2) <= 2 ^ T.+1 * 'C(h, g))%N.

(* The ratio C(u, j)^2 / C(2u, 2j) as a ratio of central coefficients. *)
Definition bin_sqr_central_statement : Prop :=
  forall u j : nat, (j <= u)%N ->
  'C(u, j) ^ 2 * 'C(2 * u, u) =
    'C(2 * j, j) * 'C(2 * (u - j), u - j) * 'C(2 * u, 2 * j).

(* The same ratio is at most 2 sqrt((u + 1) / ((j + 1) (u - j + 1))). *)
Definition bin_sqr_ratio_statement : Prop :=
  forall u j : nat, (j <= u)%N ->
  ('C(u, j) ^ 4 * j.+1 * (u - j).+1 <= 4 * u.+1 * 'C(2 * u, 2 * j) ^ 2)%N.

(* The partial sums of a row of Pascal's triangle. *)
Definition bin_partial_sum_statement : Prop :=
  forall (R : realType) (N M : nat), (M <= N)%N ->
  \sum_(j < M.+1) ('C(N, j))%:R <= (expR 1 * N%:R / M%:R) ^+ M :> R.
