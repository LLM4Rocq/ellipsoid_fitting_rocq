From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum rat reals.
From mathcomp Require Import sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic.

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
(* Each main result is stated first as a Prop definition with the suffix      *)
(* _statement, for review with batch 3 of phase 13, and the lemma of the same *)
(* name proves it with the same text; the definitions go once the user        *)
(* accepts them. The squared forms avoid square roots, and no statement       *)
(* computes a large numeral.                                                  *)
(*                                                                            *)
(* - central_bin_le: (3 n + 1) C(2n, n)^2 <= 16^n for every n.                *)
(* - central_bin_ge: 16^n <= 4 n C(2n, n)^2 for n > 0. Both follow from the   *)
(*   recursion central_binS, (n + 1) C(2n + 2, n + 1) = 2 (2n + 1) C(2n, n),  *)
(*   by induction. With the previous bound, 4^n / (2 sqrt n) <= C(2n, n) <=   *)
(*   4^n / sqrt(3 n + 1): fair_coin_tie, the example at the end.              *)
(* - half_bin_ge: 4^h <= 2 (h + 1) C(h, floor(h/2))^2 for every h, odd or     *)
(*   even (central_bin_odd: C(2n + 2, n + 1) = 2 C(2n + 1, n)).               *)
(* - leq_bin_half: C(n, k) <= C(n, floor(n/2)) for all n and k, from          *)
(*   leq_bin_succ: C(n, k) <= C(n, k + 1) when 2 k + 1 <= n.                  *)
(* - bin_near_half: if h >= 6 T and |2 g - h| <= 2 T, that is |g - h/2| <= T, *)
(*   then C(h, floor(h/2)) <= 2^(T+1) C(h, g). Below the middle 2^T suffices  *)
(*   (bin_near_half_low): each step toward the middle multiplies by at most 2 *)
(*   (bin_ratio_le2, bin_shift_le).                                           *)
(* - bin_sqr_central: C(u, j)^2 C(2u, u) = C(2j, j) C(2(u - j), u - j) C(2u,  *)
(*   2j) for j <= u, by factorials.                                           *)
(* - bin_sqr_ratio: C(u, j)^4 (j + 1) (u - j + 1) <= 4 (u + 1) C(2u, 2j)^2    *)
(*   for j <= u: the bound local:binomial-ratio of the manuscript with C = 2, *)
(*   squared; from the identity and the two central bounds.                   *)
(* - bin_partial_sum: for every realType and M <= N, sum_(j <= M) C(N, j) <=  *)
(*   (e N / M)^M, where both sides are 1 for M = 0: with x = M / N, x^M times *)
(*   the partial sum is at most (1 + x)^N <= e^M. The bound on one            *)
(*   coefficient is bin_le_expR of matrix/nets.v. In the expander lemma, with *)
(*   N = 100 a, it gives (20 e)^(5 a) at M = 5 a and (100 e a / w)^w at M =   *)
(*   w, the two crude chains of the audit.                                    *)
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

Section central.
Local Open Scope nat_scope.

(* The central coefficient of an even row is twice the middle ones of the
   odd row above it. *)
Lemma central_bin_odd n : 'C(2 * n.+1, n.+1) = 2 * 'C((2 * n).+1, n).
Proof.
have hn : n.+1 <= (2 * n).+1 by rewrite ltnS mul2n -addnn leq_addr.
have hs : 'C((2 * n).+1, n.+1) = 'C((2 * n).+1, n).
  rewrite -(bin_sub hn); congr 'C(_, _).
  by rewrite subSS mul2n -addnn addnK.
have e0 : 2 * n.+1 = (2 * n).+2 by rewrite mulnS add2n.
by rewrite e0 binS hs addnn -mul2n.
Qed.

(* The ratio of consecutive central coefficients. *)
Lemma central_binS n :
  n.+1 * 'C(2 * n.+1, n.+1) = 2 * (2 * n).+1 * 'C(2 * n, n).
Proof.
have hn : n.+1 <= (2 * n).+1 by rewrite ltnS mul2n -addnn leq_addr.
have hs : 'C((2 * n).+1, n.+1) = 'C((2 * n).+1, n).
  rewrite -(bin_sub hn); congr 'C(_, _).
  by rewrite subSS mul2n -addnn addnK.
have e3 : (2 * n).+1 * 'C(2 * n, n) = n.+1 * 'C((2 * n).+1, n).
  by rewrite -hs -(mul_bin_diag (2 * n).+1 n).
by rewrite central_bin_odd -mulnA e3; ring.
Qed.

Lemma central_bin_le n : (3 * n).+1 * 'C(2 * n, n) ^ 2 <= 16 ^ n.
Proof.
elim: n => [|n IH]; first by [].
rewrite -(@leq_pmul2l (n.+1 ^ 2)) ?expn_gt0 //.
have -> : n.+1 ^ 2 * ((3 * n.+1).+1 * 'C(2 * n.+1, n.+1) ^ 2) =
    (3 * n.+1).+1 * (n.+1 * 'C(2 * n.+1, n.+1)) ^ 2 by ring.
rewrite central_binS.
(* (3 n + 4) (2 n + 1)^2 + n = 4 (n + 1)^2 (3 n + 1) *)
have poly : (3 * n.+1).+1 * (2 * n).+1 ^ 2 <= 4 * n.+1 ^ 2 * (3 * n).+1.
  have <- : (3 * n.+1).+1 * (2 * n).+1 ^ 2 + n = 4 * n.+1 ^ 2 * (3 * n).+1.
    by ring.
  exact: leq_addr.
apply: (@leq_trans (4 * (4 * n.+1 ^ 2 * (3 * n).+1) * 'C(2 * n, n) ^ 2)).
  have -> : (3 * n.+1).+1 * (2 * (2 * n).+1 * 'C(2 * n, n)) ^ 2 =
      4 * ((3 * n.+1).+1 * (2 * n).+1 ^ 2) * 'C(2 * n, n) ^ 2 by ring.
  by rewrite leq_mul2r leq_mul2l /= poly orbT.
have -> : 4 * (4 * n.+1 ^ 2 * (3 * n).+1) * 'C(2 * n, n) ^ 2 =
    16 * n.+1 ^ 2 * ((3 * n).+1 * 'C(2 * n, n) ^ 2) by ring.
apply: (@leq_trans (16 * n.+1 ^ 2 * 16 ^ n)).
  by rewrite leq_mul2l IH orbT.
by rewrite [16 ^ n.+1]expnS mulnA [n.+1 ^ 2 * 16]mulnC.
Qed.

Lemma central_bin_ge n : 0 < n -> 16 ^ n <= 4 * n * 'C(2 * n, n) ^ 2.
Proof.
elim: n => [//|n IH] _.
have [->|n0] := posnP n; first by [].
rewrite -(@leq_pmul2l n.+1) //.
have -> : n.+1 * (4 * n.+1 * 'C(2 * n.+1, n.+1) ^ 2) =
    4 * (n.+1 * 'C(2 * n.+1, n.+1)) ^ 2 by ring.
rewrite central_binS.
apply: (@leq_trans (16 * n.+1 * (4 * n * 'C(2 * n, n) ^ 2))).
  by rewrite [16 ^ n.+1]expnS mulnA [n.+1 * 16]mulnC leq_mul2l IH ?orbT.
(* 4 n (n + 1) + 1 = (2 n + 1)^2 *)
have poly : 4 * n * n.+1 + 1 = (2 * n).+1 ^ 2 by ring.
have -> : 16 * n.+1 * (4 * n * 'C(2 * n, n) ^ 2) =
    16 * (4 * n * n.+1) * 'C(2 * n, n) ^ 2 by ring.
have -> : 4 * (2 * (2 * n).+1 * 'C(2 * n, n)) ^ 2 =
    16 * (2 * n).+1 ^ 2 * 'C(2 * n, n) ^ 2 by ring.
by rewrite leq_mul2r leq_mul2l -poly leq_addr !orbT.
Qed.

Lemma half_bin_ge h : 4 ^ h <= 2 * h.+1 * 'C(h, h./2) ^ 2.
Proof.
have [[n ->] | [n ->]] : (exists n, h = 2 * n) \/ (exists n, h = (2 * n).+1).
  have := odd_double_half h; case: (odd h) => /= e.
  - by right; exists h./2; rewrite -[LHS]e mul2n add1n.
  - by left; exists h./2; rewrite -[LHS]e mul2n.
- rewrite mul2n doubleK -mul2n.
  have [->|n0] := posnP n; first by [].
  rewrite [4 ^ _]expnM; apply: leq_trans (central_bin_ge n0) _.
  by rewrite leq_mul2r mulnS mulnA leq_addl orbT.
- have hh : (2 * n).+1./2 = n by rewrite mul2n /= uphalf_double.
  have e2 : (2 * n).+2 = 2 * n.+1 by rewrite mulnS add2n.
  rewrite hh -(@leq_pmul2l 4) // -expnS e2 expnM.
  apply: leq_trans (central_bin_ge (ltn0Sn n)) _.
  by rewrite central_bin_odd; apply: eq_leq; ring.
Qed.

(* One step up a row, below its middle. *)
Lemma leq_bin_succ n k : (2 * k).+1 <= n -> 'C(n, k) <= 'C(n, k.+1).
Proof.
move=> h; have kn : k <= n.
  by apply: leq_trans (ltnW h); rewrite mul2n -addnn leq_addl.
rewrite -(@leq_pmul2l k.+1) // mul_bin_left leq_mul2r; apply/orP; right.
by rewrite leq_subRL // addnS addnn -mul2n.
Qed.

Lemma bin_half_mono n k d : k + d <= n./2 -> 'C(n, k) <= 'C(n, k + d).
Proof.
elim: d => [|d IH] h; first by rewrite addn0.
have h' : k + d <= n./2 by apply: leq_trans h; rewrite leq_add2l.
apply: leq_trans (IH h') _; rewrite addnS; apply: leq_bin_succ.
by move: h; rewrite geq_half_double addnS doubleS mul2n => /ltnW.
Qed.

Lemma leq_bin_half n k : 'C(n, k) <= 'C(n, n./2).
Proof.
have low j : j <= n./2 -> 'C(n, j) <= 'C(n, n./2).
  by move=> hj; have := @bin_half_mono n j (n./2 - j); rewrite subnKC //; apply.
case: (leqP k n./2) => hk; first exact: low.
case: (leqP k n) => kn; last by rewrite bin_small.
(* Above the middle, by symmetry. *)
rewrite -(bin_sub kn); apply: low.
rewrite leq_subLR; apply: (@leq_trans (n./2.*2.+1)).
  by rewrite -leq_half_double.
by rewrite -addnn -addSn leq_add2r.
Qed.

(* One step up a row loses at most a factor 2 when h <= 3 k + 2. *)
Lemma bin_ratio_le2 h k : h <= 3 * k + 2 -> 'C(h, k.+1) <= 2 * 'C(h, k).
Proof.
move=> hk; rewrite -(@leq_pmul2l k.+1) // mul_bin_left mulnA [k.+1 * 2]mulnC.
rewrite leq_mul2r; apply/orP; right; rewrite leq_subLR.
by have -> : k + 2 * k.+1 = 3 * k + 2 by ring.
Qed.

Lemma bin_shift_le h k d : h <= 3 * k + 2 -> 'C(h, k + d) <= 2 ^ d * 'C(h, k).
Proof.
move=> hk; elim: d => [|d IH]; first by rewrite addn0 expn0 mul1n.
rewrite addnS expnS -mulnA; apply: leq_trans (bin_ratio_le2 _) _.
  by apply: leq_trans hk _; rewrite leq_add2r leq_mul2l leq_addr orbT.
by rewrite leq_mul2l IH orbT.
Qed.

Lemma bin_near_half_low h g T : 6 * T <= h -> h <= 2 * (g + T) ->
  g <= h./2 -> 'C(h, h./2) <= 2 ^ T * 'C(h, g).
Proof.
move=> hT hg gm.
have hk : h <= 3 * g + 2.
  by move: hT hg; rewrite -!(ler_nat rat) ?natrD ?natrM; lra.
have dT : h./2 - g <= T.
  rewrite leq_subLR leq_half_double; apply: leq_trans hg _.
  by rewrite mul2n leqnSn.
rewrite -[X in 'C(h, X)](subnKC gm).
apply: leq_trans (bin_shift_le _ hk) _.
by rewrite leq_mul2r leq_pexp2l // orbT.
Qed.

Lemma bin_near_half h g T : 6 * T <= h ->
  h <= 2 * (g + T) -> 2 * g <= h + 2 * T ->
  'C(h, h./2) <= 2 ^ T.+1 * 'C(h, g).
Proof.
move=> hT hg gh; have e2 : 2 ^ T <= 2 ^ T.+1 by rewrite leq_pexp2l.
have [gm|mg] := leqP g h./2.
  apply: leq_trans (bin_near_half_low hT hg gm) _.
  by rewrite leq_mul2r e2 orbT.
(* Above the middle, by symmetry. *)
have gle : g <= h.
  move: hT gh; rewrite -!(ler_nat rat) ?natrD ?natrM.
  by move: (ler0n rat h) (ler0n rat T); lra.
rewrite -(bin_sub gle).
apply: leq_trans (@bin_near_half_low h (h - g) T hT _ _) _.
- by move: gh (ler0n rat T); rewrite -!(ler_nat rat) ?natrD ?natrM ?natrB //;
    lra.
- rewrite leq_subLR; apply: (@leq_trans (h./2.*2.+1)).
    by rewrite -leq_half_double.
  by rewrite -addnn -addSn leq_add2r.
- by rewrite leq_mul2r e2 orbT.
Qed.

(* C(u, j)^2 / C(2u, 2j) as a ratio of central coefficients. *)
Lemma bin_sqr_central u j : j <= u ->
  'C(u, j) ^ 2 * 'C(2 * u, u) =
    'C(2 * j, j) * 'C(2 * (u - j), u - j) * 'C(2 * u, 2 * j).
Proof.
move=> ju.
have dbl n : 2 * n - n = n by rewrite mul2n -addnn addnK.
have le2 n : n <= 2 * n by rewrite mul2n -addnn leq_addl.
have f1 := bin_fact ju.
have f2 := bin_fact (le2 u); rewrite dbl in f2.
have f3 := bin_fact (le2 j); rewrite dbl in f3.
have f4 := bin_fact (le2 (u - j)); rewrite dbl in f4.
have f5 : 'C(2 * u, 2 * j) * ((2 * j)`! * (2 * (u - j))`!) = (2 * u)`!.
  by rewrite mulnBr bin_fact // leq_mul2l ju orbT.
(* Both sides times P are products of factorials. *)
set P := (j`! * (u - j)`!) ^ 2 * (u`! * u`!) * ((2 * j)`! * (2 * (u - j))`!).
have P0 : 0 < P by rewrite /P !muln_gt0 ?expn_gt0 ?muln_gt0 !fact_gt0.
apply/eqP; rewrite -(eqn_pmul2r P0); apply/eqP.
have -> : 'C(u, j) ^ 2 * 'C(2 * u, u) * P =
    ('C(u, j) * (j`! * (u - j)`!)) ^ 2 * ('C(2 * u, u) * (u`! * u`!)) *
    ((2 * j)`! * (2 * (u - j))`!) by rewrite /P; ring.
have -> : 'C(2 * j, j) * 'C(2 * (u - j), u - j) * 'C(2 * u, 2 * j) * P =
    ('C(2 * j, j) * (j`! * j`!)) *
    ('C(2 * (u - j), u - j) * ((u - j)`! * (u - j)`!)) *
    ('C(2 * u, 2 * j) * ((2 * j)`! * (2 * (u - j))`!)) * (u`! * u`!).
  by rewrite /P; ring.
by rewrite f1 f2 f3 f4 f5; ring.
Qed.

Lemma bin_sqr_ratio u j : j <= u ->
  'C(u, j) ^ 4 * j.+1 * (u - j).+1 <= 4 * u.+1 * 'C(2 * u, 2 * j) ^ 2.
Proof.
move=> ju.
have c0 : 0 < 'C(2 * u, u) by rewrite bin_gt0 mul2n -addnn leq_addl.
have cb n : n.+1 * 'C(2 * n, n) ^ 2 <= 16 ^ n.
  apply: leq_trans (central_bin_le n).
  by rewrite leq_mul2r ltnS leq_pmull ?orbT.
have hu : 16 ^ u <= 4 * u.+1 * 'C(2 * u, u) ^ 2.
  have [->|u0] := posnP u; first by [].
  apply: leq_trans (central_bin_ge u0) _.
  by rewrite leq_mul2r leq_mul2l leqnSn !orbT.
(* Multiply by C(2u, u)^2 and use the identity. *)
rewrite -(@leq_pmul2r ('C(2 * u, u) ^ 2)) ?expn_gt0 ?c0 //.
have -> : 'C(u, j) ^ 4 * j.+1 * (u - j).+1 * 'C(2 * u, u) ^ 2 =
    j.+1 * (u - j).+1 * ('C(u, j) ^ 2 * 'C(2 * u, u)) ^ 2 by ring.
rewrite bin_sqr_central //.
have -> : j.+1 * (u - j).+1 *
    ('C(2 * j, j) * 'C(2 * (u - j), u - j) * 'C(2 * u, 2 * j)) ^ 2 =
    (j.+1 * 'C(2 * j, j) ^ 2) * ((u - j).+1 * 'C(2 * (u - j), u - j) ^ 2) *
    'C(2 * u, 2 * j) ^ 2 by ring.
apply: (@leq_trans (16 ^ j * 16 ^ (u - j) * 'C(2 * u, 2 * j) ^ 2)).
  by rewrite leq_mul2r leq_mul ?cb ?orbT.
rewrite -expnD subnKC //.
have -> : 4 * u.+1 * 'C(2 * u, 2 * j) ^ 2 * 'C(2 * u, u) ^ 2 =
    4 * u.+1 * 'C(2 * u, u) ^ 2 * 'C(2 * u, 2 * j) ^ 2 by ring.
by rewrite leq_mul2r hu orbT.
Qed.

End central.

Section partial_sums.
Context {R : realType}.

(* With x = M / N: x^M sum_(j <= M) C(N, j) <= (1 + x)^N <= e^M. *)
Lemma bin_partial_sum N M : (M <= N)%N ->
  \sum_(j < M.+1) ('C(N, j))%:R <= (expR 1 * N%:R / M%:R) ^+ M :> R.
Proof.
move=> MN; case: M MN => [|M] MN; first by rewrite big_ord1 bin0 expr0.
have N0 : (0 < N)%N by apply: leq_trans MN.
have N0' : 0 < N%:R :> R by rewrite ltr0n.
set x : R := M.+1%:R / N%:R.
have x0 : 0 <= x by rewrite divr_ge0 ?ler0n.
have xp : 0 < x by rewrite divr_gt0 ?ltr0n.
have x1 : x <= 1 by rewrite ler_pdivrMr // mul1r ler_nat.
(* x^(M+1) times the partial sum is at most the full sum (1 + x)^N. *)
have h1 : x ^+ M.+1 * \sum_(j < M.+2) ('C(N, j))%:R <= (x + 1) ^+ N.
  rewrite exprD1n mulr_sumr.
  apply: (@le_trans _ _ (\sum_(j < M.+2) x ^+ j *+ 'C(N, j))).
    apply: ler_sum => j _; rewrite mulr_natr; apply: ler_wMn2r.
    by apply: ler_wiXn2l; rewrite // -ltnS.
  rewrite (big_ord_widen N.+1 (fun j => x ^+ j *+ 'C(N, j))) ?ltnS //.
  rewrite big_mkcond /=; apply: ler_sum => j _.
  by case: ifP => _ //; rewrite mulrn_wge0 ?exprn_ge0.
(* (1 + x)^N <= exp(x N) = e^(M+1). *)
have h2 : (x + 1) ^+ N <= expR 1 ^+ M.+1.
  apply: le_trans (lerXn2r _ _ _ (_ : x + 1 <= expR x)) _.
  - by rewrite nnegrE addr_ge0.
  - by rewrite nnegrE expR_ge0.
  - by rewrite addrC expR_ge1Dx.
  rewrite -[expR x ^+ N]expRM_natr /x divfK ?gt_eqF //.
  by rewrite -[expR 1 ^+ _]expRM_natl mulr1.
have -> : expR 1 * N%:R / M.+1%:R = expR 1 / x by rewrite /x invf_div mulrA.
rewrite expr_div_n ler_pdivlMr ?exprn_gt0 // mulrC.
exact: le_trans h1 h2.
Qed.

End partial_sums.

Section example.
Context {R : realType}.

(* An example: in 2 n tosses of a fair coin, n >= 1, a tie (n heads) has
   probability C(2n, n) / 4^n, between 1 / (2 sqrt n) and 1 / sqrt(3 n + 1). *)
Example fair_coin_tie n : (0 < n)%N ->
  (2 * Num.sqrt n%:R)^-1 <= ('C(2 * n, n))%:R / 4 ^+ n :> R /\
  ('C(2 * n, n))%:R / 4 ^+ n <= (Num.sqrt (3 * n).+1%:R)^-1 :> R.
Proof.
move=> n0; set p : R := _ / _.
have p0 : 0 <= p by rewrite divr_ge0 ?ler0n ?exprn_ge0.
have n0' : 0 < n%:R :> R by rewrite ltr0n.
have hp : p ^+ 2 = ('C(2 * n, n) ^ 2)%:R / (16 ^ n)%:R.
  rewrite /p expr_div_n natrX natrX; congr (_ / _).
  by rewrite -exprM mulnC exprM; congr (_ ^+ _); rewrite expr2 -natrM.
have cge := central_bin_ge n0.
have cle := central_bin_le n.
(* Compare the squares. *)
have s2 (a b : R) : 0 <= a -> 0 <= b -> (a <= b) = (a ^+ 2 <= b ^+ 2).
  by move=> a0 b0; rewrite ler_pXn2r ?nnegrE.
have c16 : 0 < (16 ^ n)%:R :> R by rewrite ltr0n expn_gt0.
split.
- have a0 : 0 <= (2 * Num.sqrt n%:R)^-1 :> R.
    by rewrite invr_ge0 mulr_ge0 ?sqrtr_ge0.
  rewrite (s2 _ _ a0 p0) hp exprVn exprMn sqr_sqrtr ?ler0n //.
  rewrite ler_pdivlMr // mulrC ler_pdivrMr ?mulr_gt0 ?exprn_gt0 //.
  rewrite -natrX -!natrM ler_nat; apply: leq_trans cge _.
  by apply: eq_leq; ring.
- have b0 : 0 <= (Num.sqrt (3 * n).+1%:R)^-1 :> R by rewrite invr_ge0 sqrtr_ge0.
  rewrite (s2 _ _ p0 b0) hp exprVn sqr_sqrtr ?ler0n //.
  by rewrite ler_pdivrMr // ler_pdivlMl ?ltr0n // -!natrM ler_nat.
Qed.

End example.
