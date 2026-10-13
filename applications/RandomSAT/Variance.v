From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianApplications.RandomSAT Require Import Model Pivotal Replacement Forcing.
From GaussianApplications Require Import SatVarianceDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: the capped variance bound                                  *)
(*                                                                            *)
(* Part of target T7 of phase 12 (see Model.v). A Rocq formalization of the   *)
(* credited argument of the proposition 'Polynomial concentration' of 'A      *)
(* limiting satisfiability threshold for every fixed clause size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/concentration.tex), assembled as in the Lean development   *)
(* of the collection (lean/OAI/Probability/RandomSAT):                        *)
(* Lean: truncatedKilling_le_forced (Variance.lean, line 412)                 *)
(* Lean: lifetimeVariance_forcing_bound (Variance.lean, line 487)             *)
(* Lean: replacementScale (Replacement.lean, line 282)                        *)
(* Lean: integrated_forcing_capped (Concentration.lean, line 49)              *)
(* Lean: variance_capped (Concentration.lean, line 80)                        *)
(*                                                                            *)
(* - trunc_le_forced: if M <= c^k, then min(M kill k S, 1) <= c b / n, with b *)
(*   the number of forced variables of S, since the killing probability is at *)
(*   most (b / n)^k (kfrac_le_pow).                                           *)
(* - sat_capped_varE: sat_capped_var R n k, the variance of the statistic of  *)
(*   the statement, is life_var k (sat_cap k n) of the set of all assignments *)
(*   (sat_prefix_lenE of Model.v).                                            *)
(* - sat_variance_bound: for K >= 3 and N >= K + 1, sat_capped_var R N K <= C *)
(*   N^(1 + 2/K), with C = 8 4^(K+1) K (3 K + 2^(K+2)). The proof takes a =   *)
(*   N^(1/K), the block g = floor(2 K a) + 1 <= 3 K a and c = 4 a, so that    *)
(*   the cap M = 2^(K+1) N is at most c^K; life_var_le_occ of Pivotal.v,      *)
(*   trunc_le_forced, forced_frac_head and integrated_head_forcing of         *)
(*   Forcing.v then bound the variance by 2 M c (g M p + (M + 1) M p          *)
(*   a^-(K-1)), with p = K / N, and N a^-(K-1) = a, N a^2 = N^(1 + 2/K).      *)
(*                                                                            *)
(* The statement and the manuscript bound Var(V_n) by C n^(1 + 2/k); the Lean *)
(* theorem bounds the variance of the lifetime by a constant times n          *)
(* (n^(1/k))^2, with a block of size ceil(2 k n^(1/k)). The constant here is  *)
(* explicit and holds for every n >= k + 1.                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section bounds.
Context {R : realType}.

(* min (M q, 1) <= c y when q <= y^K, M <= c^K and K >= 1. *)
Lemma min_le_lin (M q y c : R) K : (0 < K)%N -> 0 <= q -> 0 <= y -> 0 <= c ->
  0 <= M -> q <= y ^+ K -> M <= c ^+ K -> Num.min (M * q) 1 <= c * y.
Proof.
move=> K0 q0 y0 c0 M0 qy Mc.
have cy0 : 0 <= c * y by rewrite mulr_ge0.
have [cy1|cy1] := lerP 1 (c * y); first by rewrite ge_min cy1 orbT.
rewrite ge_min; apply/orP; left.
apply: le_trans (_ : c ^+ K * y ^+ K <= _).
  by apply: ler_pM.
rewrite -exprMn -[X in _ <= X]expr1.
by apply: ler_wiXn2l => //; exact: ltW.
Qed.

(* The truncated killing chance is at most c times the forced fraction. *)
Lemma trunc_le_forced n k M (c : R) (S : {set {ffun 'I_n -> bool}}) :
  (0 < k)%N -> (k <= n)%N -> 0 <= c -> M%:R <= c ^+ k ->
  trunc k M S <= c * (#|forced S|%:R / n%:R).
Proof.
move=> k0 kn c0 Mc.
have C0 : (0 < #|{: clause n k}|)%N by rewrite card_clause_gt0.
have n0 : (0 < n)%N by apply: leq_trans kn.
have [->|S0] := eqVneq S set0.
  rewrite /trunc (kill0 C0) mulr0 forced0 cards0 mul0r mulr0.
  by rewrite ge_min lexx.
have bn : (#|forced S| <= n)%N by rewrite -[X in (_ <= X)%N]card_ord max_card.
rewrite /trunc killE_forced //.
apply: (min_le_lin (K := k)) => //.
- exact: kfrac_ge0.
- by rewrite divr_ge0.
- apply: le_trans (kfrac_le_pow bn kn n0) _.
  apply: lerXn2r; rewrite ?nnegrE.
  + by rewrite divr_ge0 // mulr_ge0.
  + by rewrite divr_ge0.
  have n0' : 0 < n%:R :> R by rewrite ltr0n.
  rewrite invfM mulrCA -[X in _ <= X]mul1r.
  apply: ler_wpM2r; first by rewrite divr_ge0.
  by rewrite invf_le1 // ler1n.
Qed.

End bounds.

Section sat_variance.
Context {R : realType}.

Lemma sat_capped_varE n k :
  sat_capped_var R n k = life_var k (sat_cap k n) [set: {ffun 'I_n -> bool}].
Proof.
rewrite /sat_capped_var /life_var.
transitivity (unif_var (fun t : (sat_cap k n).-tuple (clause n k) =>
  (sat_prefix_len t)%:R : R)); first by [].
by apply: eq_unif_var => t; exact: sat_prefix_lenE.
Qed.

(* The root a = n^(1/K) of the manuscript's block size and error. *)
Section root.
Variables (n k : nat).
Let a : R := n.+1%:R `^ (k.+1%:R)^-1.

Lemma root_gt0 : 0 < a.
Proof. by rewrite powR_gt0 // ltr0n. Qed.

Lemma root_pow : a ^+ k.+1 = n.+1%:R.
Proof.
rewrite -powR_mulrn ?powR_ge0 // /a -powRrM mulVf ?pnatr_eq0 //.
by rewrite powRr1 // ler0n.
Qed.

Lemma root_ge1 : 1 <= a.
Proof.
rewrite leNgt; apply/negP => a1.
have : a ^+ k.+1 < 1 by rewrite exprn_ilt1 // ltW // root_gt0.
by rewrite root_pow ltNge ler1n.
Qed.

Lemma root_small : (n.+1%:R)^-1 <= a^-1 ^+ k.
Proof.
have a0 := root_gt0; have a1 := root_ge1.
rewrite exprVn lef_pV2 ?posrE ?exprn_gt0 ?ltr0n // -root_pow exprS.
by rewrite ler_peMl // exprn_ge0 // ltW.
Qed.

Lemma root_err : n.+1%:R * a^-1 ^+ k = a.
Proof.
have a0 := root_gt0.
by rewrite -root_pow exprVn exprSr -mulrA mulrCA mulfV ?mulr1 // expf_neq0 // gt_eqF.
Qed.

Lemma root_sqr : n.+1%:R * a ^+ 2 = n.+1%:R `^ (1 + 2 / k.+1%:R).
Proof.
have h : (1 + 2 / k.+1%:R == 0 :> R) ==> (n.+1%:R != 0 :> R).
  by apply/implyP => _; rewrite pnatr_eq0.
rewrite (powRD h).
rewrite powRr1 ?ler0n //; congr (_ * _).
rewrite -powR_mulrn ?powR_ge0 // /a -powRrM.
by rewrite mulrC.
Qed.

End root.

Lemma trunc_block (x : R) : 1 <= x -> (Num.truncn (2 * x)).+1%:R <= 3 * x.
Proof.
move=> x1; have x0 : 0 <= 2 * x by rewrite mulr_ge0 // (le_trans ler01).
have := x0; rewrite -truncn_le => h.
rewrite -nat1r; lra.
Qed.

(* The arithmetic of the final bound, over plain real numbers. *)
Lemma variance_arith (V Sg m N K a g e t : R) :
  0 < N -> 0 <= a -> 0 <= K -> 0 <= e -> 0 <= t -> 1 <= m -> m = t * N ->
  N * e = a -> g <= 3 * (K * a) ->
  V <= 2 * m * (4 * a * Sg) ->
  Sg <= g * m * (K / N) + (m + 1) * m * (K / N) * e ->
  V <= 8 * t * t * K * (3 * K + 2 * t) * (N * a ^+ 2).
Proof.
move=> N0 a0 K0 e0 t0 m1 mE Ne hg hV hS.
have mK : m * (K / N) = t * K by rewrite mE mulrAC -mulrA divfK ?gt_eqF.
have tK0 : 0 <= t * K by rewrite mulr_ge0.
have hS' : Sg <= t * K * a * (3 * K + 2 * t).
  have E1 : g * m * (K / N) = g * (t * K) by rewrite -mulrA mK.
  have E2 : (m + 1) * m * (K / N) * e = (m + 1) * (t * K * e).
    by rewrite -mK; ring.
  apply: le_trans hS _; rewrite E1 E2.
  have h1 : g * (t * K) <= 3 * (K * a) * (t * K) by rewrite ler_wpM2r.
  have h2 : (m + 1) * (t * K * e) <= 2 * m * (t * K * e).
    by rewrite ler_wpM2r ?mulr_ge0 //; lra.
  have h3 : 2 * m * (t * K * e) = 2 * t * K * t * (N * e).
    by rewrite mE; ring.
  rewrite h3 Ne in h2.
  apply: le_trans (lerD h1 h2) _.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
have hm0 : 0 <= 2 * m * (4 * a) by rewrite !mulr_ge0 // (le_trans ler01).
apply: le_trans hV _.
rewrite mulrA; apply: le_trans (ler_wpM2l hm0 hS') _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite mE; ring.
Qed.

Theorem sat_variance_bound K : (3 <= K)%N ->
  exists C : R, 0 < C /\ forall N, (K.+1 <= N)%N ->
    sat_capped_var R N K <= C * N%:R `^ (1 + 2 / K%:R).
Proof.
move=> K3.
pose C : R := 8 * 2 ^+ K.+1 * 2 ^+ K.+1 * K%:R * (3 * K%:R + 2 ^+ K.+2).
have K0 : (0 < K)%N by apply: leq_trans K3.
exists C; split.
  have h1 : 0 < 3 * K%:R + 2 ^+ K.+2 :> R.
    by rewrite ltr_wpDl ?exprn_gt0 // mulr_ge0 ?ler0n.
  by rewrite /C !mulr_gt0 ?exprn_gt0 ?ltr0n.
case: K K3 K0 @C => [//|k] K3 _ C N KN.
case: N KN => [//|n] KN.
have k1 : (1 <= k)%N by move: K3; rewrite ltnS; apply: leq_trans.
have kn : (k < n)%N by move: KN; rewrite !ltnS.
set M := sat_cap k.+1 n.+1.
set a : R := n.+1%:R `^ (k.+1%:R)^-1.
have a0 : 0 < a := root_gt0 n k.
have a1 : 1 <= a := root_ge1 n k.
have aK : a ^+ k.+1 = n.+1%:R := root_pow n k.
have ka1 : 1 <= k.+1%:R * a.
  by rewrite -[X in X <= _]mulr1 ler_pM // ?ler1n.
set g := (Num.truncn (2 * (k.+1%:R * a))).+1.
have hg : 2 * k.+1%:R * a <= g%:R by rewrite -mulrA ltW // truncnS_gt.
have gle : g%:R <= 3 * (k.+1%:R * a) := trunc_block ka1.
set c : R := 4 * a.
have c0 : 0 <= c by rewrite mulr_ge0 // ltW.
have Mc : M%:R <= c ^+ k.+1.
  rewrite /c exprMn aK /M /sat_cap natrM.
  apply: ler_wpM2r; first exact: ler0n.
  rewrite -natrX ler_nat -[4%N]/(2 ^ 2)%N -expnM leq_exp2l //.
  by rewrite mul2n -addnn -addn1 leq_add2l.
rewrite sat_capped_varE.
have C0 : (0 < #|{: clause n.+1 k.+1}|)%N by rewrite card_clause_gt0 // ltnW.
have hV := life_var_le_occ (R := R) C0 [set: {ffun 'I_n.+1 -> bool}] (leqnn M).
have hocc : occ k.+1 (trunc k.+1 M) M [set: {ffun 'I_n.+1 -> bool}] <=
    c * \sum_(j < M.+1) forced_frac (R := R) n k j.
  rewrite /occ mulr_sumr big_ord_recr /=.
  apply: le_trans (_ : \sum_(j < M) c * forced_frac n k j <= _).
    apply: ler_sum => j _; rewrite /forced_frac /tuple_avg -unif_meanZ.
    apply: ler_unif_mean => t.
    by apply: trunc_le_forced => //; exact: ltnW.
  rewrite lerDl mulr_ge0 //.
  by apply: unif_mean_ge0 => t; rewrite divr_ge0.
have hsum : \sum_(j < M.+1) forced_frac (R := R) n k j =
    \sum_(j < M.+1) head_forced n k j.
  by apply: eq_bigr => j _; exact: forced_frac_head.
have hint := integrated_head_forcing k1 kn a0 (root_small n k) hg M.
rewrite -hsum -[M.+1%:R]natr1 in hint.
have t0 : 0 <= 2 ^+ k.+2 :> R by rewrite exprn_ge0.
have mE : M%:R = 2 ^+ k.+2 * n.+1%:R :> R by rewrite /M /sat_cap natrM natrX.
have m1 : 1 <= M%:R :> R.
  by rewrite ler1n /M /sat_cap muln_gt0 expn_gt0.
have e0 : 0 <= a^-1 ^+ k by rewrite exprn_ge0 // invr_ge0 ltW.
have hV' : life_var k.+1 M [set: {ffun 'I_n.+1 -> bool}] <=
    2 * M%:R * (4 * a * \sum_(j < M.+1) forced_frac (R := R) n k j).
  apply: le_trans hV _; apply: ler_wpM2l => //.
  by rewrite mulr_ge0 // ler0n.
have := variance_arith (ltr0Sn R n) (ltW a0) (ler0n _ k.+1) e0 t0 m1 mE
  (root_err n k) gle hV' hint.
rewrite (root_sqr n k) => /le_trans; apply.
by rewrite /C [2 ^+ k.+3]exprS lexx.
Qed.

End sat_variance.

