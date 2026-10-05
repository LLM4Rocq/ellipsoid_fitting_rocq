(* Every fixed power of the walk length is eventually below d.
   The walk length is L(d) = 2^(k+3) with k = log2 (log2 d) (pmel_L of
   PaperMainSquarefreeEdgeUpperLimit), so L(d) <= 8 log2 d
   (pmlg_walk_length_bound). With m^2 <= 2^m for m >= 4 (pmlg_square_exp)
   and its consequence A l^k <= 2^l for large l (pmlg_poly_exp), this gives
   pmlg_eventual: for all A and k, A L(d)^k <= d for every large d, from the
   explicit threshold pmlg_threshold A k on. Natural numbers only. *)
From Stdlib Require Import Lia PeanoNat.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import PaperMainSquarefreeEdgeUpperLimit.
Local Open Scope nat_scope.

Lemma pmlg_square_exp m : 4 <= m -> m^2 <= 2^m.
Proof.
elim: m=>[//|m IH] Hm.
case: (ltngtP m 3)=>[Hlt|Hgt|->] //.
- by move: Hm; rewrite ltnS leqNgt Hlt.
- have HH := IH Hgt.
  rewrite (expnS 2 m); apply: (@leq_trans (2 * m^2)); last exact: leq_mul (leqnn 2) HH.
  rewrite !expnS expn0 !muln1; apply/ssrnat.leP.
  have Hm3 : Nat.le 3 m by exact/ssrnat.leP/ltnW.
  rewrite -!multE; nia.
Qed.

Lemma pmlg_linear_exp A m : 4 <= m -> 2 * A <= m -> A * (m+1) <= 2^m.
Proof.
move=>Hm HAm; apply: (@leq_trans (m^2)); last exact: pmlg_square_exp.
rewrite expnS expn1; apply/ssrnat.leP.
have Hm4 : Nat.le 4 m by exact/ssrnat.leP.
have HA : Nat.le (2 * A) m by exact/ssrnat.leP.
rewrite -!multE -!plusE in HA |-  * ; nia.
Qed.

Lemma pmlg_poly_exp A k l :
  (k+1) * maxn 4 (maxn (2 * (k+1)) A) <= l -> A * l^k <= 2^l.
Proof.
move=>Hl.
pose m := l %/ (k+1).
have Hk : 0 < k+1 by rewrite addn1.
have Hm : maxn 4 (maxn (2 * (k+1)) A) <= m.
{ by rewrite /m leq_divRL // mulnC. }
have Hm4 := leq_trans (leq_maxl _ _) Hm.
have Hm2 := leq_trans (leq_maxl _ _) (leq_trans (leq_maxr _ _) Hm).
have HmA := leq_trans (leq_maxr _ _) (leq_trans (leq_maxr _ _) Hm).
have Hlm : l <= (k+1) * m.+1.
{ rewrite /m mulnC; exact: ltnW (ltn_ceil _ Hk). }
have HlExp : l <= 2^m.
{ have HH := pmlg_linear_exp (k+1) m Hm4 Hm2.
  rewrite !addn1 in HH Hlm; exact (leq_trans Hlm HH). }
have HAE : A <= 2^m.
{ apply: leq_trans HmA _; apply: leq_trans (leqnSn m) _.
  by apply: ltn_expl. }
have Hpow : l^k <= (2^m)^k by case Ek: k => [|j]; rewrite ?expn0 ?leq_exp2r //.
apply: leq_trans (leq_mul HAE Hpow) _.
rewrite -expnM -expnD leq_exp2l //.
have Hblock : (k+1) * m <= l by rewrite /m mulnC leq_divM.
apply: leq_trans _ Hblock; apply/ssrnat.leP.
rewrite -!multE -!plusE; nia.
Qed.

Lemma pmlg_walk_length_bound d : 2 <= d -> pmel_L d <= 8 * trunc_log 2 d.
Proof.
move=>Hd; pose l := trunc_log 2 d.
have Hl : 0 < l.
{ rewrite lt0n; apply/eqP=> Hl0.
  have HH : d < 2^l.+1 by exact: trunc_log_ltn.
  by rewrite Hl0 /= ltnNge Hd in HH. }
have Hk1 : 2^(trunc_log 2 l) <= l by exact: trunc_logP.
rewrite /pmel_L /pmel_k -/l.
by rewrite (expnS 2 (trunc_log 2 l).+2) (expnS 2 (trunc_log 2 l).+1)
 (expnS 2 (trunc_log 2 l)) !mulnA leq_mul2l Hk1 orbT.
Qed.

Definition pmlg_threshold A k :=
  2 ^ (maxn 1 ((k+1) * maxn 4 (maxn (2 * (k+1)) (A * 8^k)))).

Lemma pmlg_threshold_bound A k d : pmlg_threshold A k <= d -> A * (pmel_L d)^k <= d.
Proof.
move=>Hd.
pose q := maxn 1 ((k+1) * maxn 4 (maxn (2 * (k+1)) (A * 8^k))).
have Hq : 1 <= q by exact: leq_maxl.
have Hd2 : 2 <= d.
{ apply: leq_trans _ Hd; change (2^1 <= 2^q); by rewrite leq_exp2l. }
have Hd0 : 0 < d by exact: leq_trans (isT : 0 < 2) Hd2.
pose l := trunc_log 2 d.
have Hld : 2^l <= d by exact: trunc_logP.
have Hlt : d < 2^l.+1 by exact: trunc_log_ltn.
have Hql : q <= l.
{ rewrite -ltnS -(ltn_exp2l _ _ (isT : 1 < 2)); exact: leq_ltn_trans Hd Hlt. }
have Hpoly : (A * 8^k) * l^k <= 2^l.
{ apply: pmlg_poly_exp; exact: leq_trans (leq_maxr _ _) Hql. }
have HL := pmlg_walk_length_bound d Hd2.
have Hpow : (pmel_L d)^k <= (8 * l)^k.
{ by case Ek: k => [|j]; rewrite ?expn0 ?leq_exp2r //. }
apply: leq_trans (leq_mul (leqnn A) Hpow) _.
rewrite expnMn mulnA; exact: leq_trans Hpoly Hld.
Qed.

Theorem pmlg_eventual A k : exists D, forall d, D <= d -> A * (pmel_L d)^k <= d.
Proof. exists (pmlg_threshold A k); exact: pmlg_threshold_bound. Qed.
