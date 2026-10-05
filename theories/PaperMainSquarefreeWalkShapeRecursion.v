(* The position recursion of the shape count (G16, checkpoint B4, item 1).
   In the shape count of the square-free walks, a walk W of length L whose
   first removable row sits at position j reduces to a walk of length L - 1
   or L - 2 whose first removable row sits at position j - 1 or later. For
   the weighted sums S L k over the walks of length L whose first removable
   row is at position k or later, this gives
     S L k <= T L + sum_(k <= j < L) (a S (L-1) (j-1) + b S (L-2) (j-1)),
   with T L the sum over the walks without a removable row. Since the
   reduced position cannot drop by more than one, the sum over j costs only
   a factor 2^(L - k) (pmsr_bound):
     S L k <= Lam L * 2^(L - k)   whenever   T L + 2 a Lam (L-1) + b Lam (L-2) <= Lam L.
   Pure arithmetic on natural numbers. *)
From mathcomp Require Import all_ssreflect_compat.

(* 1. Geometric sums. *)
Lemma pmsr_geom (L k : nat) : k <= L -> \sum_(k <= j < L) 2 ^ (L - j) <= 2 ^ (L - k).+1.
Proof.
move=> HkL; have [m Hm] := ubnP (L - k); elim: m k HkL Hm => // m IH k HkL Hm.
case: (ltngtP k L) HkL => [HkL _ | // | -> _]; last by rewrite big_geq.
rewrite big_ltn // expnS mul2n -addnn leq_add2l.
have -> : (L - k = (L - k.+1).+1)%N by rewrite subnSK.
apply: IH => //; move: Hm; rewrite ltnS => Hm.
by apply: leq_trans Hm; rewrite subnS ltn_predL subn_gt0.
Qed.

Lemma pmsr_geom1 (L k : nat) : k <= L -> \sum_(k <= j < L) 2 ^ (L.-1 - j) <= 2 ^ (L - k).
Proof.
move=> HkL; rewrite -(leq_pmul2l (isT : 0 < 2)) big_distrr /= -expnS.
apply: leq_trans _ (pmsr_geom L k HkL).
rewrite big_nat [X in _ <= X]big_nat; apply: leq_sum => j /andP [_ HjL].
have HL : 0 < L by exact: leq_ltn_trans (leq0n j) HjL.
rewrite -expnS -subSn ?prednK //.
by rewrite -ltnS prednK.
Qed.

(* 2. The recursion. *)
Section Recursion.
Variables (S : nat -> nat -> nat) (T Lam : nat -> nat) (a b : nat).

Variable HS : forall L k, k <= L ->
  S L k <= T L + \sum_(k <= j < L) (a * S L.-1 j.-1 + b * S L.-2 j.-1).
Variable HLam0 : T 0 <= Lam 0.
Variable HLam : forall L, 0 < L -> T L + 2 * a * Lam L.-1 + b * Lam L.-2 <= Lam L.

Theorem pmsr_bound L k : k <= L -> S L k <= Lam L * 2 ^ (L - k).
Proof.
have [M HM] := ubnP L; elim: M L k HM => // M IH L k HLM HkL.
apply: leq_trans (HS L k HkL) _.
case: L HLM HkL => [|L] HLM HkL.
  by move: HkL; rewrite leqn0 => /eqP ->; rewrite big_geq // addn0 expn0 muln1.
have HLM' : L < M by exact: HLM.
have H1 j : j < L.+1 -> S L j.-1 <= Lam L * 2 ^ (L.+1 - j).
  move=> HjL; apply: leq_trans (IH L j.-1 HLM' _) _.
    by rewrite (leq_trans (leq_pred j)).
  rewrite leq_mul2l leq_pexp2l ?orbT //.
  by case: j HjL => [|j] HjL; rewrite ?subn0 ?leqnSn // subSS.
have H2 j : j < L.+1 -> S L.-1 j.-1 <= Lam L.-1 * 2 ^ (L - j).
  move=> HjL; apply: leq_trans (IH L.-1 j.-1 _ _) _.
  - by apply: leq_ltn_trans HLM'; exact: leq_pred.
  - by rewrite -!subn1 leq_sub2r.
  rewrite leq_mul2l leq_pexp2l ?orbT //.
  case: j HjL => [|j] HjL /=; first by rewrite !subn0 leq_pred.
  by rewrite subnS -!subn1 subnAC.
apply: (@leq_trans (T L.+1 + \sum_(k <= j < L.+1)
    (a * (Lam L * 2 ^ (L.+1 - j)) + b * (Lam L.-1 * 2 ^ (L - j))))).
  rewrite leq_add2l big_nat [X in _ <= X]big_nat; apply: leq_sum => j /andP [_ Hj].
  by apply: leq_add; rewrite leq_mul2l ?H1 ?H2 ?orbT.
rewrite big_split /= -!big_distrr /= !mulnA.
have G1 := pmsr_geom L.+1 k HkL.
have G2 := pmsr_geom1 L.+1 k HkL.
rewrite /= in G2.
apply: (@leq_trans ((T L.+1 + 2 * a * Lam L + b * Lam L.-1) * 2 ^ (L.+1 - k))); last first.
  by rewrite leq_mul2r (HLam L.+1 (ltn0Sn L)) orbT.
rewrite !mulnDl -addnA; apply: leq_add.
  by rewrite leq_pmulr // expn_gt0.
apply: leq_add.
  by rewrite !mul0n addn0 -mulnDr addnn -mul2n -expnS leq_mul2l G1 orbT.
by rewrite leq_mul2l G2 orbT.
Qed.

End Recursion.
