(* The shape bound for square-free walks.
   Each step symbol of SquareFree.WalkShapeCode gets a weight
   (pmsb_w). With y = 2 (n + 1), the weight of a symbol times
   N^(fresh row) d^(fresh colors) y^(index slots) is N d^2 y^3
   (pmsb_w_comp), and the weights of all symbols sum to 13 N d^2 y^3
   (pmsb_w_sum).
   - pmsb_point: for a terminal walk of length L (pmso_fv N rs = L: L <= 2,
     or no row at a non-root position is visited once), the fresh values
     and the at most 45 e index slots of its code pay for the moment weight
     B^(2e), when N <= d^2 and B^2 y^45 <= d.
   - pmsb_T_le: the sum pmso_T over the terminal walks of length L is at
     most N (13 d^2)^L for L >= 1, when N <= d^2 and B^2 (2L)^45 <= d. The
     root and the code determine the walk (pmsk_inj), and the sum over
     codes factors over the steps.
   - pmsb_S_le: the sum over all valid walks is at most 2 N B^4 (26 d^2)^L
     when also L0 B^2 <= d and B^2 (2 L0)^45 <= d. This is pmso_bound with
     Lam 0 = B^4 and Lam L = 2 N B^4 (13 d^2)^L.
   Natural numbers only. *)
From Stdlib Require Import Lia ArithRing.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import SquareFree.WalkCount SquareFree.WalkExcess
  SquareFree.WalkShapeRecursion SquareFree.WalkShapeOnce
  SquareFree.WalkShapeTwin SquareFree.WalkShapeCode.

(* 1. Weights of the step symbols. *)
Section Weight.
Variables (N d n : nat).

Local Notation y := (2 * n.+1).

Definition pmsb_rw (x : 'I_N + 'I_n.+1) : nat := if x is inl _ then y else N.
Definition pmsb_cw (x : 'I_d + 'I_n.+1 * bool) : nat := if x is inl _ then y else d.

Definition pmsb_w (sy : pmsk_sym N d n) : nat :=
  match sy with
  | inl (inl _, _) => N * d ^ 2 * y ^ 3
  | inl (inr _, _) => N * d ^ 2 * y ^ 2
  | inr (x, c1, c2) => pmsb_rw x * pmsb_cw c1 * pmsb_cw c2
  end.

Lemma pmsb_w_comp (sy : pmsk_sym N d n) :
  pmsb_w sy * (N ^ pmsk_rf N d n sy * d ^ pmsk_cf N d n sy * y ^ pmsk_ix N d n sy) =
  N * d ^ 2 * y ^ 3.
Proof.
case: sy => [[[k|u] b] | [[x c1] c2]];
  last (case: x => ?; case: c1 => [?|[? ?]]; case: c2 => [?|[? ?]]);
  by rewrite /= !expnE /= -!multE -?plusE; ring.
Qed.

Lemma pmsb_w_sum : \sum_(sy : pmsk_sym N d n) pmsb_w sy = 13 * (N * d ^ 2 * y ^ 3).
Proof.
have Hpair (A B : finType) (F : A -> nat) (G : B -> nat) :
    \sum_(p : A * B) F p.1 * G p.2 = (\sum_a F a) * (\sum_b G b).
  rewrite -(pair_bigA _ (fun a b => F a * G b)) big_distrl /=.
  by apply: eq_bigr => a _; rewrite big_distrr.
have Ec : \sum_(i : ('I_3 + 'I_n.+1) * bool) pmsb_w (inl i) =
    2 * (3 * (N * d ^ 2 * y ^ 3) + n.+1 * (N * d ^ 2 * y ^ 2)).
  rewrite (eq_bigr (fun i => pmsb_w (inl (i.1, i.2)))); first by case.
  rewrite -(pair_bigA _ (fun k b => pmsb_w (inl (k, b)))) /=.
  rewrite (eq_bigr (fun k => 2 * pmsb_w (inl (k, true)))).
    by move=> k _; rewrite big_bool /= addnn -mul2n; case: k.
  rewrite -big_distrr /= big_sumType /= !sum_nat_const !card_ord.
  by rewrite mulnC [3 * _]mulnC [n.+1 * _]mulnC.
have Ee : \sum_(i : ('I_N + 'I_n.+1) * ('I_d + 'I_n.+1 * bool) * ('I_d + 'I_n.+1 * bool))
    pmsb_w (inr i) = (\sum_(x : 'I_N + 'I_n.+1) pmsb_rw x) *
    (\sum_(c : 'I_d + 'I_n.+1 * bool) pmsb_cw c) * (\sum_(c : 'I_d + 'I_n.+1 * bool) pmsb_cw c).
  rewrite (eq_bigr (fun i => (pmsb_rw i.1.1 * pmsb_cw i.1.2) * pmsb_cw i.2)).
    by case => [[x c1] c2].
  rewrite (Hpair _ _ (fun p => pmsb_rw p.1 * pmsb_cw p.2) pmsb_cw).
  by rewrite (Hpair _ _ pmsb_rw pmsb_cw).
rewrite big_sumType Ec Ee.
have Er : \sum_(x : 'I_N + 'I_n.+1) pmsb_rw x = N * y + n.+1 * N.
  by rewrite big_sumType /= !sum_nat_const !card_ord mulnC.
have Ecw : \sum_(c : 'I_d + 'I_n.+1 * bool) pmsb_cw c = d * y + n.+1 * 2 * d.
  by rewrite big_sumType /= !sum_nat_const card_prod !card_ord card_bool mulnC.
by rewrite Er Ecw /= !expnE /= -!multE -!plusE; ring.
Qed.

End Weight.

(* 2. One terminal walk. *)
Section Point.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Variables (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).
Variable HW : pmso_valid N d rs ps.
Variable HT : pmso_fv N rs = size rs.
Variables (n B : nat).
Variable Hn : size rs <= n.+1.
Variable HNd : N <= d ^ 2.
Variable HBd : B ^ 2 * (2 * n.+1) ^ 45 <= d.

Local Notation L := (size rs).
Local Notation code := (pmsk_code N d r0 q0 rs ps n).
Local Notation y := (2 * n.+1).

Lemma pmsb_R_pos : 0 < L -> 0 < pmsc_R N rs.
Proof. by move=> HL; rewrite /pmsc_R; apply/card_gt0P; exists (nth r0 rs 0); rewrite inE mem_nth. Qed.

(* The fresh values and index slots of the code pay for B^(2e). *)
Lemma pmsb_comp_le : 0 < L ->
  B ^ (2 * pmsc_e N d rs ps) * (N ^ (pmsc_R N rs - 1) * d ^ pmsc_C d ps *
    y ^ (\sum_(s < L) pmsk_ix N d n (code s))) <= d ^ (2 * L).
Proof.
move=> HL; have HR := pmsb_R_pos HL.
have Hix := pmsk_ix_le N d r0 q0 rs ps HW n HT.
have HV := pmso_valid_bound N d rs ps HW.
set e := pmsc_e N d rs ps; set R := pmsc_R N rs; set C := pmsc_C d ps.
set X := \sum_(s < L) pmsk_ix N d n (code s).
have Hy : 0 < y by rewrite muln_gt0.
have H1 : y ^ X <= y ^ (45 * e) by rewrite leq_pexp2l.
have H2 : N ^ (R - 1) <= (d ^ 2) ^ (R - 1) by case: (R - 1) => [//|k]; rewrite leq_exp2r.
have H3 : B ^ (2 * e) * y ^ (45 * e) <= d ^ e.
  by rewrite !expnM -expnMn; case: (e) => [//|k]; rewrite leq_exp2r.
apply: (@leq_trans (B ^ (2 * e) * ((d ^ 2) ^ (R - 1) * d ^ C * y ^ (45 * e)))).
  by rewrite leq_mul2l; apply/orP; right; rewrite leq_mul // leq_mul.
rewrite mulnCA mulnC mulnA; apply: (@leq_trans (d ^ e * ((d ^ 2) ^ (R - 1) * d ^ C))).
  by rewrite -mulnA leq_mul2r H3 orbT.
rewrite -expnM -!expnD; apply: eq_leq; congr (_ ^ _).
move: HV HR; rewrite /e /pmsc_e -/R -/C -!multE -!minusE -!plusE => /leP HV /leP HR; lia.
Qed.

Lemma pmsb_point : 0 < L ->
  B ^ (2 * pmsc_e N d rs ps) * (N * d ^ 2 * y ^ 3) ^ L <=
  d ^ (2 * L) * \prod_(0 <= s < L) pmsb_w N d n (code s).
Proof.
move=> HL.
have Hp : \prod_(0 <= s < L) (pmsb_w N d n (code s) * (N ^ pmsk_rf N d n (code s) *
    d ^ pmsk_cf N d n (code s) * y ^ pmsk_ix N d n (code s))) = (N * d ^ 2 * y ^ 3) ^ L.
  by rewrite (eq_big_nat _ _ (fun s _ => pmsb_w_comp N d n (code s))) prod_nat_const_nat subn0.
rewrite -Hp big_split /= !big_split /= -!expn_sum !big_mkord.
rewrite (pmsk_sum_rf N d r0 q0 rs ps HW n) (pmsk_sum_cf N d r0 q0 rs ps HW n).
rewrite mulnCA mulnC leq_mul2r; apply/orP; right; exact: pmsb_comp_le HL.
Qed.

End Point.

(* 3. The terminal sum. *)
Theorem pmsb_T_le (N d B L0 L : nat) : 0 < N -> 0 < d -> N <= d ^ 2 -> 0 < L ->
  B ^ 2 * (2 * L) ^ 45 <= d -> pmso_T N d B L0 L <= N * (13 * d ^ 2) ^ L.
Proof.
move=> HN Hd HNd HL HBd; rewrite /pmso_T; case: ifP => // HL0.
pose r0 : 'I_N := Ordinal HN; pose c0 : 'I_d := Ordinal Hd; pose q0 : 'I_d * 'I_d := (c0, c0).
pose n := L.-1; have Hn1 : n.+1 = L by rewrite prednK.
pose M := N * d ^ 2 * (2 * n.+1) ^ 3.
have HM : 0 < M by rewrite /M muln_gt0 muln_gt0 HN /= !expn_gt0 Hd.
pose A := [pred W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d) |
  (pmso_fv N W.1 == L) && pmso_valid N d W.1 W.2].
pose g (W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) :=
  (nth r0 W.1 0, [ffun i : 'I_L => pmsk_code N d r0 q0 W.1 W.2 n i]).
pose G (x : 'I_N * {ffun 'I_L -> pmsk_sym N d n}) :=
  d ^ (2 * L) * \prod_(i : 'I_L) pmsb_w N d n (x.2 i).
have HML : 0 < M ^ L by rewrite expn_gt0 HM.
rewrite -(leq_pmul2l HML) big_distrr /=.
(* Each terminal walk is bounded by the weight of its code. *)
apply: (@leq_trans (\sum_(W | A W) G (g W))).
  rewrite [X in _ <= X]big_mkcond /=; apply: leq_sum => W _.
  rewrite /pmso_w; case HA: (A W); last first.
    move: HA; rewrite inE; case: (pmso_fv N W.1 == L); case: (pmso_valid N d W.1 W.2);
    by rewrite ?muln0 ?mul0n.
  move: HA; rewrite inE => /andP [/eqP HT HW]; rewrite HT HW !mul1n.
  rewrite eqxx /= mul1n /G /g /=.
  have Hs : size W.1 = L by rewrite size_tuple.
  have HT' : pmso_fv N W.1 = size W.1 by rewrite Hs.
  have HBd' : B ^ 2 * (2 * n.+1) ^ 45 <= d by rewrite Hn1.
  have HL' : 0 < size W.1 by rewrite Hs.
  have := pmsb_point N d r0 q0 W.1 W.2 HW HT' n B HNd HBd' HL'.
  move=> H; rewrite Hs in H; rewrite mulnC; apply: leq_trans H _.
  rewrite big_mkord; apply: eq_leq; congr (_ * _).
  by apply: eq_bigr => i _; rewrite ffunE.
(* The root and the code determine the walk. *)
have Hinj : {in A &, injective g}.
  move=> W W'; rewrite !inE => /andP [_ HW] /andP [_ HW'] Hg.
  case: Hg => H0 Hf.
  have Hc s : s < size W.1 ->
      pmsk_code N d r0 q0 W.1 W.2 n s = pmsk_code N d r0 q0 W'.1 W'.2 n s.
    move=> Hs; rewrite size_tuple in Hs.
    have := congr1 (fun f : {ffun 'I_L -> pmsk_sym N d n} => f (Ordinal Hs)) Hf.
    by rewrite !ffunE.
  have HS : size W.1 = size W'.1 by rewrite !size_tuple.
  have HSn : size W.1 <= n.+1 by rewrite size_tuple Hn1.
  have [E1 E2] := pmsk_inj N d n r0 q0 W.1 W'.1 W.2 W'.2 HW HW' HS HSn H0 Hc.
  case: W W' {HW HW' H0 Hf Hc HS HSn} E1 E2 => [t1 t2] [t1' t2'] /= E1 E2.
  by congr (_, _); apply: val_inj.
have E : \sum_(W | A W) G (g W) = \sum_(x in g @: A) G x by rewrite (big_imset _ Hinj).
rewrite E; apply: (@leq_trans (\sum_x G x)).
  by rewrite [X in _ <= X](bigID (mem (g @: A))) /= leq_addr.
(* The sum over all codes factors over the steps. *)
rewrite (eq_bigr (fun x => (fun (r : 'I_N) (k : {ffun 'I_L -> pmsk_sym N d n}) =>
  d ^ (2 * L) * \prod_(i : 'I_L) pmsb_w N d n (k i)) x.1 x.2)) //.
rewrite -(pair_bigA _ (fun (r : 'I_N) (k : {ffun 'I_L -> pmsk_sym N d n}) =>
  d ^ (2 * L) * \prod_(i : 'I_L) pmsb_w N d n (k i))) /=.
rewrite sum_nat_const card_ord -big_distrr /=.
rewrite -(bigA_distr_bigA (fun (i : 'I_L) (j : pmsk_sym N d n) => pmsb_w N d n j)) /=.
rewrite prod_nat_const card_ord pmsb_w_sum -/M.
apply: eq_leq; rewrite (expnMn 13 M L) (expnMn 13 (d ^ 2) L) -(expnM d 2 L).
move: (13 ^ L) (M ^ L) (d ^ (2 * L)) => a b c.
by rewrite -!multE; ring.
Qed.

(* 4. The recursion of pmso_bound, with the terminal bound. *)
Lemma pmsb_arith (N D S B4 : nat) : N <= D -> S <= 4 * D -> 0 < B4 ->
  N * (13 * D) ^ 2 + 2 * (2 * N) * (2 * N * B4 * (13 * D)) + 2 * N * S * (2 * N * B4) <=
  2 * N * B4 * (13 * D) ^ 2.
Proof.
move=> HND HS HB.
have Q1 : N * D * D <= N * B4 * D * D by rewrite !leq_mul2r leq_pmulr ?orbT.
have Q2 : N * N * B4 * D <= N * D * B4 * D by rewrite !leq_mul2r leq_mul2l HND !orbT.
have Q3 : N * N * S * B4 <= N * D * (4 * D) * B4.
  by rewrite leq_mul2r (leq_mul (leq_mul (leqnn N) HND) HS) orbT.
move: Q1 Q2 Q3; rewrite !expnE /= -!multE -!plusE => /leP Q1 /leP Q2 /leP Q3.
by apply/leP; lia.
Qed.

Lemma pmsb_arith1 (N D S B4 : nat) : 0 < N -> 0 < D -> N <= D -> S <= 4 * D -> 0 < B4 ->
  N * (13 * D) + 2 * (2 * N) * B4 + 2 * N * S * B4 <= 2 * N * B4 * (13 * D).
Proof.
move=> HN HD HND HS HB.
have P1 : N * D <= N * B4 * D by rewrite leq_mul2r leq_pmulr ?orbT.
have P2 : N * B4 <= N * B4 * D by rewrite leq_pmulr.
have P3 : N * S * B4 <= N * (4 * D) * B4 by rewrite leq_mul2r leq_mul2l HS !orbT.
by move: P1 P2 P3; rewrite -!multE -!plusE => /leP P1 /leP P2 /leP P3; apply/leP; lia.
Qed.

Definition pmsb_Lam (N d B : nat) (L : nat) : nat :=
  if L is 0 then B ^ 4 else 2 * N * B ^ 4 * (13 * d ^ 2) ^ L.

Theorem pmsb_S_le (N d B L0 L : nat) : 0 < N -> 0 < d -> 0 < B -> N <= d ^ 2 ->
  L0 * B ^ 2 <= d -> B ^ 2 * (2 * L0) ^ 45 <= d ->
  pmso_S N d B L0 L 0 <= 2 * N * B ^ 4 * (26 * d ^ 2) ^ L.
Proof.
move=> HN Hd HB HNd HL0B HBd.
pose r0 : 'I_N := Ordinal HN; pose q0 : 'I_d * 'I_d := (Ordinal Hd, Ordinal Hd).
have HB4 : 0 < B ^ 4 by rewrite expn_gt0 HB.
have HD : 0 < d ^ 2 by rewrite expn_gt0 Hd.
(* The terminal sums. *)
have HT L' : 0 < L' -> pmso_T N d B L0 L' <= N * (13 * d ^ 2) ^ L'.
  move=> HL'; case: (leqP L' L0) => HLL0.
    apply: pmsb_T_le => //; apply: leq_trans HBd.
    by rewrite leq_mul2l leq_exp2r // leq_mul2l HLL0 !orbT.
  by rewrite /pmso_T; case: ifP => // H; move: HLL0; rewrite ltnNge H.
have HS2 : (d + L0 * B ^ 2) ^ 2 <= 4 * d ^ 2.
  have H2 : d + L0 * B ^ 2 <= 2 * d by rewrite mul2n -addnn leq_add2l.
  by apply: leq_trans (_ : (2 * d) ^ 2 <= 4 * d ^ 2); rewrite ?leq_exp2r // expnMn.
(* The empty walk. *)
have H0 : pmso_T N d B L0 0 <= pmsb_Lam N d B 0.
  rewrite /pmso_T /pmsb_Lam leq0n.
  apply: (@leq_trans (\sum_(W : 0.-tuple 'I_N * 0.-tuple ('I_d * 'I_d)) B ^ 4)).
    apply: leq_sum => W _; rewrite /pmso_w.
    have Hs : size W.1 = 0 by rewrite size_tuple.
    case: (_ == _); case: (pmso_valid _ _ _ _); rewrite ?mul0n ?mul1n //.
    by rewrite leq_pexp2l // /pmsc_e Hs muln0 add0n (_ : 4 = 2 * 2) // leq_mul2l leq_subr.
  rewrite (big_pred1 ([tuple], [tuple])) // => W /=; case: W => t1 t2.
  by apply/esym/eqP; congr (_, _); apply: val_inj; apply: size0nil; rewrite size_tuple.
(* Lam dominates the recursion. *)
have HLam L' : 0 < L' -> pmso_T N d B L0 L' + 2 * (2 * N) * pmsb_Lam N d B L'.-1 +
    2 * N * (d + L0 * B ^ 2) ^ 2 * pmsb_Lam N d B L'.-2 <= pmsb_Lam N d B L'.
  case: L' => [//|[|m]] _.
    rewrite /pmsb_Lam /= expn1.
    apply: leq_trans (pmsb_arith1 N (d ^ 2) ((d + L0 * B ^ 2) ^ 2) (B ^ 4) HN HD HNd HS2 HB4).
    by rewrite leq_add2r leq_add2r; have := HT 1 isT; rewrite expn1.
  set K := 13 * d ^ 2; set S := (d + L0 * B ^ 2) ^ 2.
  have Hm : pmsb_Lam N d B m <= 2 * N * B ^ 4 * K ^ m.
    by case: m => [|m'] //=; rewrite expn0 muln1 leq_pmull // muln_gt0 HN.
  apply: (@leq_trans (N * K ^ m.+2 + 2 * (2 * N) * (2 * N * B ^ 4 * K ^ m.+1) +
    2 * N * S * (2 * N * B ^ 4 * K ^ m))).
    rewrite /= leq_add //; first by rewrite leq_add2r HT.
    by rewrite leq_mul2l Hm orbT.
  rewrite /pmsb_Lam -/K.
  have EL : N * K ^ m.+2 + 2 * (2 * N) * (2 * N * B ^ 4 * K ^ m.+1) +
      2 * N * S * (2 * N * B ^ 4 * K ^ m) = K ^ m * (N * K ^ 2 +
      2 * (2 * N) * (2 * N * B ^ 4 * K) + 2 * N * S * (2 * N * B ^ 4)).
    move: (B ^ 4) => B4; rewrite !expnS expn0 muln1; move: (K ^ m) => Km.
    by rewrite -!multE -!plusE; ring.
  have ER : 2 * N * B ^ 4 * K ^ m.+2 = K ^ m * (2 * N * B ^ 4 * K ^ 2).
    move: (B ^ 4) => B4; rewrite !expnS expn0 muln1; move: (K ^ m) => Km.
    by rewrite -!multE; ring.
  rewrite EL ER leq_mul2l; apply/orP; right.
  exact: pmsb_arith N (d ^ 2) S (B ^ 4) HNd HS2 HB4.
have := pmso_bound N d r0 q0 B L0 (pmsb_Lam N d B) H0 HLam L.
move=> H; apply: leq_trans H _.
case: L => [|L'].
  by rewrite /pmsb_Lam !expn0 !muln1 leq_pmull // muln_gt0 HN.
rewrite /pmsb_Lam (_ : 26 * d ^ 2 = 2 * (13 * d ^ 2)); first by rewrite mulnA.
rewrite (expnMn 2 (13 * d ^ 2)); apply: eq_leq.
move: (2 ^ L'.+1) ((13 * d ^ 2) ^ L'.+1) (B ^ 4) => a b c.
by rewrite -!multE; ring.
Qed.
