(* The terminal sum of the sharp NB count, for the lower edge.
   Over any real field. Let lam > 0 with N 'C(d, 2) <= lam^4 and
   0 < theta <= 1. A step symbol y of PaperMainSquarefreeWalkShapeCode gets
   the weight (pmns_w)
     [F y] [c1 < c2] lam^(-(2 rf + cf)) theta^(2 [X y or (Z y after F)]),
   with [F y] [c1 < c2] read as 1 for symbols other than F. A list of
   symbols gets the product of the weights of its steps, where "after F"
   refers to the previous symbol (pmns_pw).
   - pmns_transfer: if every row sum of a step weight is at most mu, the
     weights of all lists of length L sum to at most mu^L.
   - pmns_pw_pot: the potentials 1 (after F) and 1/theta (otherwise) give a
     second weight (pmns_w') with row sums at most 1 + theta (1 + K)
     (pmns_rows), where K bounds the sum of lam^(-(2 rf + cf)) over all
     symbols (pmns_sum_all).
   - pmns_code_ge: for a terminal valid walk with increasing pairs and
     L >= 3, lam^(-2L) B^(2e) is at most the weight of its code, when
     B^2 <= lam theta^294. This uses #X + #FZ <= 147 e
     (PaperMainSquarefreeWalkNBCore) and 2 (R - 1) + C = 2 L - e.
   - pmns_T_le: the terminal sum is at most
     lam^(2L) N (1 + theta (1 + K))^L, since the root and the code
     determine the walk (pmsk_inj). *)
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From EllipsoidFitting Require Import PaperMainSquarefreeWalkCount PaperMainSquarefreeWalkExcess
  PaperMainSquarefreeWalkShapeOnce PaperMainSquarefreeWalkShapeTwin
  PaperMainSquarefreeWalkShapeCode PaperMainSquarefreeWalkNBMarks
  PaperMainSquarefreeWalkNBCore.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Weighted lists and the transfer bound. *)
Section Transfer.
Variables (R : realFieldType) (T : finType) (st : T -> bool).

Fixpoint pmns_pw (w : bool -> T -> R) (x : bool) (cs : seq T) : R :=
  if cs is y :: cs' then w x y * pmns_pw w (st y) cs' else 1.

Lemma pmns_tuple_cons (m : nat) (f : m.+1.-tuple T -> R) :
  \sum_(c : m.+1.-tuple T) f c = \sum_(y : T) \sum_(c : m.-tuple T) f [tuple of y :: c].
Proof.
rewrite (reindex (fun p : T * m.-tuple T => [tuple of p.1 :: p.2])) /=; last first.
  by rewrite -(pair_bigA _ (fun (y : T) (c : m.-tuple T) => f [tuple of y :: c])).
exists (fun t : m.+1.-tuple T => (thead t, [tuple of behead t])) => [[y c] _ | t _].
  by congr (_, _); apply: val_inj.
by apply: val_inj; rewrite /= [in RHS](tuple_eta t).
Qed.

Lemma pmns_pw_ge0 (w : bool -> T -> R) : (forall x y, 0 <= w x y) ->
  forall x cs, 0 <= pmns_pw w x cs.
Proof.
move=> Hw x cs; elim: cs x => [|y cs IH] x /=; first exact: ler01.
by rewrite mulr_ge0.
Qed.

Lemma pmns_transfer (w : bool -> T -> R) (mu : R) : (forall x y, 0 <= w x y) ->
  (forall x, \sum_(y : T) w x y <= mu) -> 0 <= mu ->
  forall m x, \sum_(c : m.-tuple T) pmns_pw w x c <= mu ^+ m.
Proof.
move=> Hw Hrow Hmu m; elim: m => [|m IH] x.
  rewrite (eq_bigr (fun _ => 1)); first by move=> c _; rewrite (tuple0 c).
  by rewrite sumr_const card_tuple expn0 expr0.
rewrite pmns_tuple_cons /=.
apply: (@le_trans _ _ (\sum_(y : T) w x y * mu ^+ m)).
  apply: ler_sum => y _; rewrite -mulr_sumr; apply: ler_wpM2l; [exact: Hw | exact: IH].
by rewrite -mulr_suml exprS; apply: ler_wpM2r; [exact: exprn_ge0 | exact: Hrow].
Qed.

Lemma pmns_pw_pot (w w' : bool -> T -> R) (v : bool -> R) :
  (forall x, 1 <= v x) -> (forall x y, 0 <= w x y) -> (forall x y, 0 <= w' x y) ->
  (forall x y, w x y * v (st y) <= v x * w' x y) ->
  forall x cs, pmns_pw w x cs <= v x * pmns_pw w' x cs.
Proof.
move=> Hv Hw Hw' Hpot x cs; elim: cs x => [|y cs IH] x /=; first by rewrite mulr1 Hv.
apply: (@le_trans _ _ (w x y * (v (st y) * pmns_pw w' (st y) cs))).
  by apply: ler_wpM2l; [exact: Hw | exact: IH].
rewrite mulrA [X in _ <= X]mulrA; apply: ler_wpM2r; last exact: Hpot.
exact: pmns_pw_ge0 Hw' _ _.
Qed.

End Transfer.

Arguments pmns_pw {R T} st w x cs.

(* 2. The weights of the step symbols. *)
Section Weights.
Variables (R : realFieldType) (N d n : nat) (lam theta : R).
Local Notation sym := (pmsk_sym N d n).

Definition pmns_ex (y : sym) : nat := (2 * pmsk_rf N d n y + pmsk_cf N d n y)%N.

Definition pmns_w (x : bool) (y : sym) : R :=
  (if pmnc_F y then (pmnc_Fincr y)%:R else 1) * lam^-1 ^+ pmns_ex y *
  (if pmnc_X y || (pmnc_Z y && x) then theta ^+ 2 else 1).

(* The potentials. *)
Definition pmns_v (x : bool) : R := if x then 1 else theta^-1.

Definition pmns_w' (x : bool) (y : sym) : R := pmns_w x y * pmns_v (pmnc_F y) / pmns_v x.

Lemma pmns_w_ge0 : 0 <= lam -> 0 <= theta -> forall x y, 0 <= pmns_w x y.
Proof.
move=> Hl Ht x y; rewrite /pmns_w.
apply: mulr_ge0; first apply: mulr_ge0.
- by case: (pmnc_F y); rewrite ?ler0n ?ler01.
- by apply: exprn_ge0; rewrite invr_ge0.
- by case: ifP => _; rewrite ?exprn_ge0 ?ler01.
Qed.

Lemma pmns_v_ge1 : 0 < theta <= 1 -> forall x, 1 <= pmns_v x.
Proof.
move=> /andP [Ht0 Ht1] [|] /=; first exact: lexx.
by rewrite invf_ge1.
Qed.

Lemma pmns_w'_ge0 : 0 <= lam -> 0 < theta -> forall x y, 0 <= pmns_w' x y.
Proof.
move=> Hl Ht x y; rewrite /pmns_w'.
have Hv z : 0 <= pmns_v z by case: z => /=; rewrite ?ler01 // invr_ge0 ltW.
apply: mulr_ge0; first apply: mulr_ge0.
- exact: pmns_w_ge0 Hl (ltW Ht) x y.
- exact: Hv.
- by rewrite invr_ge0.
Qed.

Lemma pmns_pot_ok : 0 < theta -> forall x y,
  pmns_w x y * pmns_v (pmnc_F y) <= pmns_v x * pmns_w' x y.
Proof.
move=> Ht x y; rewrite /pmns_w' mulrCA mulrA [X in _ <= X]mulrC mulrA.
have Hv : pmns_v x != 0 by case: x => /=; rewrite ?oner_eq0 // invr_eq0 gt_eqF.
by rewrite [X in _ <= X]mulrAC mulVf // mul1r.
Qed.

(* Sums over the symbols. *)
Lemma pmns_sum_sym (f : sym -> R) : \sum_(y : sym) f y =
  \sum_(k : 'I_3 + 'I_n.+1) \sum_(b : bool) f (inl (k, b)) +
  \sum_(x : 'I_N + 'I_n.+1) \sum_(c1 : 'I_d + 'I_n.+1 * bool) \sum_(c2 : 'I_d + 'I_n.+1 * bool)
    f (inr (x, c1, c2)).
Proof.
rewrite big_sumType /=; congr (_ + _).
  by rewrite pair_bigA; apply: eq_bigr => [[k b]] _.
by rewrite pair_bigA pair_bigA; apply: eq_bigr => [[[x c1] c2]] _.
Qed.

Lemma pmns_sum_F : \sum_(y : sym | pmnc_F y) (pmnc_Fincr y)%:R * lam^-1 ^+ 4 =
  (N * 'C(d, 2))%:R * lam^-1 ^+ 4.
Proof.
rewrite big_mkcond /= pmns_sum_sym.
(* Only explicit symbols with explicit row and colors are F. *)
rewrite [X in X + _]big1 ?add0r; first by move=> k _; rewrite big1.
rewrite big_sumType /= [X in _ + X]big1 ?addr0;
  first by move=> j _; rewrite big1 // => c1 _; rewrite big1.
rewrite (eq_bigr (fun _ => 'C(d, 2)%:R * lam^-1 ^+ 4)); last first.
  by rewrite sumr_const card_ord -[_ *+ N]mulr_natl mulrA -natrM.
move=> i _.
rewrite big_sumType /= [X in _ + X]big1 ?addr0; first by move=> j _; rewrite big1.
rewrite (eq_bigr (fun a : 'I_d => \sum_(b : 'I_d) (a < b)%:R * lam^-1 ^+ 4)).
  by move=> a _; rewrite big_sumType /= [X in _ + X]big1 ?addr0.
(* The increasing pairs number 'C(d, 2). *)
under eq_bigr => a _ do rewrite -mulr_suml.
rewrite -mulr_suml; congr (_ * _).
under eq_bigr => a _ do rewrite -natr_sum.
rewrite -natr_sum; congr (_%:R).
rewrite -pmnm_card_incr big_mkcond /= pair_bigA /=.
by rewrite [RHS]big_mkcond; apply: eq_bigr => [[a b]] _ /=; case: (a < b)%N.
Qed.

Lemma pmns_sum_Z (f : sym -> R) : \sum_(y : sym | pmnc_Z y) f y = f (inl (inl ord0, true)).
Proof.
apply: big_pred1 => y.
case: y => [[[k|j] [|]] | [[x c1] c2]] /=.
- apply/eqP/eqP => [Hk | [->]] //.
  by congr (inl (inl _, true)); apply: val_inj.
- by apply/esym/eqP; case.
- by apply/esym/eqP; case.
- by apply/esym/eqP; case.
- by apply/esym/eqP.
Qed.

Lemma pmns_sum_all (c0 : R) : 0 < lam -> 0 <= c0 -> N%:R <= lam ^+ 2 -> d%:R <= c0 * lam ->
  \sum_(y : sym) lam^-1 ^+ pmns_ex y <=
  (2 * (n + 4))%:R + (n + 2)%:R * (c0 + (2 * n.+1)%:R) ^+ 2.
Proof.
move=> Hl Hc0 HN Hd.
have Hli : 0 < lam^-1 by rewrite invr_gt0.
rewrite pmns_sum_sym; apply: lerD.
  (* The closers: 2 (n + 4) symbols of weight 1. *)
  rewrite (eq_bigr (fun _ => 2%:R)).
    by move=> k _; rewrite big_bool /pmns_ex /= expr0.
  rewrite sumr_const card_sum !card_ord -mulrnA ler_nat.
  by rewrite (addnC 3) addSn -addnS.
(* The explicit symbols: a row factor times two color factors. *)
set A := fun x : 'I_N + 'I_n.+1 => lam^-1 ^+ (2 * (if x is inl _ then 1 else 0))%N.
set Bc := fun c : 'I_d + 'I_n.+1 * bool => lam^-1 ^+ pmsk_cfx d n c.
rewrite (eq_bigr (fun x => \sum_(c1 : 'I_d + 'I_n.+1 * bool)
    \sum_(c2 : 'I_d + 'I_n.+1 * bool) A x * (Bc c1 * Bc c2))).
  move=> x _; apply: eq_bigr => c1 _; apply: eq_bigr => c2 _.
  by rewrite /pmns_ex /A /Bc /= -!exprD; case: x.
have Ef : \sum_(i : 'I_N + 'I_n.+1) \sum_(c1 : 'I_d + 'I_n.+1 * bool)
    \sum_(c2 : 'I_d + 'I_n.+1 * bool) A i * (Bc c1 * Bc c2) =
    (\sum_i A i) * ((\sum_c1 Bc c1) * (\sum_c2 Bc c2)).
  rewrite [RHS]mulr_suml; apply: eq_bigr => i _.
  rewrite [X in _ = _ * X]mulr_suml [RHS]mulr_sumr; apply: eq_bigr => c1 _.
  by rewrite [X in _ = _ * X]mulr_sumr [RHS]mulr_sumr.
rewrite Ef.
have HA0 : 0 <= \sum_i A i by apply: sumr_ge0 => i _; apply: exprn_ge0; rewrite ltW.
have HB0 : 0 <= \sum_c Bc c by apply: sumr_ge0 => c _; apply: exprn_ge0; rewrite ltW.
have HA : \sum_i A i <= (n + 2)%:R.
  rewrite big_sumType /A /= !sumr_const !card_ord muln0 expr0 muln1.
  have -> : (n + 2)%:R = 1 + n.+1%:R :> R by rewrite addn2 -add1n natrD.
  apply: lerD => //.
  by rewrite -mulr_natl exprVn ler_pdivrMr ?exprn_gt0 // mul1r.
have HB : \sum_c Bc c <= c0 + (2 * n.+1)%:R.
  rewrite big_sumType /Bc /= !sumr_const card_prod !card_ord card_bool expr1 expr0.
  apply: lerD; last by rewrite mulnC.
  by rewrite -mulr_natl ler_pdivrMr.
rewrite expr2; apply: ler_pM => //; first exact: mulr_ge0.
by apply: ler_pM.
Qed.

(* The row sums of the potential weight. *)
Lemma pmns_rows (K : R) : 0 < lam -> 0 < theta <= 1 -> (N * 'C(d, 2))%:R <= lam ^+ 4 ->
  \sum_(y : sym) lam^-1 ^+ pmns_ex y <= K ->
  forall x, \sum_(y : sym) pmns_w' x y <= 1 + theta * (1 + K).
Proof.
move=> Hl /andP [Ht0 Ht1] HNM HK x.
have Hli : 0 < lam^-1 by rewrite invr_gt0.
have Hti : 0 < theta^-1 by rewrite invr_gt0.
set vx := (pmns_v x)^-1.
have Hvx : vx = if x then 1 else theta.
  by rewrite /vx /pmns_v; case: ifP => _; rewrite ?invr1 ?invrK.
(* The weights of the three classes. *)
have HwF y : pmnc_F y -> pmns_w' x y = (pmnc_Fincr y)%:R * lam^-1 ^+ 4 * vx.
  move=> HF; rewrite /pmns_w' /pmns_w HF /pmnc_X HF /= /pmns_ex.
  rewrite (pmnc_F_rf N d n y HF) (pmnc_F_cf N d n y HF) /=.
  have -> : pmnc_Z y = false by move: HF; case: y => [[? [|]] | ?].
  by rewrite mulr1 mulr1.
have HwX y : pmnc_X y -> pmns_w' x y = lam^-1 ^+ pmns_ex y * (theta * vx).
  move=> HX; move: (HX); rewrite /pmnc_X => /andP [HnF HnZ].
  rewrite /pmns_w' /pmns_w (negbTE HnF) HX /= mul1r /pmns_v /=.
  rewrite -/(pmns_v x) -/vx expr2 mulrA mulfK ?gt_eqF //.
  by rewrite -mulrA.
have HwZ : pmns_w' x (inl (inl ord0, true)) = (if x then theta else 1).
  rewrite /pmns_w' /pmns_w /= /pmns_ex /= expr0 !mul1r -/(pmns_v x) -/vx Hvx.
  case: x {vx Hvx HwF HwX} => /=; rewrite ?mulr1 ?expr2 ?mulfK ?gt_eqF //.
  by rewrite mul1r mulVf ?gt_eqF.
have HK0 : 0 <= K.
  by apply: le_trans HK; apply: sumr_ge0 => y _; apply: exprn_ge0; rewrite ltW.
have HF1 : (N * 'C(d, 2))%:R * lam^-1 ^+ 4 <= 1.
  by rewrite exprVn ler_pdivrMr ?exprn_gt0 // mul1r.
(* Split by class: F, then the single Z symbol, then X. *)
rewrite (bigID pmnc_F) /= [X in _ + X](bigID pmnc_Z) /=.
have E1 : \sum_(y | pmnc_F y) pmns_w' x y = (N * 'C(d, 2))%:R * lam^-1 ^+ 4 * vx.
  rewrite (eq_bigr (fun y => (pmnc_Fincr y)%:R * lam^-1 ^+ 4 * vx)); first exact: HwF.
  by rewrite -mulr_suml pmns_sum_F.
have E2 : \sum_(y | ~~ pmnc_F y && pmnc_Z y) pmns_w' x y = (if x then theta else 1).
  rewrite (eq_bigl pmnc_Z); first by move=> y; case: y => [? | ?] //=; rewrite andbF.
  by rewrite pmns_sum_Z HwZ.
have E3 : \sum_(y | ~~ pmnc_F y && ~~ pmnc_Z y) pmns_w' x y <= theta * vx * K.
  rewrite (eq_bigr (fun y => lam^-1 ^+ pmns_ex y * (theta * vx))); first exact: HwX.
  rewrite -mulr_suml mulrC; apply: ler_wpM2l.
    by rewrite Hvx; case: (x) {HwF HwX HwZ E1 E2 Hvx}; rewrite ?mulr1 ?mulr_ge0 ?ltW.
  apply: le_trans HK.
  rewrite [X in _ <= X](bigID (fun y => ~~ pmnc_F y && ~~ pmnc_Z y)) /= lerDl.
  by apply: sumr_ge0 => y _; apply: exprn_ge0; rewrite ltW.
rewrite E1 E2.
apply: (le_trans (lerD (lexx _) (lerD (lexx _) E3))).
rewrite Hvx; case: (x) {HwF HwX HwZ E1 E2 E3 Hvx}.
  by rewrite !mulr1 mulrDr mulr1 lerD2r.
rewrite mulrDr mulr1 !addrA; apply: lerD.
  by rewrite addrC lerD2l ler_piMl // ltW.
by rewrite -mulrA ler_piMl ?mulr_ge0 // ltW.
Qed.

End Weights.

Arguments pmns_ex {N d n} y.
Arguments pmns_w {R N d n} lam theta x y.
Arguments pmns_w' {R N d n} lam theta x y.

(* 3. The weight of the code of a terminal walk. *)
Section Code.
Variables (R : realFieldType) (N d n : nat) (lam theta : R).
Local Notation sym := (pmsk_sym N d n).

(* The number of factors theta^2 along a list. *)
Fixpoint pmns_cnt (x : bool) (cs : seq sym) : nat :=
  if cs is y :: cs' then ((pmnc_X y || (pmnc_Z y && x)) + pmns_cnt (pmnc_F y) cs')%N
  else 0%N.

Lemma pmns_pw_eq x cs : all pmnc_Fincr cs ->
  pmns_pw pmnc_F (pmns_w lam theta) x cs =
  lam^-1 ^+ (\sum_(y <- cs) pmns_ex y) * theta ^+ (2 * pmns_cnt x cs).
Proof.
elim: cs x => [|y cs IH] x /=; first by rewrite big_nil !expr0 mulr1.
case/andP => Hy Hcs; rewrite IH // big_cons /pmns_w.
have -> : (if pmnc_F y then (pmnc_Fincr y)%:R else 1) = 1 :> R.
  by case: (pmnc_F y); rewrite // Hy.
rewrite mul1r exprD mulnDr exprD.
(* The two exponent sums differ only in their monoid instance: reflexivity. *)
case: (pmnc_X y || (pmnc_Z y && x)) => /=; rewrite ?muln1 ?muln0 ?expr0 ?mulr1 ?mul1r.
  by rewrite mulrACA; reflexivity.
by rewrite mulrA; reflexivity.
Qed.

Lemma pmns_cnt_map (f : nat -> sym) x k m : pmns_cnt x [seq f i | i <- iota k m] =
  (\sum_(k <= s < k + m)
     (pmnc_X (f s) || (pmnc_Z (f s) && (if s == k then x else pmnc_F (f s.-1)))))%N.
Proof.
elim: m k x => [|m IH] k x; first by rewrite addn0 big_geq.
rewrite /= IH.
rewrite addSnnS [RHS]big_ltn; first by rewrite addnS ltnS leq_addr.
rewrite eqxx; congr (_ + _)%N.
apply: eq_big_nat => s /andP [Hs _].
have Hsk : (s == k) = false by apply/negbTE; rewrite neq_ltn Hs orbT.
by rewrite Hsk; case: eqP => // ->.
Qed.

End Code.

Arguments pmns_cnt {N d n} x cs.

Section Walk.
Variables (R : realFieldType) (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Variables (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).
Variable HW : pmso_valid N d rs ps.
Variable Hinc : pmnm_incr d ps.
Variable HT : pmso_fv N rs = size rs.
Variable H3 : (2 < size rs)%N.
Variable n : nat.
Variable Hn : (size rs <= n.+1)%N.

Local Notation L := (size rs).
Local Notation code := (pmsk_code N d r0 q0 rs ps n).

Lemma pmns_code_cnt : (pmns_cnt true [seq code s | s <- iota 0 L] <= 147 * pmsc_e N d rs ps)%N.
Proof.
apply: leq_trans _ (pmnc_XFZ_le N d r0 q0 rs ps HW Hinc HT H3 n).
have HL0 : (0 < L)%N by apply: ltn_trans H3.
have HZ0 : pmnc_Z (code 0) = false.
  by rewrite (pmnc_code_Z N d r0 q0 rs ps HW Hinc n 0 HL0) /pmsk_closer ltn0.
rewrite pmns_cnt_map add0n.
rewrite -(big_mkord xpredT (fun s => nat_of_bool (pmnc_X (code s)))).
rewrite -(big_mkord xpredT (fun s => nat_of_bool
  [&& (s.+1 < L)%N, pmnc_F (code s) & pmnc_Z (code s.+1)])).
apply: (@leq_trans (\sum_(0 <= s < L) (pmnc_X (code s) +
    (pmnc_Z (code s) && (if s == 0%N then true else pmnc_F (code s.-1)))))%N).
  by apply: leq_sum => s _; case: (pmnc_X _); case: (pmnc_Z _ && _).
rewrite big_split /= leq_add2l.
(* Position 0 is not a closer; shift the rest by one. *)
rewrite big_ltn // eqxx HZ0 add0n big_add1 /=.
apply: (leq_trans _ (pmnm_sum_nat_le _ _ _ (leq_pred L))).
rewrite big_nat_cond [X in (_ <= X)%N]big_nat_cond.
apply: leq_sum => i /andP [/andP [_ Hi] _].
have Hi1 : (i.+1 < L)%N by rewrite -ltn_predRL.
by rewrite Hi1 andbC.
Qed.

(* The weight of a terminal walk is at most the weight of its code. *)
Lemma pmns_code_ge (lam theta : R) (B : nat) : 0 < lam -> 0 < theta <= 1 ->
  (B ^ 2)%:R <= lam * theta ^+ 294 ->
  lam^-1 ^+ (2 * L) * (B ^ (2 * pmsc_e N d rs ps))%:R <=
  pmns_pw pmnc_F (pmns_w lam theta) true [seq code s | s <- iota 0 L].
Proof.
move=> Hl /andP [Ht0 Ht1] HB.
set e := pmsc_e N d rs ps.
set cs := [seq code s | s <- iota 0 L].
have Hall : all pmnc_Fincr cs.
  apply/allP => y /mapP [s]; rewrite mem_iota add0n => /andP [_ Hs] ->.
  exact: pmnc_code_Fincr N d r0 q0 rs ps HW Hinc n s Hs.
rewrite pmns_pw_eq //.
(* The code exponent is 2 L - e. *)
have Hex : (\sum_(y <- cs) pmns_ex y + e = 2 * L)%N.
  rewrite -(pmnc_weight_exp N d r0 q0 rs ps HW HT H3 n) /cs big_map; congr (_ + _)%N.
  by rewrite -(big_mkord xpredT (fun s => pmns_ex (code s))) /index_iota subn0.
have Hc := pmns_code_cnt.
have Hli : 0 < lam^-1 by rewrite invr_gt0.
rewrite -Hex exprD -mulrA; apply: ler_wpM2l; first by apply: exprn_ge0; rewrite ltW.
(* lam^(-e) B^(2e) <= theta^(294 e) <= theta^(2 cnt). *)
have HBe : (B ^ (2 * e))%:R = ((B ^ 2)%:R) ^+ e :> R by rewrite expnM natrX.
rewrite HBe -exprMn.
apply: (@le_trans _ _ (theta ^+ (294 * e))); last first.
  apply: ler_wiXn2l; [exact: ltW | exact: Ht1 |].
  by rewrite (_ : 294 = 2 * 147)%N // -mulnA leq_mul2l Hc orbT.
rewrite exprM; apply: lerXn2r.
- by rewrite nnegrE; apply: mulr_ge0; [exact: ltW | exact: ler0n].
- by rewrite nnegrE; apply: exprn_ge0; exact: ltW.
- by rewrite ler_pdivrMl.
Qed.

End Walk.

(* 4. The terminal sum. With n = L - 1 for the code indices. *)
Theorem pmns_T_le (R : realFieldType) (N d B L : nat) (q0 : 'I_d * 'I_d) (ms : seq bool)
    (lam theta c0 : R) :
  (0 < N)%N -> (2 < L)%N -> 0 < lam -> 0 < theta <= 1 -> 0 <= c0 ->
  (N * 'C(d, 2))%:R <= lam ^+ 4 -> N%:R <= lam ^+ 2 -> d%:R <= c0 * lam ->
  (B ^ 2)%:R <= lam * theta ^+ 294 ->
  (pmnm_T N d q0 B L ms)%:R <=
  lam ^+ (2 * L) * N%:R *
  (1 + theta * (1 + ((2 * (L.-1 + 4))%:R + (L.-1 + 2)%:R * (c0 + (2 * L)%:R) ^+ 2))) ^+ L.
Proof.
move=> HN HL3 Hl Ht Hc0 HNM HN2 Hd HB.
have HL0 : (0 < L)%N by apply: ltn_trans HL3.
pose r0 : 'I_N := Ordinal HN.
pose n := L.-1.
have Hn1 : n.+1 = L by rewrite /n prednK.
set K := (2 * (L.-1 + 4))%:R + (L.-1 + 2)%:R * (c0 + (2 * L)%:R) ^+ 2.
set mu := 1 + theta * (1 + K).
(* The row sums and the transfer bound. *)
have HK : \sum_(y : pmsk_sym N d n) lam^-1 ^+ pmns_ex y <= K.
  by have := pmns_sum_all R N d n lam c0 Hl Hc0 HN2 Hd; rewrite Hn1.
have Hrow := pmns_rows R N d n lam theta K Hl Ht HNM HK.
have Ht0 : 0 < theta by case/andP: Ht.
have Hw0 := pmns_w_ge0 R N d n lam theta (ltW Hl) (ltW Ht0).
have Hw'0 := pmns_w'_ge0 R N d n lam theta (ltW Hl) Ht0.
have HK0 : 0 <= K.
  by apply: le_trans HK; apply: sumr_ge0 => y _; apply: exprn_ge0; rewrite invr_ge0 ltW.
have Hmu0 : 0 <= mu.
  rewrite /mu; apply: addr_ge0; first exact: ler01.
  apply: mulr_ge0; first exact: ltW.
  by apply: addr_ge0; [exact: ler01 | exact: HK0].
have Htr := pmns_transfer R (pmsk_sym N d n) pmnc_F (pmns_w' lam theta) mu Hw'0 Hrow Hmu0
  L true.
(* Each terminal walk is bounded through its root and its code. *)
pose A := [pred W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d) |
  [&& pmso_fv N W.1 == L, pmso_valid N d W.1 W.2 & pmnm_incr d W.2]].
have Hsz (W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) :
    size [seq pmsk_code N d r0 q0 W.1 W.2 n s | s <- iota 0 L] == L.
  by rewrite size_map size_iota.
pose g (W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) : 'I_N * L.-tuple (pmsk_sym N d n) :=
  (nth r0 W.1 0, Tuple (Hsz W)).
pose G (x : 'I_N * L.-tuple (pmsk_sym N d n)) : R :=
  lam ^+ (2 * L) * pmns_pw pmnc_F (pmns_w' lam theta) true x.2.
have HG0 x : 0 <= G x.
  by apply: mulr_ge0; [apply: exprn_ge0; exact: ltW | exact: pmns_pw_ge0].
have Hpw (W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) : A W ->
    (B ^ (2 * pmsc_e N d W.1 W.2))%:R <= G (g W).
  rewrite inE => /and3P [/eqP Hf HW Hinc].
  have Hs : size W.1 = L by rewrite size_tuple.
  have HT : pmso_fv N W.1 = size W.1 by rewrite Hs.
  have H3' : (2 < size W.1)%N by rewrite Hs.
  have Hge := pmns_code_ge R N d r0 q0 W.1 W.2 HW Hinc HT H3' n lam theta B Hl Ht HB.
  rewrite Hs in Hge.
  have Hpot := pmns_pw_pot R (pmsk_sym N d n) pmnc_F (pmns_w lam theta) (pmns_w' lam theta)
    (pmns_v R theta) (pmns_v_ge1 R theta Ht) Hw0 Hw'0 (pmns_pot_ok R N d n lam theta Ht0)
    true [seq pmsk_code N d r0 q0 W.1 W.2 n s | s <- iota 0 L].
  rewrite /= mul1r in Hpot.
  rewrite /G /g /=.
  apply: (@le_trans _ _
    (lam ^+ (2 * L) * (lam^-1 ^+ (2 * L) * (B ^ (2 * pmsc_e N d W.1 W.2))%:R))).
    by rewrite mulrA -exprMn divff ?gt_eqF // expr1n mul1r.
  apply: ler_wpM2l; first by apply: exprn_ge0; exact: ltW.
  exact: le_trans Hge Hpot.
(* The root and the code determine the walk. *)
have Hinj : {in A &, injective g}.
  move=> W W'; rewrite !inE => /and3P [_ HW _] /and3P [_ HW' _] Hg.
  case: Hg => H0 Hc.
  have Hcs s : (s < size W.1)%N ->
      pmsk_code N d r0 q0 W.1 W.2 n s = pmsk_code N d r0 q0 W'.1 W'.2 n s.
    move=> Hs; rewrite size_tuple in Hs.
    have := congr1 (fun l => nth (pmsk_code N d r0 q0 W.1 W.2 n 0) l s) Hc.
    by rewrite /= !(nth_map 0) ?size_iota // nth_iota.
  have HS : size W.1 = size W'.1 by rewrite !size_tuple.
  have HSn : (size W.1 <= n.+1)%N by rewrite size_tuple Hn1.
  have [E1 E2] := pmsk_inj N d n r0 q0 W.1 W'.1 W.2 W'.2 HW HW' HS HSn H0 Hcs.
  case: W W' {HW HW' H0 Hc Hcs HS HSn} E1 E2 => [t1 t2] [t1' t2'] /= E1 E2.
  by congr (_, _); apply: val_inj.
apply: (@le_trans _ _ (\sum_(W in A) G (g W))).
  rewrite /pmnm_T natr_sum [X in _ <= X]big_mkcond /=; apply: ler_sum => W _.
  case HA: (W \in A).
    have HA' : A W by [].
    move: (HA'); rewrite inE => /and3P [/eqP Hf HW Hinc].
    apply: le_trans (Hpw W HA'); rewrite Hf eqxx mul1n /pmnm_w HW Hinc /= ler_nat.
    by case: (pmnm_nb _ _ _ _); rewrite ?mul1n ?mul0n.
  move: HA; rewrite inE /pmnm_w.
  by case: (pmso_fv N W.1 == L); case: (pmso_valid _ _ _ _); case: (pmnm_incr _ _);
    rewrite //= ?andbF ?mul0n ?muln0.
(* Sum over all roots and codes. *)
rewrite -(big_imset _ Hinj) /=.
apply: (@le_trans _ _ (\sum_x G x)).
  rewrite [X in _ <= X](bigID (mem (g @: A))) /= lerDl.
  by apply: sumr_ge0 => x _; exact: HG0.
rewrite -(pair_bigA _ (fun (r : 'I_N) (c : L.-tuple (pmsk_sym N d n)) => G (r, c))) /=.
rewrite /G /= sumr_const card_ord -mulr_sumr -[_ *+ N]mulr_natl mulrCA mulrA.
apply: ler_wpM2l; last exact: Htr.
by apply: mulr_ge0; [apply: exprn_ge0; exact: ltW | exact: ler0n].
Qed.
