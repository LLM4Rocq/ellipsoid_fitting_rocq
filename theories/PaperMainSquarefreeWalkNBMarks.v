(* Marked walks for the sharp non-backtracking count of the lower spectral
   edge. A closed walk (rs, ps) of PaperMainSquarefreeWalkShapeOnce carries
   marks ms (one per row position). It is ms-NB when consecutive label
   pairs differ except at marked rows (pmnm_nb), and its pairs are
   increasing (pmnm_incr). For the trace of a power of a non-backtracking
   matrix the marks are the junction rows.
   - pmnm_mark_once: a non-root row visited once sits at a mark, because
     parity makes its two pairs equal.
   - The contraction of PaperMainSquarefreeWalkShapeOnce at a mark keeps
     the walk NB for the marks with that position deleted
     (pmnm_contract_nb); the excursion keeps it NB once the merge row is
     marked (pmnm_exc_nb).
   - One reduction at the first removable row j, with weight B^(2e)
     (pmnm_step_c, pmnm_step_e). A contraction costs a factor N. An
     excursion costs N ('C(d, 2) + 2 L d B^4): the removed pair is
     increasing, so there is no orientation factor 2.
   - The resulting recursion and its solution, pmnm_solve and pmnm_count,
     are described before section 4. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import PaperMainSquarefreeWalkCount PaperMainSquarefreeWalkExcess
  PaperMainSquarefreeWalkShapeOnce.

(* 1. Marks, increasing pairs and the NB condition. *)
Definition pmnm_succ (n t : nat) : nat := if t.+1 < n then t.+1 else 0.

Section Marks.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)) (ms : seq bool).

Definition pmnm_incr ps : bool := all (fun p : 'I_d * 'I_d => (p.1 < p.2)%N) ps.

(* The row between step t and step t+1 is at position succ t. *)
Definition pmnm_nb ms ps : bool :=
  all (fun t => nth false ms (pmnm_succ (size ps) t) ||
    (nth q0 ps t != nth q0 ps (pmnm_succ (size ps) t))) (iota 0 (size ps)).

Lemma pmnm_nbP ms ps : reflect (forall t, t < size ps -> nth false ms (pmnm_succ (size ps) t) ||
    (nth q0 ps t != nth q0 ps (pmnm_succ (size ps) t))) (pmnm_nb ms ps).
Proof.
apply: (iffP allP) => H t.
  by move=> Ht; apply: H; rewrite mem_iota add0n Ht.
by rewrite mem_iota add0n => /andP [_ Ht]; exact: H.
Qed.

Lemma pmnm_incr_nth ps t : pmnm_incr ps -> t < size ps -> (nth q0 ps t).1 < (nth q0 ps t).2.
Proof. by move=> /allP H Ht; exact: H (mem_nth q0 Ht). Qed.

(* An increasing pair is its own only increasing orientation. *)
Lemma pmnm_orient_incr (p q : 'I_d * 'I_d) b : p.1 < p.2 -> q.1 < q.2 ->
  p = pmso_orient d b q -> p = q.
Proof.
move=> Hp Hq; case: b => //= E; rewrite E /= in Hp.
by have := ltn_trans Hp Hq; rewrite ltnn.
Qed.

Lemma pmnm_mark_once rs ps ms j : pmso_valid N d rs ps -> pmnm_nb ms ps -> pmnm_incr ps ->
  2 < size rs -> 0 < j < size rs -> count_mem (nth r0 rs j) rs = 1 -> nth false ms j.
Proof.
move=> HW Hnb Hinc H2 Hj Hv.
have Hs : size ps = size rs by move: HW => /and4P [/eqP].
have Hor : nth q0 ps j = pmso_orient d (nth q0 ps j == nth q0 ps j.-1) (nth q0 ps j.-1).
  case: (eqVneq (nth r0 rs j.-1) (nth r0 rs (pmso_succ N j rs))) => Hk.
  - by have [_ _ _ H] := pmso_excursion N d r0 q0 rs ps j HW H2 Hj Hv Hk.
  - by have [_ _ _ H] := pmso_contract N d r0 q0 rs ps j HW H2 Hj Hv Hk.
case/andP: Hj => Hj0 Hjr.
have Hjp : j < size ps by rewrite Hs.
have Hj1 : j.-1 < size ps by apply: leq_ltn_trans Hjp; exact: leq_pred.
have E : nth q0 ps j = nth q0 ps j.-1.
  exact: pmnm_orient_incr (pmnm_incr_nth _ _ Hinc Hjp) (pmnm_incr_nth _ _ Hinc Hj1) Hor.
move/pmnm_nbP: Hnb => /(_ j.-1 Hj1).
have -> : pmnm_succ (size ps) j.-1 = j by rewrite /pmnm_succ prednK // Hjp.
by rewrite E eqxx orbF.
Qed.

(* 2. Reductions keep the NB condition. *)
Definition pmnm_exc_ms j ms : seq bool :=
  if j.+1 < size ms then set_nth false (pmso_del j (pmso_del j ms)) j.-1 true
  else set_nth false (pmso_del j.-1 (pmso_del j.-1 ms)) 0 true.

Lemma pmnm_contract_nb ms ps j : size ms = size ps -> 2 < size ps -> 0 < j < size ps ->
  nth q0 ps j = nth q0 ps j.-1 -> pmnm_nb ms ps -> pmnm_nb (pmso_del j ms) (pmso_del j ps).
Proof.
move=> Hsz H2 /andP [Hj0 Hj] E /pmnm_nbP H; apply/pmnm_nbP => t.
rewrite pmso_size_del // => Ht.
set n := size ps in Hsz H2 Hj H Ht *.
have Hn : n.-1.+1 = n by rewrite prednK // (leq_trans _ H2).
rewrite /pmnm_succ.
(* Before the merged step. *)
case: (ltnP t.+1 j) => Htj.
  have Htn : t.+1 < n.-1 by apply: leq_trans Htj _; rewrite -ltnS Hn.
  rewrite Htn !(pmso_nth_del _ j) // ?(ltn_trans (ltnSn t) Htj) //.
  have Htn1 : t < n by apply: (ltn_trans Ht); rewrite -{2}Hn ltnSn.
  have := H t Htn1.
  by rewrite /pmnm_succ (ltn_trans Htj Hj).
(* The merged step carries the pair of step j. *)
case: (eqVneq t.+1 j) => Htj'.
  have Htj1 : t < j by rewrite -Htj'.
  rewrite (pmso_nth_del _ j t) //.
  have Ej1 : t = j.-1 by rewrite -Htj'.
  have := H j Hj; rewrite /pmnm_succ E -Ej1 -Htj'.
  have Heq : (t.+2 < n) = (t.+1 < n.-1) by rewrite -[in RHS](ltn_add2r 1) !addn1 Hn.
  rewrite Heq; case: ifP => _.
    by rewrite !(pmso_nth_del_ge _ t.+1).
  by rewrite !(pmso_nth_del _ t.+1 0).
(* After the merged step. *)
have Hjt : j <= t by rewrite -ltnS ltn_neqAle eq_sym Htj' Htj.
rewrite (pmso_nth_del_ge _ j t) //.
have Ht1 : t.+1 < n by rewrite -Hn ltnS.
have Heq : (t.+2 < n) = (t.+1 < n.-1) by rewrite -[in RHS](ltn_add2r 1) !addn1 Hn.
have := H t.+1 Ht1; rewrite /pmnm_succ Heq.
case: ifP => _.
  by rewrite !(pmso_nth_del_ge _ j) // (leq_trans Hjt).
by rewrite !(pmso_nth_del _ j 0).
Qed.

Lemma pmnm_exc_nb ms ps j : size ms = size ps -> 2 < size ps -> 0 < j < size ps ->
  pmnm_nb ms ps -> pmnm_nb (pmnm_exc_ms j ms) (pmso_del j.-1 (pmso_del j.-1 ps)).
Proof.
move=> Hsz H2 /andP [Hj0 Hj] /pmnm_nbP H; apply/pmnm_nbP => t.
set n := size ps in Hsz H2 Hj H *.
have [m Hm] : exists m, n = m.+3 by exists (n - 3); rewrite -addn3 subnK.
have Hj1 : j.-1 < n by rewrite (leq_ltn_trans (leq_pred j) Hj).
have Hsz1 : size (pmso_del j.-1 ps) = m.+2 by rewrite pmso_size_del // -/n Hm.
have Hj2 : j.-1 < m.+2 by rewrite -ltnS prednK // -Hm.
have Hsz2 : size (pmso_del j.-1 (pmso_del j.-1 ps)) = m.+1 by rewrite pmso_size_del Hsz1.
rewrite Hsz2 => Ht.
(* Entries of the shortened lists. *)
have Ep i : nth q0 (pmso_del j.-1 (pmso_del j.-1 ps)) i =
    if i < j.-1 then nth q0 ps i else nth q0 ps i.+2.
  case: ifP => Hi; first by rewrite !(pmso_nth_del _ j.-1).
  have Hji : j.-1 <= i by rewrite leqNgt Hi.
  rewrite (pmso_nth_del_ge _ j.-1 i) // (pmso_nth_del_ge _ j.-1 i.+1) //.
  exact: leq_trans Hji (leqnSn _).
have Ed (s : seq bool) k i : nth false (pmso_del k (pmso_del k s)) i =
    if i < k then nth false s i else nth false s i.+2.
  case: ifP => Hi; first by rewrite !(pmso_nth_del _ k).
  have Hki : k <= i by rewrite leqNgt Hi.
  rewrite (pmso_nth_del_ge _ k i) // (pmso_nth_del_ge _ k i.+1) //.
  exact: leq_trans Hki (leqnSn _).
rewrite /pmnm_exc_ms Hsz -/n Hm.
case: ifP => Hjn.
(* The merge row j - 1 is marked. *)
  rewrite nth_set_nth /=.
  set u := pmnm_succ m.+1 t.
  case: (eqVneq u j.-1) => [//|Hu] /=.
  rewrite Ed !Ep.
  have Hjm : j <= m.+1 by rewrite -ltnS -ltnS.
  case: (ltnP t j.-1) => Htj.
    have Hj1m : j.-1 <= m by rewrite -ltnS prednK.
    have Htm : t < m := leq_trans Htj Hj1m.
    have Hu1 : u = t.+1 by rewrite /u /pmnm_succ ltnS Htm.
    have Htj1 : t.+1 < j.-1 by rewrite ltn_neqAle Htj andbT -Hu1.
    have Hjp : j.-1 < j by rewrite ltn_predL.
    have Htj2 : t.+1 < j := ltn_trans Htj1 Hjp.
    rewrite Hu1 Htj2 Htj1.
    have Htn : t.+1 < n by rewrite Hm ltnS (ltn_trans Ht) // ltnS ltnW.
    have := H t (ltn_trans (ltnSn t) Htn).
    by rewrite /pmnm_succ Htn.
  have Hjt : j <= t.+1 by rewrite -(leq_add2r 1) !addn1 prednK in Htj *.
  have Ht2 : t.+2 < n by rewrite Hm !ltnS.
  case Htm: (t.+1 < m.+1).
    have Hu1 : u = t.+1 by rewrite /u /pmnm_succ Htm.
    rewrite Hu1 ltnNge Hjt /= ltnNge (leq_trans (leq_pred j) Hjt) /=.
    have := H t.+2 Ht2.
    have Htm' : t < m by rewrite -ltnS Htm.
    by rewrite /pmnm_succ Hm !ltnS Htm'.
  have Hu0 : u = 0 by rewrite /u /pmnm_succ Htm.
  rewrite Hu0 Hj0 /=.
  have Hj10 : 0 < j.-1 by rewrite lt0n -Hu0 eq_sym.
  rewrite Hj10.
  have Htm' : (t < m) = false by rewrite -ltnS Htm.
  have := H t.+2 Ht2.
  by rewrite /pmnm_succ Hm !ltnS Htm'.
(* Wrap-around: the merge row is the root. *)
have Ejm : j = m.+2.
  apply/eqP; rewrite eqn_leq; apply/andP; split; first by rewrite -ltnS -Hm.
  by rewrite -ltnS leqNgt Hjn.
rewrite nth_set_nth /= Ed !Ep Ejm /=.
rewrite /pmnm_succ; case: ifP => Htm //=.
have Ht1n : t.+1 < n by rewrite Hm ltnS ltnW.
case: ifP Htm => // Htm1 _.
rewrite Htm1 Ht.
have := H t (ltn_trans (ltnSn t) Ht1n).
by rewrite /pmnm_succ Ht1n.
Qed.

Lemma pmnm_incr_del ps j : pmnm_incr ps -> pmnm_incr (pmso_del j ps).
Proof.
move=> /allP H; rewrite /pmnm_incr /pmso_del all_cat; apply/andP; split; apply/allP => x Hx.
- by apply: H; exact: mem_take Hx.
- by apply: H; exact: mem_drop Hx.
Qed.

End Marks.

(* 3. One step of the recursion, with sharp label counts. *)
Section Steps.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d) (B : nat).
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)) (ms : seq bool).

Definition pmnm_w ms rs ps : nat :=
  [&& pmso_valid N d rs ps, pmnm_nb d q0 ms ps & pmnm_incr d ps] * B ^ (2 * pmsc_e N d rs ps).

(* A contraction at j removes a row visited once; the label is the pair
   of step j - 1, with no orientation choice. *)
Lemma pmnm_step_c L ms j : size ms = L.+1 -> j < L.+1 ->
  (\sum_(W : L.+1.-tuple 'I_N * L.+1.-tuple ('I_d * 'I_d))
     ((pmso_fv N W.1 == j) && pmso_kc N r0 W.1 j) * pmnm_w ms W.1 W.2 <=
   N * \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
     (j <= pmso_fv N W.1) * pmnm_w (pmso_del j ms) W.1 W.2)%N.
Proof.
move=> Hms HjL.
set I := (L.+1.-tuple 'I_N * L.+1.-tuple ('I_d * 'I_d))%type.
set J := ((L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N)%type.
pose P (W : I) := [&& pmso_fv N W.1 == j, pmso_kc N r0 W.1 j, pmso_valid N d W.1 W.2,
  pmnm_nb d q0 ms W.2 & pmnm_incr d W.2].
pose Q (y : J) := (j <= pmso_fv N y.1.1).
pose g (y : J) : I := (pmso_tins j y.2 y.1.1, pmso_tins j (nth q0 y.1.2 j.-1) y.1.2).
have -> : (\sum_(W : I) ((pmso_fv N W.1 == j) && pmso_kc N r0 W.1 j) * pmnm_w ms W.1 W.2 =
    \sum_(W | P W) B ^ (2 * pmsc_e N d W.1 W.2))%N.
  rewrite [RHS]big_mkcond /=; apply: eq_bigr => W _; rewrite /P /pmnm_w.
  by case: (_ == j); case: pmso_kc; case: pmso_valid; case: pmnm_nb; case: pmnm_incr;
    rewrite ?mul0n ?mul1n.
(* Each walk is rebuilt from the contracted walk and the removed row. *)
apply: (leq_trans (pmso_cover _ _ P Q g (fun W => B ^ (2 * pmsc_e N d W.1 W.2)) _)).
  move=> [rs ps] /and5P [/eqP Hf Hk HW Hnb Hinc].
  have Hj : j < size rs by rewrite size_tuple.
  have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
  have [_ _ _ Hor] := pmso_contract N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
  have Hs : size ps = size rs by move: HW => /and4P [/eqP].
  have Hjp : j < size ps by rewrite Hs.
  have Hj1 : j.-1 < size ps by apply: leq_ltn_trans Hjp; exact: leq_pred.
  have Epj : nth q0 ps j = nth q0 ps j.-1.
    exact: pmnm_orient_incr (pmnm_incr_nth d q0 _ _ Hinc Hjp) (pmnm_incr_nth d q0 _ _ Hinc Hj1) Hor.
  exists ((Tuple (pmso_tdel_size j rs HjL), Tuple (pmso_tdel_size j ps HjL)), nth r0 rs j).
    by rewrite /Q /=; exact: (pmso_fv_remc N r0 rs j Hf Hj).
  rewrite /g /=; congr (_, _); apply: val_inj => /=.
    by rewrite pmso_ins_del.
  have Hj1j : j.-1 < j by rewrite prednK.
  by rewrite (pmso_nth_del q0 j j.-1 ps Hj1j) -Epj pmso_ins_del.
(* The rebuilt walk has the weight of the contracted walk. *)
apply: (@leq_trans (\sum_(y | Q y) pmnm_w (pmso_del j ms) y.1.1 y.1.2)).
  apply: leq_sum => [[[rs' ps'] v]] Qy.
  case HP: (P _); rewrite ?mul0n // mul1n.
  move: HP; rewrite /P /g /= => /and5P [/eqP Hf Hk HW Hnb Hinc].
  set rs := pmso_ins j v rs' in Hf Hk HW *.
  set ps := pmso_ins j (nth q0 ps' j.-1) ps' in HW Hnb Hinc *.
  have Hj : j < size rs by rewrite pmso_size_ins size_tuple.
  have Ers : pmso_del j rs = rs' by rewrite /rs pmso_del_ins // size_tuple -ltnS.
  have Eps : pmso_del j ps = ps' by rewrite /ps pmso_del_ins // size_tuple -ltnS.
  have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
  have [HW' _ _ _] := pmso_contract N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
  have He := pmso_e_contract N d r0 q0 rs ps j HW Hf Hj Hk.
  have Hs : size ps = size rs by move: HW => /and4P [/eqP].
  have Hj1j : j.-1 < j by rewrite prednK.
  have Epj : nth q0 ps j = nth q0 ps j.-1.
    have Hjs' : j <= size ps' by rewrite size_tuple -ltnS.
    rewrite /ps (pmso_nth_ins_at q0 j _ ps' Hjs').
    by rewrite (pmso_nth_ins q0 j _ j.-1 ps' Hj1j Hjs').
  have Hsz1 : size ms = size ps by rewrite Hms Hs pmso_size_ins size_tuple.
  have H2p : 2 < size ps by rewrite Hs.
  have Hjp : 0 < j < size ps by rewrite H0 Hs.
  have Hnb' := pmnm_contract_nb d q0 ms ps j Hsz1 H2p Hjp Epj Hnb.
  rewrite Eps in Hnb'.
  have Hinc' := pmnm_incr_del d ps j Hinc; rewrite Eps in Hinc'.
  rewrite Ers Eps in HW' He.
  by rewrite /pmnm_w HW' Hnb' Hinc' He mul1n.
rewrite (pmso_sum_pair _ _ (fun W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d) =>
    j <= pmso_fv N W.1) (fun W => pmnm_w (pmso_del j ms) W.1 W.2)) card_ord leq_mul2l.
apply/orP; right; rewrite big_mkcond /=; apply: leq_sum => W _.
by case: ifP => _; rewrite ?mul1n ?mul0n.
Qed.

(* The removed pair of an excursion is increasing; fresh pairs number
   'C(d, 2), and pairs with an old color cost B^4. *)
Lemma pmnm_card_incr : (\sum_(q : 'I_d * 'I_d | (q.1 < q.2)%N) 1 = 'C(d, 2))%N.
Proof.
rewrite -(pair_big_dep xpredT (fun a b : 'I_d => (a < b)%N) (fun _ _ => 1%N)) /=.
rewrite (exchange_big_dep xpredT) //=.
rewrite (eq_bigr (fun j : 'I_d => j : nat)); last first.
  by rewrite -bin2_sum big_mkord.
move=> j _; rewrite (eq_bigl (fun i0 : 'I_d => true && (i0 < j))) //.
by rewrite (big_ord_narrow_cond (ltnW (ltn_ord j))) /= sum1_card card_ord.
Qed.

Lemma pmnm_sum_old (ps : seq ('I_d * 'I_d)) :
  (\sum_(q : 'I_d * 'I_d | (q.1 < q.2)%N) B ^ (2 * pmso_old d ps q) <=
   'C(d, 2) + 2 * #|pmso_cols d ps| * d * B ^ 4)%N.
Proof.
set C := pmso_cols d ps.
have Hpt : forall q : 'I_d * 'I_d,
    (B ^ (2 * pmso_old d ps q) <= 1 + ((q.1 \in C) + (q.2 \in C)) * B ^ 4)%N.
  move=> q; rewrite /pmso_old -/C.
  have HB : (B ^ 2 <= 1 + B ^ 4)%N.
    case: B => [// | b]; apply: leq_trans (leq_addl 1 _).
    by rewrite leq_pexp2l.
  case: (q.1 \in C); case: (q.2 \in C) => /=; rewrite ?mul1n ?add0n ?addn0 //.
  rewrite (_ : (2 * (1 + 1) = 4)%N) // (_ : (1 + 1 = 2)%N) //.
  by rewrite mul2n -addnn addnA leq_addl.
apply: (@leq_trans (\sum_(q : 'I_d * 'I_d | (q.1 < q.2)%N)
    (1 + ((q.1 \in C) + (q.2 \in C)) * B ^ 4))%N).
  by apply: leq_sum => q _; exact: Hpt.
rewrite big_split /= pmnm_card_incr leq_add2l -big_distrl /= leq_mul2r.
apply/orP; right.
apply: (@leq_trans (\sum_(q : 'I_d * 'I_d) ((q.1 \in C) + (q.2 \in C)))%N).
  rewrite [X in (_ <= X)%N](bigID (fun q : 'I_d * 'I_d => (q.1 < q.2)%N)) /=.
  exact: leq_addr.
rewrite big_split /=.
have H1 : (\sum_(q : 'I_d * 'I_d) (q.1 \in C) = #|C| * d)%N.
  rewrite -(pair_bigA _ (fun (a b : 'I_d) => nat_of_bool (a \in C))) /=.
  rewrite (eq_bigr (fun a : 'I_d => (a \in C) * d)%N);
    first by move=> a _; rewrite big_const_ord iter_addn_0.
  rewrite -big_distrl /=; congr (_ * _)%N.
  by rewrite -sum1_card [RHS]big_mkcond /=; apply: eq_bigr => a _; case: (a \in C).
have H2 : (\sum_(q : 'I_d * 'I_d) (q.2 \in C) = d * #|C|)%N.
  rewrite -(pair_bigA _ (fun (a b : 'I_d) => nat_of_bool (b \in C))) /=.
  rewrite (eq_bigr (fun a : 'I_d => #|C|)); first last.
    by rewrite big_const_ord iter_addn_0 mulnC.
  by move=> a _; rewrite -sum1_card [RHS]big_mkcond /=; apply: eq_bigr => b _; case: (b \in C).
by rewrite H1 H2 (mulnC d) addnn -mul2n mulnA.
Qed.

Lemma pmnm_step_e L ms j : size ms = L.+2 -> j < L.+2 ->
  (\sum_(W : L.+2.-tuple 'I_N * L.+2.-tuple ('I_d * 'I_d))
     ((pmso_fv N W.1 == j) && pmso_ke N r0 W.1 j) * pmnm_w ms W.1 W.2 <=
   N * ('C(d, 2) + 2 * L * d * B ^ 4) * \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
     (j.-1 <= pmso_fv N W.1) * pmnm_w (pmnm_exc_ms j ms) W.1 W.2)%N.
Proof.
move=> Hms HjL.
set I := (L.+2.-tuple 'I_N * L.+2.-tuple ('I_d * 'I_d))%type.
set J := (((L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N) * ('I_d * 'I_d))%type.
pose P (W : I) := [&& pmso_fv N W.1 == j, pmso_ke N r0 W.1 j, pmso_valid N d W.1 W.2,
  pmnm_nb d q0 ms W.2 & pmnm_incr d W.2].
pose Q (y : J) := (j.-1 <= pmso_fv N y.1.1.1) && (y.2.1 < y.2.2)%N.
pose g (y : J) : I := (Tuple (pmso_tinse_rows_size N r0 _ j y.1.2 y.1.1.1),
  Tuple (pmso_tinse_labs_size d _ j y.2 true y.1.1.2)).
have -> : (\sum_(W : I) ((pmso_fv N W.1 == j) && pmso_ke N r0 W.1 j) * pmnm_w ms W.1 W.2 =
    \sum_(W | P W) B ^ (2 * pmsc_e N d W.1 W.2))%N.
  rewrite [RHS]big_mkcond /=; apply: eq_bigr => W _; rewrite /P /pmnm_w.
  by case: (_ == j); case: pmso_ke; case: pmso_valid; case: pmnm_nb; case: pmnm_incr;
    rewrite ?mul0n ?mul1n.
(* Each walk is rebuilt from the shortened walk, the removed row and the
   increasing pair of step j - 1; the orientation is forced. *)
apply: (leq_trans (pmso_cover _ _ P Q g (fun W => B ^ (2 * pmsc_e N d W.1 W.2)) _)).
  move=> [rs ps] /and5P [/eqP Hf /eqP Hk HW Hnb Hinc].
  have Hj : j < size rs by rewrite size_tuple.
  have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
  have [Hr Hp] := pmso_rebuild_e N d r0 q0 rs ps j HW Hf Hj Hk.
  have [_ _ _ Hor] := pmso_excursion N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
  have Hs : size ps = size rs by move: HW => /and4P [/eqP].
  have Hjp : j < size ps by rewrite Hs.
  have Hj1 : j.-1 < size ps by apply: leq_ltn_trans Hjp; exact: leq_pred.
  have Epj : nth q0 ps j = nth q0 ps j.-1.
    exact: pmnm_orient_incr (pmnm_incr_nth d q0 _ _ Hinc Hjp) (pmnm_incr_nth d q0 _ _ Hinc Hj1) Hor.
  have Hsz1 : size (pmso_del2r j rs) == L.
    by rewrite pmso_size_del2r ?H0 ?Hj // size_tuple.
  have Hj1' : j.-1 < L.+2 by rewrite (leq_ltn_trans (leq_pred j)).
  have Hsz2 : size (pmso_del j.-1 (pmso_del j.-1 ps)) == L.
    rewrite (pmso_size_del j.-1 (pmso_del j.-1 ps)) ?(pmso_size_del j.-1 ps) ?size_tuple //.
    by rewrite ltn_predRL prednK.
  exists (((Tuple Hsz1, Tuple Hsz2), nth r0 rs j), nth q0 ps j.-1).
    rewrite /Q /= (pmso_fv_reme N r0 rs j Hf Hj Hk) /=.
    exact: (pmnm_incr_nth d q0 _ _ Hinc Hj1).
  rewrite /g /=; congr (_, _); apply: val_inj => /=; first exact: (esym Hr).
  by move: Hp; rewrite Epj eqxx => <-.
(* The rebuilt walk has the weight of the shortened walk, times B to the
   power twice the number of old colors of the pair. *)
apply: (@leq_trans (\sum_(y | Q y)
    pmnm_w (pmnm_exc_ms j ms) y.1.1.1 y.1.1.2 * B ^ (2 * pmso_old d y.1.1.2 y.2))).
  apply: leq_sum => [[[[rs'' ps''] v] q]] Qy.
  case HP: (P _); rewrite ?mul0n // mul1n.
  move: HP; rewrite /P /g /= => /and5P [/eqP Hf /eqP Hk HW Hnb Hinc].
  set rs := pmso_inse_rows N r0 j v rs'' in Hf Hk HW *.
  set ps := pmso_inse_labs d j q true ps'' in HW Hnb Hinc *.
  have Hj : j < size rs by rewrite pmso_size_inse_rows size_tuple.
  have Ers : pmso_del2r j rs = rs'' by rewrite /rs pmso_del2r_inse // size_tuple -ltnS.
  have Hj1 : j.-1 <= size ps'' by rewrite size_tuple -subn1 leq_subLR add1n -ltnS.
  have [Eps Eq] := pmso_del2l_inse d q0 j q true ps'' Hj1.
  have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
  have [HW' _ _ _] := pmso_excursion N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
  have He := pmso_e_excursion N d r0 q0 rs ps j HW Hf Hj Hk.
  have Hs : size ps = size rs by move: HW => /and4P [/eqP].
  have Hsz1 : size ms = size ps by rewrite Hms Hs pmso_size_inse_rows size_tuple.
  have H2p : 2 < size ps by rewrite Hs.
  have Hjp : 0 < j < size ps by rewrite H0 Hs.
  have Hnb' := pmnm_exc_nb d q0 ms ps j Hsz1 H2p Hjp Hnb.
  have Hinc' := pmnm_incr_del d _ j.-1 (pmnm_incr_del d ps j.-1 Hinc).
  rewrite /ps Eps Eq Ers in He; rewrite /ps Eps Ers in HW'; rewrite /ps Eps in Hnb' Hinc'.
  by rewrite /pmnm_w HW' Hnb' Hinc' /= mul1n /ps He mulnDr expnD.
(* The increasing pairs with old colors. *)
set ms' := pmnm_exc_ms j ms.
set K := ('C(d, 2) + 2 * L * d * B ^ 4)%N.
rewrite -(pair_big
  (fun x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N => j.-1 <= pmso_fv N x.1.1)
  (fun q : 'I_d * 'I_d => (q.1 < q.2)%N)
  (fun x q => pmnm_w ms' x.1.1 x.1.2 * B ^ (2 * pmso_old d x.1.2 q))%N) /=.
have Hin : forall x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N,
    (\sum_(q : 'I_d * 'I_d | (q.1 < q.2)%N)
       pmnm_w ms' x.1.1 x.1.2 * B ^ (2 * pmso_old d x.1.2 q) <=
     pmnm_w ms' x.1.1 x.1.2 * K)%N.
  move=> x; rewrite -big_distrr /= leq_mul2l.
  case: eqP => [// | /eqP Hw].
  have HV : pmso_valid N d x.1.1 x.1.2.
    by move: Hw; rewrite /pmnm_w; case: pmso_valid => //=; rewrite mul0n eqxx.
  move: HV => /and4P [/eqP Hs Hl Hd /pmso_evenP He].
  have HC := pmsc_colors_le N d x.1.1 x.1.2 Hs Hl Hd He.
  rewrite orFb; apply: (leq_trans (pmnm_sum_old x.1.2)).
  rewrite /K leq_add2l; apply: leq_mul => //; apply: leq_mul => //; apply: leq_mul => //.
  by rewrite pmso_card_cols (leq_trans HC) // size_tuple.
apply: (@leq_trans
    (\sum_(x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N | j.-1 <= pmso_fv N x.1.1)
      pmnm_w ms' x.1.1 x.1.2 * K)%N).
  by apply: leq_sum => x _; exact: Hin.
rewrite (pmso_sum_pair _ _ (fun W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d) =>
    j.-1 <= pmso_fv N W.1) (fun W => pmnm_w ms' W.1 W.2 * K)%N) card_ord.
rewrite -mulnA leq_mul2l; apply/orP; right.
rewrite -big_distrl /= mulnC leq_mul2l; apply/orP; right.
rewrite big_mkcond /=; apply: leq_sum => W _.
by case: ifP => _; rewrite ?mul1n ?mul0n.
Qed.

End Steps.

(* Sections 4 to 7: the recursion by the first removable mark and its
   solution. S L ms k sums the weights of the walks of length L whose
   first removable row is at k or later (pmnm_S). Such a row is a mark
   (pmnm_unmarked, pmnm_split). A contraction at the m-th mark from k
   leaves phi - m marks from j on; an excursion leaves at most
   phi - m + 1 from j - 1 on. So S L ms k <= 2^phi binom(L + phi, phi) z L
   (pmnm_solve), where phi is the number of marks from k on. With z the
   explicit sum pmnm_Z over the numbers of contractions and excursions,
   the full sum is at most 2^c binom(L + c, c) pmnm_Z L, where c <= n is
   the number of marks (pmnm_count). *)

(* 4. Counting facts on marks. *)
Lemma pmnm_drop_del (T : Type) j i (s : seq T) : j <= i -> drop i (pmso_del j s) = drop i.+1 s.
Proof.
move=> Hji; rewrite /pmso_del drop_cat size_take.
case: (ltnP j (size s)) => Hjs.
  by rewrite ltnNge Hji /= drop_drop addnS subnK.
have Hi : size s <= i := leq_trans Hjs Hji.
rewrite ltnNge Hi /= (drop_oversize (n := j.+1)) ?(leq_trans Hjs) //.
by rewrite /= drop_oversize //; exact: leqW.
Qed.

Lemma pmnm_count_del j (s : seq bool) : count id (pmso_del j s) + nth false s j = count id s.
Proof.
rewrite /pmso_del -[in RHS](cat_take_drop j s) !count_cat -addnA; congr (_ + _).
case: (ltnP j (size s)) => Hj.
  by rewrite [in RHS](drop_nth false Hj) /= addnC.
by rewrite !drop_oversize ?nth_default ?addn0 // (leq_trans Hj).
Qed.

Lemma pmnm_count_drop n (s : seq bool) : count id (drop n s) <= count id s.
Proof.
by rewrite -[in X in _ <= X](cat_take_drop n s) count_cat leq_addl.
Qed.

Lemma pmnm_count_set (s : seq bool) i : count id (set_nth false s i true) <= (count id s).+1.
Proof.
elim: s i => [|x s IH] i.
  elim: i => [|i IHi] /=; first by [].
  by move: IHi; rewrite /= add0n; case: i.
case: i => [|i] /=.
  by rewrite add1n ltnS leq_addl.
by rewrite -addnS leq_add2l IH.
Qed.

Lemma pmnm_count_drop_set (s : seq bool) i :
  count id (drop i (set_nth false s i true)) <= (count id (drop i.+1 s)).+1.
Proof.
elim: s i => [|x s IH] i.
  elim: i => [|i IHi] /=; first by [].
  by move: IHi; case: i.
case: i => [|i] /=.
  by rewrite add1n drop0.
exact: IH.
Qed.

Lemma pmnm_exc_size j ms : 0 < j < size ms -> 2 < size ms -> size (pmnm_exc_ms j ms) = (size ms).-2.
Proof.
move=> /andP [Hj0 Hj] H2.
have [m Hm] : exists m, size ms = m.+3 by exists (size ms - 3); rewrite -addn3 subnK.
rewrite /pmnm_exc_ms Hm /=; case: ifP => Hj1; rewrite size_set_nth.
  have Hs1 : size (pmso_del j ms) = m.+2 by rewrite pmso_size_del // Hm.
  rewrite pmso_size_del Hs1 //.
  by apply/maxn_idPr; rewrite prednK.
have Hj1' : j.-1 < size ms by rewrite (leq_ltn_trans (leq_pred j)).
have Hs1 : size (pmso_del j.-1 ms) = m.+2 by rewrite pmso_size_del // Hm.
rewrite pmso_size_del Hs1; first by rewrite -ltnS prednK // -Hm.
by apply/maxn_idPr.
Qed.

Lemma pmnm_exc_count j ms : 0 < j < size ms -> 2 < size ms -> nth false ms j ->
  count id (pmnm_exc_ms j ms) <= count id ms.
Proof.
move=> /andP [Hj0 Hj] H2 Hm.
rewrite /pmnm_exc_ms; case: ifP => _; apply: (leq_trans (pmnm_count_set _ _)).
  have E1 := pmnm_count_del j ms; rewrite Hm /= addn1 in E1.
  have E2 := pmnm_count_del j (pmso_del j ms).
  by rewrite -E1 ltnS -[X in _ <= X]E2 leq_addr.
have E1 := pmnm_count_del j.-1 (pmso_del j.-1 ms).
rewrite (pmso_nth_del_ge false j.-1 j.-1 ms (leqnn _)) prednK // Hm /= addn1 in E1.
by rewrite E1 -[X in _ <= X](pmnm_count_del j.-1 ms) leq_addr.
Qed.

Lemma pmnm_exc_drop j ms : 0 < j < size ms -> 2 < size ms ->
  count id (drop j.-1 (pmnm_exc_ms j ms)) <= (count id (drop j.+1 ms)).+1.
Proof.
move=> Hj H2.
have Hsz := pmnm_exc_size j ms Hj H2.
case/andP: Hj => Hj0 Hj.
move: Hsz; rewrite /pmnm_exc_ms; case: ifP => Hj1 Hsz.
  apply: (leq_trans (pmnm_count_drop_set _ _)).
  rewrite prednK // (pmnm_drop_del _ j j) // (pmnm_drop_del _ j j.+1) // ltnS.
  have -> : drop j.+2 ms = drop 1 (drop j.+1 ms) by rewrite drop_drop.
  exact: pmnm_count_drop.
(* Wrap-around: the new list ends at position j - 1. *)
apply: (leq_trans (count_size _ _)).
have Ej : size ms = j.+1 by apply/eqP; rewrite eqn_leq leqNgt Hj1 Hj.
by rewrite size_drop Hsz Ej /= subnn.
Qed.

(* Summing over the marks at positions k or later, by the number of
   marks after each. *)
Lemma pmnm_sum_marks (G : nat -> nat) ms k L : size ms = L ->
  (\sum_(k <= j < L | nth false ms j) G (count id (drop j.+1 ms)) =
   \sum_(i < count id (drop k ms)) G i)%N.
Proof.
move=> <-; move Hn : (size ms - k) => m; elim: m k Hn => [|m IH] k Hn.
  have Hk : size ms <= k by rewrite -subn_eq0 Hn.
  by rewrite big_geq // drop_oversize // big_ord0.
have Hk : k < size ms by rewrite -subn_gt0 Hn.
have Hn' : size ms - k.+1 = m by rewrite subnS Hn.
rewrite big_ltn_cond // (IH k.+1 Hn') (drop_nth false Hk) /=.
case: (nth false ms k) => /=.
  by rewrite add1n big_ord_recr /= addnC.
by rewrite add0n.
Qed.

(* 5. The bound 2^phi binom(L + phi, phi). *)
Definition pmnm_F L phi : nat := 2 ^ phi * 'C(L + phi, phi).

Lemma pmnm_F_gt0 L phi : 0 < pmnm_F L phi.
Proof.
by rewrite /pmnm_F muln_gt0 expn_gt0 bin_gt0 leq_addl.
Qed.

Lemma pmnm_F_mono L phi1 phi2 : phi1 <= phi2 -> pmnm_F L phi1 <= pmnm_F L phi2.
Proof.
move=> H; apply: (homo_leq leqnn leq_trans _ H) => i.
by apply: leq_mul; [exact: leq_pexp2l | rewrite addnS binS leq_addl].
Qed.

Lemma pmnm_F_rec L phi :
  (1 + \sum_(i < phi) (pmnm_F L.+1 i + pmnm_F L i.+1) <= pmnm_F L.+2 phi)%N.
Proof.
elim: phi => [|phi IH].
  by rewrite big_ord0 /pmnm_F addn0 bin0.
rewrite big_ord_recr /= addnA.
apply: (leq_trans (leq_add IH (leqnn _))).
rewrite /pmnm_F.
have Ha : 'C(L.+1 + phi, phi) <= 'C(L.+2 + phi, phi).
  by apply: leq_bin2l; rewrite leq_add2r.
have Hb : 'C(L + phi.+1, phi.+1) <= 'C(L.+2 + phi, phi.+1).
  by apply: leq_bin2l; rewrite addnS !addSn leqnSn.
(* Pascal's rule on the right. *)
rewrite [in X in _ <= X]expnS [in X in _ <= X]addnS [in X in _ <= X]binS.
set p := 2 ^ phi; set a := 'C(L.+2 + phi, phi); set b := 'C(L.+2 + phi, phi.+1).
apply: (@leq_trans (p * a + (p * a + 2 * p * b))).
  rewrite leq_add2l; apply: leq_add; first by rewrite leq_mul2l Ha orbT.
  by rewrite expnS -/p leq_mul2l Hb orbT.
by rewrite addnA addnn -mul2n mulnA -mulnDr addnC.
Qed.

(* 6. The recursion and its solution. *)
Section Solve.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d) (B : nat).
Implicit Types (ms : seq bool).

(* Walks of length L whose first removable row is at k or later. *)
Definition pmnm_S L ms k : nat :=
  \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
    (k <= pmso_fv N W.1) * pmnm_w N d q0 B ms W.1 W.2.

(* Terminal walks: no removable row. *)
Definition pmnm_T L ms : nat :=
  \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
    (pmso_fv N W.1 == L) * pmnm_w N d q0 B ms W.1 W.2.

Lemma pmnm_unmarked L ms j (W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) :
  j < L -> pmso_fv N W.1 = j -> nth false ms j = false -> pmnm_w N d q0 B ms W.1 W.2 = 0.
Proof.
move=> HjL Hf Hm; rewrite /pmnm_w.
case: (boolP [&& pmso_valid N d W.1 W.2, pmnm_nb d q0 ms W.2 & pmnm_incr d W.2]) =>
  [/and3P [HW Hnb Hinc] | _]; last by rewrite mul0n.
have Hj : j < size W.1 by rewrite size_tuple.
have [H2 H0 Hv _] := pmso_fvP N r0 W.1 j Hf Hj.
have := pmnm_mark_once N d r0 q0 W.1 W.2 ms j HW Hnb Hinc H2 (introT andP (conj H0 Hj)) Hv.
by rewrite Hm.
Qed.

(* Only marked positions can be the first removable row. *)
Lemma pmnm_split L ms k :
  (pmnm_S L ms k <= pmnm_T L ms + \sum_(k <= j < L | nth false ms j)
     \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
       (pmso_fv N W.1 == j) * pmnm_w N d q0 B ms W.1 W.2)%N.
Proof.
set G := fun j => \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
  (pmso_fv N W.1 == j) * pmnm_w N d q0 B ms W.1 W.2.
have -> : \sum_(k <= j < L | nth false ms j) G j = \sum_(k <= j < L) G j.
  rewrite [RHS](bigID (fun j => nth false ms j)) /= [X in _ = _ + X]big1_seq ?addn0 //.
  move=> j /andP [/= Hm]; rewrite mem_index_iota => /andP [_ HjL].
  rewrite /G big1 // => W _.
  case: eqP => [Hf | _]; last by rewrite mul0n.
  by rewrite (pmnm_unmarked L ms j W HjL Hf (negbTE Hm)) muln0.
(* Each walk has its first removable row at fv, with k <= fv <= L. *)
rewrite /pmnm_S /pmnm_T /G exchange_big /= -big_split /=; apply: leq_sum => W _.
rewrite -big_distrl /= -mulnDl leq_mul2r; apply/orP; right.
have Hf := pmso_fv_le N W.1; rewrite size_tuple in Hf.
case: (leqP k (pmso_fv N W.1)) => Hk //=.
case: (ltngtP (pmso_fv N W.1) L) => HL.
- rewrite (bigD1_seq (pmso_fv N W.1)) ?mem_index_iota ?Hk ?HL ?iota_uniq //= eqxx.
  by rewrite addnCA leq_addr.
- by move: Hf; rewrite leqNgt HL.
- by rewrite add1n.
Qed.

(* The solution. The bound z dominates the terminal sums and absorbs one
   contraction (factor N) or one excursion (factor N X). *)
Theorem pmnm_solve n X (z : nat -> nat) L0 :
  ('C(d, 2) + 2 * L0 * d * B ^ 4 <= X)%N ->
  (forall L ms, L <= L0 -> size ms = L -> count id ms <= n -> pmnm_T L ms <= z L) ->
  (forall L, L.+1 <= L0 -> N * z L <= z L.+1) ->
  (forall L, L.+2 <= L0 -> N * X * z L <= z L.+2) ->
  forall L ms k, L <= L0 -> size ms = L -> count id ms <= n ->
  pmnm_S L ms k <= pmnm_F L (count id (drop k ms)) * z L.
Proof.
move=> HX HT HZ1 HZ2 L; elim/ltn_ind: L => L IH ms k HL Hms Hn.
(* Walks of length at most 2 have no removable row. *)
case: (ltnP L 3) => HL3.
  apply: (@leq_trans (pmnm_T L ms)).
    rewrite /pmnm_S /pmnm_T; apply: leq_sum => W _; rewrite leq_mul2r; apply/orP; right.
    have -> : pmso_fv N W.1 = L.
      by rewrite /pmso_fv size_tuple; case: ifP => // H; move: HL3; rewrite ltnNge H.
    by rewrite eqxx leq_b1.
  apply: (leq_trans (HT L ms HL Hms Hn)).
  by rewrite leq_pmull // pmnm_F_gt0.
have [L' EL] : exists L', L = L'.+3 by exists (L - 3); rewrite -addn3 subnK.
move: IH HL Hms; rewrite EL => IH HL Hms; clear EL HL3.
apply: (leq_trans (pmnm_split _ _ _)).
set Z := z L'.+3.
pose c j := count id (drop j.+1 ms).
apply: (@leq_trans (Z + \sum_(k <= j < L'.+3 | nth false ms j)
    (pmnm_F L'.+2 (c j) + pmnm_F L'.+1 (c j).+1) * Z)).
  apply: leq_add; first exact: HT.
  rewrite big_nat_cond [X in (_ <= X)%N]big_nat_cond.
  apply: leq_sum => j /andP [/andP [Hkj HjL] Hmj].
  (* Position 0 is never removable. *)
  case: (posnP j) => [Ej | Hj0].
    rewrite big1 // => W _; case: eqP => [Hf | _]; last by rewrite mul0n.
    have HjW : j < size W.1 by rewrite size_tuple.
    have [_ H0 _ _] := pmso_fvP N r0 W.1 j Hf HjW.
    by move: H0; rewrite Ej.
  rewrite (eq_bigr (fun W : L'.+3.-tuple 'I_N * L'.+3.-tuple ('I_d * 'I_d) =>
      ((pmso_fv N W.1 == j) && pmso_kc N r0 W.1 j) * pmnm_w N d q0 B ms W.1 W.2 +
      ((pmso_fv N W.1 == j) && pmso_ke N r0 W.1 j) * pmnm_w N d q0 B ms W.1 W.2));
    first by move=> W _; rewrite -mulnDl /pmso_kc /pmso_ke; case: (_ == j); case: (_ == _).
  rewrite big_split mulnDl /=; apply: leq_add.
    (* A contraction at the mark j: the marks after j are c j. *)
    apply: (leq_trans (pmnm_step_c N d r0 q0 B L'.+2 ms j Hms HjL)).
    have Hj' : j < size ms by rewrite Hms.
    have Hsz : size (pmso_del j ms) = L'.+2 by rewrite pmso_size_del // Hms.
    have Hc : count id (pmso_del j ms) <= n.
      by apply: leq_trans Hn; rewrite -(pmnm_count_del j ms) leq_addr.
    have IH1 := IH L'.+2 (ltnSn _) (pmso_del j ms) j (ltnW HL) Hsz Hc.
    rewrite (pmnm_drop_del _ j j ms (leqnn j)) -/(c j) in IH1.
    apply: (leq_trans (leq_mul (leqnn N) IH1)).
    by rewrite mulnCA leq_mul2l; apply/orP; right; exact: HZ1.
  (* An excursion at the mark j: at most c j + 1 marks from j - 1 on. *)
  apply: (leq_trans (pmnm_step_e N d r0 q0 B L'.+1 ms j Hms HjL)).
  have Hjj : 0 < j < size ms by rewrite Hj0 Hms.
  have H2 : 2 < size ms by rewrite Hms.
  have Hsz : size (pmnm_exc_ms j ms) = L'.+1 by rewrite pmnm_exc_size // Hms.
  have Hc : count id (pmnm_exc_ms j ms) <= n := leq_trans (pmnm_exc_count j ms Hjj H2 Hmj) Hn.
  have IH2 := IH L'.+1 (ltnW (ltnSn _)) (pmnm_exc_ms j ms) j.-1 (ltnW (ltnW HL)) Hsz Hc.
  have Hd := pmnm_exc_drop j ms Hjj H2.
  apply: (@leq_trans
      (N * X * (pmnm_F L'.+1 (count id (drop j.-1 (pmnm_exc_ms j ms))) * z L'.+1))).
    apply: leq_mul; last exact: IH2.
    apply: leq_mul => //; apply: leq_trans HX; rewrite leq_add2l.
    apply: leq_mul => //; apply: leq_mul => //; apply: leq_mul => //.
    exact: ltnW (ltnW HL).
  by rewrite mulnCA; apply: leq_mul; [exact: pmnm_F_mono | exact: HZ2].
(* Sum over the marks, then the recursion of the bound. *)
rewrite -big_distrl /= /c.
rewrite (pmnm_sum_marks (fun i => pmnm_F L'.+2 i + pmnm_F L'.+1 i.+1) ms k L'.+3 Hms).
rewrite -[X in X + _]mul1n -mulnDl leq_mul2r; apply/orP; right.
exact: pmnm_F_rec.
Qed.

End Solve.

(* 7. An explicit bound z from a bound tau on the terminal sums: each
   number a of contractions and b of excursions is counted once. *)
Definition pmnm_Z (N X : nat) (tau : nat -> nat) (L : nat) : nat :=
  \sum_(0 <= a < L.+1) \sum_(0 <= b < L.+1)
    (a + 2 * b <= L) * (N ^ a * (N * X) ^ b * tau (L - a - 2 * b)).

Lemma pmnm_sum_nat_le (F : nat -> nat) n m : n <= m ->
  (\sum_(0 <= a < n) F a <= \sum_(0 <= a < m) F a)%N.
Proof.
by move=> H; rewrite [X in _ <= X](big_cat_nat (leq0n n) H) /= leq_addr.
Qed.

Lemma pmnm_Z_tau N X tau L : tau L <= pmnm_Z N X tau L.
Proof.
rewrite /pmnm_Z big_nat_recl // big_nat_recl //=.
by rewrite muln0 !subn0 !expn0 !mul1n -addnA leq_addr.
Qed.

Lemma pmnm_Z_N N X tau L : N * pmnm_Z N X tau L <= pmnm_Z N X tau L.+1.
Proof.
rewrite /pmnm_Z [X in _ <= X]big_nat_recl //=.
apply: leq_trans (leq_addl _ _).
rewrite big_distrr /=; apply: leq_sum => a _.
rewrite big_distrr /=.
apply: (@leq_trans (\sum_(0 <= b < L.+1) (a.+1 + 2 * b <= L.+1) *
  (N ^ a.+1 * (N * X) ^ b * tau (L.+1 - a.+1 - 2 * b)))); last exact: pmnm_sum_nat_le.
apply: leq_sum => b _.
by rewrite addSn ltnS subSS expnS mulnCA !mulnA.
Qed.

Lemma pmnm_Z_NX N X tau L : N * X * pmnm_Z N X tau L <= pmnm_Z N X tau L.+2.
Proof.
rewrite /pmnm_Z.
apply: (@leq_trans (\sum_(0 <= a < L.+1) \sum_(0 <= b < L.+3)
    (a + 2 * b <= L.+2) * (N ^ a * (N * X) ^ b * tau (L.+2 - a - 2 * b)))).
  2: by apply: pmnm_sum_nat_le; apply: leqW.
rewrite big_distrr /=; apply: leq_sum => a _.
rewrite [X in _ <= X]big_nat_recl //=.
apply: leq_trans (leq_addl _ _).
rewrite big_distrr /=.
apply: (@leq_trans (\sum_(0 <= b < L.+1) (a + 2 * b.+1 <= L.+2) *
  (N ^ a * (N * X) ^ b.+1 * tau (L.+2 - a - 2 * b.+1)))); last by apply: pmnm_sum_nat_le.
apply: leq_sum => b _.
have E1 : (a + 2 * b.+1 <= L.+2) = (a + 2 * b <= L) by rewrite mulnS addnCA add2n !ltnS.
have E2 : L.+2 - a - 2 * b.+1 = L - a - 2 * b.
  by rewrite mulnS -subnDA addnCA subnDA !subSS subn0 subnDA.
rewrite E1 E2 expnS.
set c := nat_of_bool _; set T := tau _; set Y := (N * X) ^ b; set NX := N * X.
apply: eq_leq; rewrite mulnCA; congr (_ * _); rewrite mulnA; congr (_ * _).
exact: mulnCA.
Qed.

(* The count: the full weighted sum over marked walks. *)
Theorem pmnm_count N d (r0 : 'I_N) (q0 : 'I_d * 'I_d) B n X (tau : nat -> nat) L0 :
  ('C(d, 2) + 2 * L0 * d * B ^ 4 <= X)%N ->
  (forall L ms, L <= L0 -> size ms = L -> count id ms <= n ->
     pmnm_T N d q0 B L ms <= tau L) ->
  forall L ms, L <= L0 -> size ms = L -> count id ms <= n ->
  (\sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) pmnm_w N d q0 B ms W.1 W.2 <=
   pmnm_F L (count id ms) * pmnm_Z N X tau L)%N.
Proof.
move=> HX HT L ms HL Hms Hn.
have H := pmnm_solve N d r0 q0 B n X (pmnm_Z N X tau) L0 HX
  (fun L ms HL Hs Hc => leq_trans (HT L ms HL Hs Hc) (pmnm_Z_tau N X tau L))
  (fun L _ => pmnm_Z_N N X tau L) (fun L _ => pmnm_Z_NX N X tau L) L ms 0 HL Hms Hn.
rewrite drop0 in H; apply: leq_trans H.
by rewrite /pmnm_S; apply: eq_leq; apply: eq_bigr => W _; rewrite leq0n mul1n.
Qed.
