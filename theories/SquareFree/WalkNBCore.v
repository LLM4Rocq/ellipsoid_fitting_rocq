(* The terminal core of the sharp count of non-backtracking (NB) walks.
   A terminal valid walk (rs, ps) of length L >= 3 with increasing pairs
   is coded by SquareFree.WalkShapeCode (pmsk_code). Its step
   symbols fall into three classes:
   - F: a fresh row and two fresh colors (pmnc_F);
   - Z: a closer of rank 0 (pmnc_Z); its orientation is forced, since the
     pairs are increasing;
   - X: all other symbols (pmnc_X).
   Main result (pmnc_XFZ_le): #X + #(F followed by Z) <= 147 e.
   - #X <= #(symbols with an index slot) + #(closers of rank >= 1)
     (pmnc_X_le).
   - A closer of rank >= 1 sits at a row visited at least 3 times, or its
     first open step is lonely, or it is the second visit of the root
     (pmnc_rank_le).
   - After F and then Z, the fresh row has been visited once. The walk is
     terminal, so the row is visited again, and the step of that arrival
     is a non-closer with an index slot (pmnc_FZ_le).
   For the weighted sum over codes: the explicit colors of an F symbol are
   increasing (pmnc_code_Fincr), and the code exponent is
   sum_s (2 rf + cf) = 2 (R - 1) + C = 2 L - e (pmnc_weight_exp).
   Deterministic, and the NB condition is not used. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import SquareFree.WalkCount SquareFree.WalkExcess
  SquareFree.WalkShapeOnce SquareFree.WalkShapeTwin SquareFree.WalkShapeCode
  SquareFree.WalkNBMarks.

(* 1. Classes of step symbols. *)
Section Classes.
Variables (N d n : nat).

Definition pmnc_F (y : pmsk_sym N d n) : bool :=
  match y with inr (inl _, inl _, inl _) => true | _ => false end.

Definition pmnc_Z (y : pmsk_sym N d n) : bool :=
  match y with inl (inl k, true) => k == 0 :> nat | _ => false end.

Definition pmnc_X (y : pmsk_sym N d n) : bool := ~~ pmnc_F y && ~~ pmnc_Z y.

(* The two explicit colors of an F symbol are increasing. *)
Definition pmnc_Fincr (y : pmsk_sym N d n) : bool :=
  match y with inr (inl _, inl c1, inl c2) => c1 < c2 | _ => true end.

Lemma pmnc_F_rf y : pmnc_F y -> pmsk_rf N d n y = 1.
Proof.
by case: y => [// | [[[?|?] [?|?]] [?|?]]].
Qed.

Lemma pmnc_F_cf y : pmnc_F y -> pmsk_cf N d n y = 2.
Proof.
by case: y => [// | [[[?|?] [?|?]] [?|?]]].
Qed.

Lemma pmnc_cf_le2 y : pmsk_cf N d n y <= 2.
Proof.
by case: y => [// | [[? [?|?]] [?|?]]].
Qed.

End Classes.

Arguments pmnc_F {N d n} y.
Arguments pmnc_Z {N d n} y.
Arguments pmnc_X {N d n} y.
Arguments pmnc_Fincr {N d n} y.

(* 2. Counting by injections. *)
Lemma pmnc_inj_count (m : nat) (P Q : pred 'I_m) (f : 'I_m -> 'I_m) :
  {in P &, injective f} -> (forall s, P s -> Q (f s)) ->
  (\sum_(s < m) P s <= \sum_(s < m) Q s)%N.
Proof.
move=> Hinj HPQ.
have E (Pr : pred 'I_m) : (\sum_(s < m) Pr s = #|Pr|)%N.
  rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => s _ /=.
  by rewrite unfold_in; case: (Pr s).
rewrite !E -(card_in_imset Hinj); apply: subset_leq_card; apply/subsetP => y.
by case/imsetP => x Px ->; exact: HPQ.
Qed.

Lemma pmnc_inj_count2 (m : nat) (P Q : pred 'I_m) (f : 'I_m -> 'I_m * bool) :
  {in P &, injective f} -> (forall s, P s -> Q (f s).1) ->
  (\sum_(s < m) P s <= 2 * \sum_(s < m) Q s)%N.
Proof.
move=> Hinj HPQ.
have E (T : finType) (Pr : pred T) : (\sum_(s : T) Pr s = #|Pr|)%N.
  rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => s _ /=.
  by rewrite unfold_in; case: (Pr s).
rewrite E -(card_in_imset Hinj).
apply: (@leq_trans #|[pred x : 'I_m * bool | Q x.1]|).
  apply: subset_leq_card; apply/subsetP => y; case/imsetP => x Px ->.
  by rewrite inE; exact: HPQ.
rewrite -E -(pair_bigA _ (fun (s : 'I_m) (b : bool) => nat_of_bool (Q s))) /=.
rewrite (eq_bigr (fun s => 2 * Q s)%N); first by move=> s _; rewrite big_bool /= addnn -mul2n.
by rewrite -big_distrr.
Qed.

Lemma pmnc_le1 (m : nat) (P : pred 'I_m) :
  (forall s1 s2, P s1 -> P s2 -> s1 = s2) -> (\sum_(s < m) P s <= 1)%N.
Proof.
move=> H.
have E : (\sum_(s < m) P s = #|P|)%N.
  rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => s _ /=.
  by rewrite unfold_in; case: (P s).
rewrite E; case: (pickP P) => [x Px | Hno]; last by rewrite eq_card0.
apply: (@leq_trans #|[set x]|); last by rewrite cards1.
by apply: subset_leq_card; apply/subsetP => y Py; rewrite inE (H y x Py Px).
Qed.

(* 3. The core of a terminal walk. *)
Section Core.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Variables (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).
Variable HW : pmso_valid N d rs ps.
Variable Hinc : pmnm_incr d ps.
Variable HT : pmso_fv N rs = size rs.
Variable H3 : 2 < size rs.
Variable n : nat.
Variable Hn : size rs <= n.+1.

Local Notation L := (size rs).
Local Notation a := (pmst_a N r0 rs).
Local Notation b := (pmst_b N r0 rs).
Local Notation p := (pmst_p d q0 ps).
Local Notation tw := (pmsk_tw N d q0 rs ps).
Local Notation closer := (pmsk_closer N d q0 rs ps).
Local Notation code := (pmsk_code N d r0 q0 rs ps n).
Local Notation ol := (pmsk_ol N d r0 q0 rs ps).
Local Notation ix := (pmsk_ix N d n).

(* Open steps at the row of step s. *)
Lemma pmnc_ol_mem s u : s < L ->
  (u \in ol s) = [&& u < s, pmsk_open d q0 (take s ps) u & (a s == a u) || (a s == b u)].
Proof.
move=> Hs; have Hps : size ps = L := pmst_size_ps N d rs ps HW.
have Hsz : size (take s ps) = s by rewrite size_takel // Hps ltnW.
rewrite /pmsk_ol /pmsk_olist mem_filter mem_iota Hsz add0n leq0n /=.
rewrite (pmsk_last_take N r0 rs s Hs).
case: (ltnP u s) => Hu; rewrite ?andbF ?andbT //=.
have Hu1 : u < s.+1 by rewrite ltnS ltnW.
have Hu2 : u.+1 < s.+1 by rewrite ltnS.
by rewrite (nth_take _ Hu1) (nth_take _ Hu2) /pmst_b /pmst_succ (leq_ltn_trans Hu Hs).
Qed.

Lemma pmnc_ol_uniq s : uniq (ol s).
Proof.
by rewrite /pmsk_ol /pmsk_olist filter_uniq // iota_uniq.
Qed.

(* At the first visit of a row, at most one step is open there. *)
Lemma pmnc_ol_first s : s < L -> a s \notin take s rs -> size (ol s) <= 1.
Proof.
move=> Hs Hnew.
have Hsub : {subset ol s <= [:: s.-1]}.
  move=> u; rewrite (pmnc_ol_mem s u Hs) => /and3P [Hu _ Hrow].
  rewrite inE; case/orP: Hrow => /eqP E.
    have : a u \in take s rs.
      by rewrite /pmst_a -(nth_take r0 Hu) mem_nth // size_takel // ltnW.
    by rewrite -E (negbTE Hnew).
  have Hu1 : u.+1 < L by rewrite (leq_ltn_trans Hu Hs).
  move: E; rewrite /pmst_b /pmst_succ Hu1 => E.
  case: (ltnP u.+1 s) => Hus.
    have : nth r0 rs u.+1 \in take s rs.
      by rewrite -(nth_take r0 Hus) mem_nth // size_takel // ltnW.
    by rewrite -E (negbTE Hnew).
  by have -> : s = u.+1 by apply/eqP; rewrite eqn_leq Hus Hu.
by rewrite -[1]/(size [:: s.-1]); exact: uniq_leq_size (pmnc_ol_uniq s) Hsub.
Qed.

Lemma pmnc_rank_old s : s < L -> closer s -> 0 < index (tw s) (ol s) -> a s \in take s rs.
Proof.
move=> Hs Hcl Hk; apply/negPn/negP => Hnew.
have H1 := pmnc_ol_first s Hs Hnew.
have H2 : index (tw s) (ol s) < size (ol s).
  by rewrite index_mem; exact: pmsk_ol_closer N d r0 q0 rs ps HW s Hs Hcl.
by move: Hk; rewrite lt0n; move: H2 H1; case: (index _ _) => // k; case: (size _) => [|[|]].
Qed.

Lemma pmnc_index_take (x : 'I_N) k : x \in take k rs -> index x rs < k.
Proof.
move=> Hx; rewrite -(cat_take_drop k rs) index_cat Hx.
apply: leq_trans (_ : size (take k rs) <= k); rewrite ?index_mem // size_take.
by case: ifP => // /negbT; rewrite -leqNgt.
Qed.

Lemma pmnc_count3 v i j k : i < j -> j < k -> k < L ->
  nth r0 rs i = v -> nth r0 rs j = v -> nth r0 rs k = v -> 3 <= count_mem v rs.
Proof.
move=> Hij Hjk HkL Hi Hj Hk.
have HjL : j < L := ltn_trans Hjk HkL.
rewrite -(cat_take_drop j rs) count_cat (drop_nth r0 HjL) /= Hj eqxx add1n.
have H1 : 0 < count_mem v (take j rs).
  by rewrite -has_count has_pred1 -Hi -(nth_take r0 Hij) mem_nth // size_takel // ltnW.
have H2 : 0 < count_mem v (drop j.+1 rs).
  rewrite -has_count has_pred1 -Hk.
  have Ek : k = j.+1 + (k - j.+1) by rewrite subnKC.
  rewrite [in nth r0 rs k]Ek -nth_drop mem_nth // size_drop.
  by rewrite ltn_sub2r // (leq_ltn_trans Hjk HkL).
by rewrite addnS ltnS; exact: (leq_add H1 H2).
Qed.

(* A row visited twice has one second visit. *)
Lemma pmnc_old_unique s1 s2 : s1 < L -> s2 < L -> a s1 = a s2 -> count_mem (a s1) rs <= 2 ->
  a s1 \in take s1 rs -> a s2 \in take s2 rs -> s1 = s2.
Proof.
move=> Hs1 Hs2 Ea Hc Ho1 Ho2.
have Hidx := pmnc_index_take.
have Hin (x : 'I_N) k : x \in take k rs -> x \in rs by move=> Hx; exact: mem_take Hx.
case: (ltngtP s1 s2) => // Hlt.
  have H := pmnc_count3 (a s1) _ _ _ (Hidx _ _ Ho1) Hlt Hs2
    (nth_index r0 (Hin _ _ Ho1)) erefl (esym Ea).
  by move: Hc; rewrite leqNgt H.
rewrite Ea in Hc.
have H := pmnc_count3 (a s2) _ _ _ (Hidx _ _ Ho2) Hlt Hs1 (nth_index r0 (Hin _ _ Ho2)) erefl Ea.
by move: Hc; rewrite leqNgt H.
Qed.

(* The first open step at a closer of rank >= 1 is lonely, unless the
   closer is at the root. *)
Lemma pmnc_head_lonely s : s < L -> closer s -> 0 < index (tw s) (ol s) ->
  count_mem (a s) rs <= 2 -> a s != nth r0 rs 0 -> tw (nth 0 (ol s) 0) = nth 0 (ol s) 0.
Proof.
move=> Hs Hcl Hk Hc Hroot.
set u := nth 0 (ol s) 0.
have Hts : tw s \in ol s := pmsk_ol_closer N d r0 q0 rs ps HW s Hs Hcl.
have Hsz : 0 < size (ol s) by case: (ol s) Hts.
have Hu : u \in ol s := mem_nth 0 Hsz.
have Hut : u != tw s.
  apply/eqP => E; move: Hk; rewrite -E /u.
  by case: (ol s) Hsz => // x l _ /=; rewrite eqxx.
move: (Hu); rewrite (pmnc_ol_mem s u Hs) => /and3P [Hus Hopen Hrow].
have HuL : u < L := ltn_trans Hus Hs.
have Hold := pmnc_rank_old s Hs Hcl Hk.
(* If u had a twin t, then t would come after s and touch the row of s. *)
apply/eqP; apply/negPn/negP => Hne.
set t := tw u in Hne *.
have Htw := pmsk_tw_spec N d q0 rs ps u Hne.
have HtL : t < L := pmsk_tw_lt N d q0 rs ps u HuL.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
have Hshare : pmsk_share d (p u) (p t).
  have := pmsk_twin_in N d q0 rs ps u t Htw (p u).1.
  rewrite !pmst_in_p eqxx /= /pmsk_share => /esym /orP [] /eqP ->; by rewrite eqxx ?orbT.
have Hst : s <= t.
  rewrite leqNgt; apply/negP => Hts'.
  move: Hopen; rewrite /pmsk_open => /allP /(_ t).
  have Hszs : size (take s ps) = s by rewrite size_takel // Hps ltnW.
  rewrite Hszs mem_iota add0n Hts' => /(_ isT).
  by rewrite (negbTE Hne) /= !nth_take // Hshare.
have Hts'' : t != s.
  by apply/eqP => E; move: Hut; rewrite -E /t (pmsk_tw_tw N d q0 rs ps u HuL) eqxx.
have Hgt : s < t by rewrite ltn_neqAle eq_sym Hts'' Hst.
have Hsame := pmsk_tw_same N d r0 q0 rs ps HW u HuL.
have Hrow' : (a s == a t) || (a s == b t).
  move: Hsame Hrow; rewrite /pmst_same -/t.
  by case/orP => /andP [/eqP E1 /eqP E2]; rewrite E1 E2 // orbC.
(* Then the row of s would be visited three times. *)
have Hidx : index (a s) rs < s := pmnc_index_take _ _ Hold.
have Hin : a s \in rs := mem_take Hold.
have Hni : nth r0 rs (index (a s) rs) = a s := nth_index r0 Hin.
case/orP: Hrow' => /eqP E.
  have := pmnc_count3 (a s) _ _ _ Hidx Hgt HtL Hni erefl (esym E).
  by rewrite ltnNge Hc.
move: E; rewrite /pmst_b /pmst_succ; case: ifP => Ht1 E; last by move: Hroot; rewrite E eqxx.
have := pmnc_count3 (a s) _ _ _ Hidx (ltn_trans Hgt (ltnSn t)) Ht1 Hni erefl (esym E).
by rewrite ltnNge Hc.
Qed.

Lemma pmnc_rank_le :
  (\sum_(s < L) (closer s && (0 < index (tw s) (ol s))) <=
   \sum_(s < L) (3 <= count_mem (a s) rs) +
   2 * #|[pred s : 'I_L | pmst_lonely N d q0 rs ps s]| + 1)%N.
Proof.
set P := fun s : 'I_L =>
  [&& closer s, 0 < index (tw s) (ol s), count_mem (a s) rs <= 2 & a s != nth r0 rs 0].
set Q := fun s : 'I_L =>
  [&& closer s, 0 < index (tw s) (ol s), count_mem (a s) rs <= 2 & a s == nth r0 rs 0].
apply: (@leq_trans (\sum_(s < L) ((3 <= count_mem (a s) rs) + P s + Q s))).
  apply: leq_sum => s _; rewrite /P /Q.
  case: (closer s) => //=; case: (0 < index _ _) => //=.
  by case: (leqP (count_mem (a s) rs) 2) => H /=; case: (a s == nth r0 rs 0).
rewrite big_split [X in X + _ <= _]big_split; apply: leq_add; first rewrite leq_add2l.
  (* Off the root: the first open step is lonely, at most 2 to 1. *)
  have E : \sum_(s < L) pmst_lonely N d q0 rs ps s =
      #|[pred s | pmst_lonely N d q0 rs ps s]|.
    rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => s _ /=.
    by rewrite unfold_in /=; case: (pmst_lonely _ _ _ _ _ s).
  rewrite -E.
  pose hd (s : 'I_L) : nat := nth 0 (ol s) 0.
  have Hhd (s : 'I_L) : P s -> hd s \in ol s.
    case/and4P => Hcl _ _ _; apply: mem_nth.
    by case: (ol s) (pmsk_ol_closer N d r0 q0 rs ps HW s (ltn_ord s) Hcl).
  have HhdL (s : 'I_L) : P s -> hd s < L.
    move=> HP; have := Hhd s HP; rewrite (pmnc_ol_mem s _ (ltn_ord s)) => /and3P [H _ _].
    exact: ltn_trans H (ltn_ord s).
  pose f (s : 'I_L) : 'I_L * bool := (insubd s (hd s), a s == a (hd s)).
  apply: (pmnc_inj_count2 _ P _ f).
    move=> s1 s2 HP1 HP2 [Hf1 Hf2].
    have E1 : hd s1 = hd s2.
      by move: (congr1 val Hf1); rewrite !val_insubd (HhdL s1 HP1) (HhdL s2 HP2).
    have R1 := Hhd s1 HP1; have R2 := Hhd s2 HP2.
    move: R1; rewrite (pmnc_ol_mem s1 _ (ltn_ord s1)) => /and3P [_ _ Hr1].
    move: R2; rewrite (pmnc_ol_mem s2 _ (ltn_ord s2)) => /and3P [_ _ Hr2].
    have Ea : a s1 = a s2.
      move: Hf2 Hr1 Hr2; rewrite E1.
      by case: eqP => [-> | _]; case: eqP => [-> | _] //= _ /eqP -> /eqP ->.
    case/and4P: HP1 => Hcl1 Hk1 Hc1 _; case/and4P: HP2 => Hcl2 Hk2 _ _.
    apply: val_inj; apply: (pmnc_old_unique s1 s2 (ltn_ord s1) (ltn_ord s2) Ea Hc1).
      exact: pmnc_rank_old (ltn_ord s1) Hcl1 Hk1.
    exact: pmnc_rank_old (ltn_ord s2) Hcl2 Hk2.
  move=> s HP; rewrite /f /= pmsk_tw_lonely val_insubd (HhdL s HP).
  case/and4P: HP => Hcl Hk Hc Hroot.
  by apply/eqP; exact: pmnc_head_lonely (ltn_ord s) Hcl Hk Hc Hroot.
(* At the root: only its second visit. *)
apply: pmnc_le1 => s1 s2 /and4P [Hcl1 Hk1 Hc1 /eqP E1] /and4P [Hcl2 Hk2 _ /eqP E2].
apply: val_inj; apply: (pmnc_old_unique s1 s2 (ltn_ord s1) (ltn_ord s2) _ Hc1).
- by rewrite E1 E2.
- exact: pmnc_rank_old (ltn_ord s1) Hcl1 Hk1.
- exact: pmnc_rank_old (ltn_ord s2) Hcl2 Hk2.
Qed.

(* The classes of the code symbols. *)
Lemma pmnc_orient s : s < L -> closer s -> p s = p (tw s).
Proof.
move=> Hs _.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
have HtL : tw s < L := pmsk_tw_lt N d q0 rs ps s Hs.
apply: (pmnm_orient_incr d _ _ _ _ _ (pmsk_tw_pair N d q0 rs ps HW s Hs)).
  by apply: pmnm_incr_nth; rewrite ?Hps.
by apply: pmnm_incr_nth; rewrite ?Hps.
Qed.

Lemma pmnc_code_Z s : s < L -> pmnc_Z (code s) = closer s && (index (tw s) (ol s) == 0).
Proof.
move=> Hs; rewrite /pmsk_code; case: ifP => Hcl //=.
rewrite (pmnc_orient s Hs Hcl) eqxx.
case: ifP => Hk /=; first by rewrite inordK.
by move: Hk; case: (index _ _).
Qed.

Lemma pmnc_code_F s : s < L -> pmnc_F (code s) = ~~ closer s && (ix (code s) == 0).
Proof.
move=> Hs; rewrite /pmsk_code; case: ifP => Hcl //=.
by rewrite /pmsk_ccode; case: ifP => _; case: ifP => _; case: ifP => _.
Qed.

Lemma pmnc_code_Fincr s : s < L -> pmnc_Fincr (code s).
Proof.
move=> Hs; rewrite /pmsk_code; case: ifP => Hcl //=.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
have Hi : (p s).1 < (p s).2 by apply: pmnm_incr_nth; rewrite ?Hps.
unfold pmsk_ccode.
case: (b s \in take s.+1 rs) => //=.
case: (has (fun q : 'I_d * 'I_d => (q.1 == (p s).1) || (q.2 == (p s).1)) (take s ps)) => //=.
by case: (has (fun q : 'I_d * 'I_d => (q.1 == (p s).2) || (q.2 == (p s).2)) (take s ps)).
Qed.

Lemma pmnc_X_le s : s < L ->
  pmnc_X (code s) <= (0 < ix (code s)) + (closer s && (0 < index (tw s) (ol s))).
Proof.
move=> Hs; rewrite /pmnc_X (pmnc_code_F s Hs) (pmnc_code_Z s Hs).
case Hcl: (closer s) => /=.
  by rewrite -lt0n; case: (0 < index _ _); rewrite ?leq_addl.
by rewrite andbT -lt0n addn0.
Qed.

(* An F step followed by a Z step. *)
Lemma pmnc_F_fresh s : s < L -> pmnc_F (code s) -> b s \notin take s.+1 rs.
Proof.
move=> Hs HF; have := pmsk_code_rf N d r0 q0 rs ps HW n s Hs.
by rewrite (pmnc_F_rf N d n (code s) HF); case: (b s \notin _).
Qed.

Lemma pmnc_FZ_tw s : s.+1 < L -> pmnc_F (code s) -> pmnc_Z (code s.+1) -> tw s.+1 = s.
Proof.
move=> Hs1 HF HZ.
have Hs : s < L := ltn_trans (ltnSn s) Hs1.
have Hfr := pmnc_F_fresh s Hs HF.
have Hcl : closer s.+1 by move: HZ; rewrite (pmnc_code_Z s.+1 Hs1) => /andP [].
have Hm := pmsk_ol_closer N d r0 q0 rs ps HW s.+1 Hs1 Hcl.
move: Hm; rewrite (pmnc_ol_mem s.+1 _ Hs1) => /and3P [Hlt _ Hrow].
have Ea : a s.+1 = b s by rewrite /pmst_a /pmst_b /pmst_succ Hs1.
have Hin u : u <= s -> nth r0 rs u \in take s.+1 rs.
  by move=> Hu; rewrite -(nth_take r0 (Hu : u < s.+1)) mem_nth // size_takel.
(* An open step at the fresh row b s, other than s, would have an old row
   there. *)
rewrite ltnS leq_eqVlt in Hlt; case/orP: Hlt => [/eqP // | Hlt].
exfalso; move: Hrow; rewrite Ea => /orP [] /eqP E; move: Hfr; rewrite E.
  by rewrite /pmst_a (Hin _ (ltnW Hlt)).
have Ht1 : (tw s.+1).+1 < L by rewrite (leq_ltn_trans Hlt Hs).
by rewrite /pmst_b /pmst_succ Ht1 (Hin _ Hlt).
Qed.

(* The next visit of the row b s after position s + 1. *)
Definition pmnc_nv (s : nat) : nat := s.+2 + find (pred1 (b s)) (drop s.+2 rs).

Lemma pmnc_nv_spec s : s.+1 < L -> b s \notin take s.+1 rs ->
  [/\ s.+1 < pmnc_nv s < L, nth r0 rs (pmnc_nv s) = b s &
      forall j, s.+1 < j < pmnc_nv s -> nth r0 rs j != b s].
Proof.
move=> Hs1 Hfr.
set v := b s.
have Ev : nth r0 rs s.+1 = v by rewrite /v /pmst_b /pmst_succ Hs1.
(* The walk is terminal, so v is visited at least twice. *)
have Hc : count_mem v rs != 1.
  have := pmst_fv_terminal N r0 rs s.+1 HT H3 (introT andP (conj (ltn0Sn s) Hs1)).
  by rewrite Ev.
have Hv : v \in rs by rewrite -Ev mem_nth.
have Hc1 : 0 < count_mem v rs by rewrite -has_count has_pred1.
have Hc2 : 1 < count_mem v rs by rewrite ltn_neqAle eq_sym Hc Hc1.
have Htake : count_mem v (take s.+2 rs) = 1.
  rewrite (take_nth r0 Hs1) -cats1 count_cat /= Ev eqxx addn0.
  have -> : count_mem v (take s.+1 rs) = 0.
    by apply/eqP; rewrite -leqn0 leqNgt -has_count has_pred1 (negbTE Hfr).
  by [].
have Hdrop : 0 < count_mem v (drop s.+2 rs).
  by move: Hc2; rewrite -{1}(cat_take_drop s.+2 rs) count_cat Htake add1n ltnS.
have Hhas : has (pred1 v) (drop s.+2 rs) by rewrite has_count.
have Hf := nth_find r0 Hhas.
have Hfs : find (pred1 v) (drop s.+2 rs) < size (drop s.+2 rs) by rewrite -has_find.
rewrite /pmnc_nv -/v; split.
- apply/andP; split; first by rewrite addSn ltnS leq_addr.
  by move: Hfs; rewrite size_drop ltn_subRL.
- by rewrite -nth_drop; exact/eqP.
- move=> j /andP [Hj1 Hj2].
  have Ej : j = s.+2 + (j - s.+2) by rewrite subnKC.
  rewrite Ej -nth_drop; apply/negbT.
  have Hi : j - s.+2 < find (pred1 v) (drop s.+2 rs) by rewrite ltn_subLR.
  exact: (@before_find _ r0 (pred1 v) _ _ Hi).
Qed.

(* The arrival at the next visit is a non-closer with an index slot. *)
Lemma pmnc_FZ_next s : s.+1 < L -> pmnc_F (code s) -> pmnc_Z (code s.+1) ->
  0 < ix (code (pmnc_nv s).-1).
Proof.
move=> Hs1 HF HZ.
have Hs : s < L := ltn_trans (ltnSn s) Hs1.
have Hfr := pmnc_F_fresh s Hs HF.
have [/andP [Ht1 HtL] Hnt Hmin] := pmnc_nv_spec s Hs1 Hfr.
set t := pmnc_nv s in Ht1 HtL Hnt Hmin *.
set g := t.-1.
have Htg : t = g.+1 by rewrite /g prednK // (leq_trans _ Ht1).
have HgL : g < L by rewrite -ltnS -Htg ltnW.
have Hsg : s < g by rewrite -ltnS -Htg.
have Hbg : b g = b s by rewrite /pmst_b /pmst_succ -Htg HtL.
have Hin u : u <= s -> nth r0 rs u \in take s.+1 rs.
  by move=> Hu; rewrite -(nth_take r0 (Hu : u < s.+1)) mem_nth // size_takel.
have Htws1 := pmnc_FZ_tw s Hs1 HF HZ.
have Htws : tw s = s.+1 by rewrite -{1}Htws1 (pmsk_tw_tw N d q0 rs ps s.+1 Hs1).
(* Before t, the row b s occurs only at position s + 1. *)
have Hpos j : j < t -> nth r0 rs j = b s -> j = s.+1.
  move=> Hjt Hj.
  case: (leqP j s) => Hjs.
    by move: Hfr; rewrite -Hj (Hin _ Hjs).
  case: (ltngtP j s.+1) => // Hj1.
    by move: Hjs; rewrite ltnNge -ltnS Hj1.
  by move: (Hmin j); rewrite Hj1 Hjt Hj eqxx => /(_ isT).
(* The arrival step g is not a closer: its twin would be s or s + 1. *)
have Hncl : ~~ closer g.
  apply/negP => Hcl.
  have Hu : tw g < g := Hcl.
  have HuL : tw g < L := ltn_trans Hu HgL.
  have Hsame := pmsk_tw_same N d r0 q0 rs ps HW g HgL.
  have Hrow : (a (tw g) == b s) || (b (tw g) == b s).
    move: Hsame; rewrite /pmst_same Hbg.
    by case/orP => /andP [/eqP E1 /eqP E2]; rewrite -?E1 -?E2 eqxx ?orbT.
  have Hu1 : (tw g).+1 < L by rewrite (leq_ltn_trans Hu HgL).
  have Hcase : tw g = s.+1 \/ tw g = s.
    case/orP: Hrow => /eqP E; first by left; apply: Hpos (ltn_trans Hu _) E; rewrite Htg.
    right; move: E; rewrite /pmst_b /pmst_succ Hu1 => E.
    by have := Hpos _ (leq_ltn_trans Hu _) E; rewrite Htg => /(_ (ltnSn _)) [].
  case: Hcase => E.
    by move: Hsg; rewrite -Htws1 -E (pmsk_tw_tw N d q0 rs ps g HgL) ltnn.
  have Eg : g = s.+1 by rewrite -Htws -E (pmsk_tw_tw N d q0 rs ps g HgL).
  have Hs2 : s.+2 < L by rewrite -Eg -Htg.
  have Hsame' := pmsk_tw_same N d r0 q0 rs ps HW s Hs; rewrite Htws in Hsame'.
  have Hl := pmst_loopfree N d r0 q0 rs ps HW s Hs.
  have Eb1 : b s.+1 = b s by rewrite -Hnt Htg Eg /pmst_b /pmst_succ Hs2.
  have Ea1 : a s.+1 = b s by rewrite /pmst_a /pmst_b /pmst_succ Hs1.
  move: Hsame'; rewrite /pmst_same Ea1 Eb1 => /orP [] /andP [/eqP E1 _].
    by move: Hl; rewrite E1 eqxx.
  by move: Hl; rewrite E1 eqxx.
(* Its row is old, so its code has an index slot. *)
have Hrf : pmsk_rf N d n (code g) = 0.
  rewrite (pmsk_code_rf N d r0 q0 rs ps HW n g HgL) Hbg.
  have Hb : b s = nth r0 rs s.+1 by rewrite /pmst_b /pmst_succ Hs1.
  have Hsg1 : s.+1 < g.+1 by rewrite ltnS.
  by rewrite Hb -(nth_take r0 Hsg1) mem_nth // size_takel // -Htg ltnW.
have Hix := pmsk_code_ix N d r0 q0 rs ps n g HgL.
rewrite (negbTE Hncl) Hrf addn0 in Hix.
have Hcf := pmnc_cf_le2 N d n (code g).
rewrite lt0n; apply/eqP => E; move: Hix; rewrite E add0n => Hc3.
by rewrite Hc3 in Hcf.
Qed.

Lemma pmnc_FZ_le :
  (\sum_(s < L) [&& s.+1 < L, pmnc_F (code s) & pmnc_Z (code s.+1)] <=
   \sum_(s < L) (0 < ix (code s)))%N.
Proof.
have Hin s u : s < L -> u <= s -> nth r0 rs u \in take s.+1 rs.
  by move=> Hs Hu; rewrite -(nth_take r0 (Hu : u < s.+1)) mem_nth // size_takel.
(* Distinct F steps have distinct fresh rows. *)
have Hfresh_inj s1 s2 : s1 < L -> s2 < L -> b s1 \notin take s1.+1 rs ->
    b s2 \notin take s2.+1 rs -> s1.+1 < L -> s2.+1 < L -> b s1 = b s2 -> s1 = s2.
  move=> Hs1 Hs2 F1 F2 H1 H2 E.
  have Eb1 : b s1 = nth r0 rs s1.+1 by rewrite /pmst_b /pmst_succ H1.
  have Eb2 : b s2 = nth r0 rs s2.+1 by rewrite /pmst_b /pmst_succ H2.
  case: (ltngtP s1 s2) => // Hlt.
    by move: F2; rewrite -E Eb1 (Hin s2 s1.+1 Hs2 Hlt).
  by move: F1; rewrite E Eb2 (Hin s1 s2.+1 Hs1 Hlt).
(* Map an F step followed by Z to the arrival at the next visit of its row. *)
apply: (pmnc_inj_count _
  (fun s : 'I_L => [&& s.+1 < L, pmnc_F (code s) & pmnc_Z (code s.+1)])
  (fun s : 'I_L => 0 < ix (code s)) (fun s => insubd s (pmnc_nv s).-1)).
  move=> s1 s2 /and3P [H1 HF1 HZ1] /and3P [H2 HF2 HZ2] Hf.
  have F1 := pmnc_F_fresh s1 (ltn_ord s1) HF1.
  have F2 := pmnc_F_fresh s2 (ltn_ord s2) HF2.
  have [/andP [Ha1 Hb1] Hn1 _] := pmnc_nv_spec s1 H1 F1.
  have [/andP [Ha2 Hb2] Hn2 _] := pmnc_nv_spec s2 H2 F2.
  have Hp1 : (pmnc_nv s1).-1 < L := leq_ltn_trans (leq_pred _) Hb1.
  have Hp2 : (pmnc_nv s2).-1 < L := leq_ltn_trans (leq_pred _) Hb2.
  have E1 : (pmnc_nv s1).-1 = (pmnc_nv s2).-1.
    by move: (congr1 val Hf); rewrite !val_insubd Hp1 Hp2.
  have E2 : pmnc_nv s1 = pmnc_nv s2.
    have Hp2' : 0 < pmnc_nv s2 := leq_ltn_trans (leq0n _) Ha2.
    by rewrite -(prednK (leq_ltn_trans (leq0n _) Ha1)) E1 prednK.
  apply: val_inj; apply: (Hfresh_inj s1 s2 (ltn_ord s1) (ltn_ord s2) F1 F2 H1 H2).
  by rewrite -Hn1 -Hn2 E2.
move=> s /and3P [H1 HF HZ] /=.
have F1 := pmnc_F_fresh s (ltn_ord s) HF.
have [/andP [_ Hb1] _ _] := pmnc_nv_spec s H1 F1.
rewrite val_insubd (leq_ltn_trans (leq_pred _) Hb1).
exact: pmnc_FZ_next H1 HF HZ.
Qed.

(* Every row except the root is visited at least twice. *)
Lemma pmnc_R_le : 2 * pmsc_R N rs <= L + 1.
Proof.
(* The root is visited at least once, every other row at least twice. *)
have HS : 2 * \sum_(v : 'I_N) (v \in rs) <=
    \sum_(v : 'I_N) count_mem v rs + \sum_(v : 'I_N) (nth r0 rs 0 == v).
  rewrite big_distrr -big_split; apply: leq_sum => v _ /=.
  case Hv: (v \in rs); last by rewrite muln0.
  have Hc : 0 < count_mem v rs by rewrite -has_count has_pred1 Hv.
  case: (eqVneq (nth r0 rs 0) v) => [_ | Hne].
    by rewrite muln1 addn1 ltnS.
  have Hi : 0 < index v rs < L.
    rewrite index_mem Hv andbT lt0n; apply/eqP => H0.
    by move: Hne; rewrite -H0 nth_index ?eqxx.
  have := pmst_fv_terminal N r0 rs (index v rs) HT H3 Hi; rewrite nth_index // => H1.
  by rewrite muln1 addn0 ltn_neqAle eq_sym H1 Hc.
have HR : \sum_(v : 'I_N) (v \in rs) = pmsc_R N rs.
  rewrite /pmsc_R -sum1_card [RHS]big_mkcond; apply: eq_bigr => v _; rewrite inE.
  by case: (v \in rs).
by rewrite HR (pmsc_count_sum N rs) (pmsc_sum_eq1 _ (nth r0 rs 0)) in HS.
Qed.

(* The exponent of a code: 2 (R - 1) + C = 2 L - e. *)
Lemma pmnc_weight_exp :
  (\sum_(s < L) (2 * pmsk_rf N d n (code s) + pmsk_cf N d n (code s)) +
   pmsc_e N d rs ps = 2 * L)%N.
Proof.
rewrite big_split -big_distrr /=.
rewrite (pmsk_sum_rf N d r0 q0 rs ps HW n) (pmsk_sum_cf N d r0 q0 rs ps HW n).
have HV := pmso_valid_bound N d rs ps HW.
have HR0 : 0 < pmsc_R N rs.
  apply/card_gt0P; exists (nth r0 rs 0); rewrite inE mem_nth //.
  exact: ltn_trans _ H3.
rewrite /pmsc_e.
move: HV HR0; set R := pmsc_R N rs; set C := pmsc_C d ps; set LL := L.
clearbody R C LL.
by rewrite -!multE -!minusE -!plusE => /leP HV /leP HR0; lia.
Qed.

Theorem pmnc_XFZ_le :
  (\sum_(s < L) pmnc_X (code s) +
   \sum_(s < L) [&& s.+1 < L, pmnc_F (code s) & pmnc_Z (code s.+1)] <=
   147 * pmsc_e N d rs ps)%N.
Proof.
have HX : \sum_(s < L) pmnc_X (code s) <=
    \sum_(s < L) (0 < ix (code s)) + \sum_(s < L) (closer s && (0 < index (tw s) (ol s))).
  by rewrite -big_split; apply: leq_sum => s _; exact: pmnc_X_le (ltn_ord s).
have HFZ := pmnc_FZ_le.
have Hix : \sum_(s < L) (0 < ix (code s)) <= \sum_(s < L) ix (code s).
  by apply: leq_sum => s _; case: (ix _).
have Hix45 := pmsk_ix_le N d r0 q0 rs ps HW n HT.
have Hrank := pmnc_rank_le.
have Hrows := pmsk_rows3 N r0 rs HT.
have Hlo := pmst_lonely_le N d r0 q0 rs ps HW HT.
have HR := pmnc_R_le.
have HC := pmst_C_le N d rs ps HW.
have HV := pmso_valid_bound N d rs ps HW.
(* With e = (L + 1 - 2 R) + (L + 1 - C) and L + 1 - C >= 1. *)
move: HX HFZ Hix Hix45 Hrank Hrows Hlo HR HC HV; rewrite /pmsc_e.
set SX := \sum_(s < L) pmnc_X (code s).
set SFZ := \sum_(s < L) [&& _, _ & _].
set S0 := \sum_(s < L) (0 < ix (code s)).
set Sr := \sum_(s < L) (closer s && _).
set Six := \sum_(s < L) ix (code s).
set S3 := \sum_(s < L) (2 < _).
set Slo := #|_|.
set R := pmsc_R N rs; set C := pmsc_C d ps; set LL := L.
clearbody SX SFZ S0 Sr Six S3 Slo R C LL.
rewrite -!multE -!minusE -!plusE.
move=> /leP HX /leP HFZ /leP Hix /leP Hix45 /leP Hrank /leP Hrows /leP Hlo /leP HR /leP HC /leP HV.
by apply/leP; lia.
Qed.

End Core.
