(* The twin code of square-free walks (G16, checkpoint B4, item 4).
   A valid walk (rs, ps) of length L <= n + 1 is coded step by step. The
   root rs_0 is kept apart. Step s, from rs_s to rs_(s+1 mod L) with label
   pair ps_s, gets one symbol (pmsk_sym):
   - a closer, whose twin u is an earlier step: the rank k < 3 of u among
     the open steps at the current row, or else u itself, with an
     orientation bit;
   - otherwise an explicit step: the target row, fresh or by index, and
     each color, fresh or by the step and side of an earlier occurrence.
   The symbol and the prefix take (s+1) rs, take s ps give back the step
   (pmsk_dec_code). So the code is injective on valid walks with the same
   root (pmsk_inj).
   No probability premise. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import PaperMainSquarefreeWalkCount PaperMainSquarefreeWalkExcess
  PaperMainSquarefreeWalkShapeOnce PaperMainSquarefreeWalkShapeTwin.

(* 1. Step symbols and their decoding from a prefix. *)
Section Decode.
Variables (N d n : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).

Definition pmsk_sym : finType :=
  ((('I_3 + 'I_n.+1) * bool) +
   (('I_N + 'I_n.+1) * ('I_d + 'I_n.+1 * bool) * ('I_d + 'I_n.+1 * bool)))%type.

Definition pmsk_share (p q : 'I_d * 'I_d) : bool :=
  [|| q.1 == p.1, q.2 == p.1, q.1 == p.2 | q.2 == p.2].

(* Step u is open in the prefix pp when no other step of pp shares a color
   with it. *)
Definition pmsk_open (pp : seq ('I_d * 'I_d)) (u : nat) : bool :=
  all (fun j => (j == u) || ~~ pmsk_share (nth q0 pp u) (nth q0 pp j)) (iota 0 (size pp)).

(* The open steps of the prefix at the current row last r0 pr. *)
Definition pmsk_olist (pr : seq 'I_N) (pp : seq ('I_d * 'I_d)) : seq nat :=
  [seq u <- iota 0 (size pp) | pmsk_open pp u &&
    ((last r0 pr == nth r0 pr u) || (last r0 pr == nth r0 pr u.+1))].

Definition pmsk_col (pp : seq ('I_d * 'I_d)) (x : 'I_d + 'I_n.+1 * bool) : 'I_d :=
  match x with
  | inl c => c
  | inr (j, b) => if b then (nth q0 pp j).1 else (nth q0 pp j).2
  end.

Definition pmsk_twin_of (pr : seq 'I_N) (pp : seq ('I_d * 'I_d)) (k : 'I_3 + 'I_n.+1) : nat :=
  match k with inl k => nth 0 (pmsk_olist pr pp) k | inr u => u end.

Definition pmsk_dec (pr : seq 'I_N) (pp : seq ('I_d * 'I_d)) (y : pmsk_sym) :
  'I_N * ('I_d * 'I_d) :=
  match y with
  | inl (k, b) =>
      let u := pmsk_twin_of pr pp k in
      (if last r0 pr == nth r0 pr u then nth r0 pr u.+1 else nth r0 pr u,
       pmso_orient d b (nth q0 pp u))
  | inr (x, c1, c2) =>
      (match x with inl v => v | inr j => nth r0 pr j end, (pmsk_col pp c1, pmsk_col pp c2))
  end.

End Decode.

(* 2. The twin of a step. *)
Section Code.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Variables (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).
Variable HW : pmso_valid N d rs ps.

Local Notation L := (size rs).
Local Notation a := (pmst_a N r0 rs).
Local Notation b := (pmst_b N r0 rs).
Local Notation p := (pmst_p d q0 ps).
Local Notation pin := (pmst_in d q0 ps).
Local Notation nc := (pmst_n N d q0 rs ps).
Local Notation twin := (pmst_twin N d q0 rs ps).

Lemma pmsk_two_only (c : 'I_d) (s t u : nat) : s < L -> t < L -> u < L -> s != t ->
  pin c s -> pin c t -> nc c = 2 -> pin c u -> (u == s) || (u == t).
Proof.
move=> Hs Ht Hu Hst Hcs Hct Hn Hcu.
have := pmst_two N d q0 rs ps c s t (fun v => nat_of_bool (v == u)) Hs Ht Hst Hcs Hct Hn.
rewrite (bigD1 (Ordinal Hu)) //= eqxx Hcu big1 ?addn0.
  move=> i Hi; case: (eqVneq (i : nat) u) => [Hiu | ]; last by rewrite mul0n.
  by move: Hi; rewrite (_ : i = Ordinal Hu) ?eqxx //; apply: val_inj.
by rewrite [s == u]eq_sym [t == u]eq_sym; case: (u == s); case: (u == t).
Qed.

Lemma pmsk_twin_lt s t : twin s t -> t < L.
Proof. by case/and5P. Qed.

Lemma pmsk_twin_neq s t : twin s t -> s != t.
Proof. by case/and5P. Qed.

Lemma pmsk_twin_in s t : twin s t -> forall c, pin c s = pin c t.
Proof. by case/and5P => _ _ /forallP H _ _ c; exact: (eqP (H c)). Qed.

Lemma pmsk_twin_n1 s t : twin s t -> nc (p s).1 = 2.
Proof. by case/and5P => _ _ _ /eqP. Qed.

Lemma pmsk_twin_n2 s t : twin s t -> nc (p s).2 = 2.
Proof. by case/and5P => _ _ _ _ /eqP. Qed.

Lemma pmsk_twin_sym s t : s < L -> twin s t -> twin t s.
Proof.
move=> Hs Hst; have Hin := pmsk_twin_in s t Hst.
have H1 := pmsk_twin_n1 s t Hst; have H2 := pmsk_twin_n2 s t Hst.
have Hc (c : 'I_d) : pin c t -> nc c = 2.
  by rewrite -Hin pmst_in_p => /orP [/eqP <- | /eqP <-].
apply/and5P; split.
- by rewrite eq_sym; exact: pmsk_twin_neq Hst.
- exact: Hs.
- by apply/forallP => c; rewrite Hin.
- by apply/eqP; apply: Hc; rewrite pmst_in_p eqxx.
- by apply/eqP; apply: Hc; rewrite pmst_in_p eqxx orbT.
Qed.

Lemma pmsk_twin_unique s t t' : s < L -> twin s t -> twin s t' -> t = t'.
Proof.
move=> Hs Ht Ht'.
have Hcs : pin (p s).1 s by rewrite pmst_in_p eqxx.
have Hct : pin (p s).1 t by rewrite -(pmsk_twin_in s t Ht).
have Hct' : pin (p s).1 t' by rewrite -(pmsk_twin_in s t' Ht').
have := pmsk_two_only (p s).1 s t t' Hs (pmsk_twin_lt s t Ht) (pmsk_twin_lt s t' Ht')
  (pmsk_twin_neq s t Ht) Hcs Hct (pmsk_twin_n1 s t Ht) Hct'.
case/orP => /eqP // Hs'; by move: (pmsk_twin_neq s t' Ht'); rewrite Hs' eqxx.
Qed.

Definition pmsk_tw (s : nat) : nat :=
  if [pick t : 'I_L | twin s t] is Some t then val t else s.

Lemma pmsk_tw_twin s t : s < L -> twin s t -> pmsk_tw s = t.
Proof.
move=> Hs Ht; rewrite /pmsk_tw; case: pickP => [t0 Ht0 | Hno].
  by apply: pmsk_twin_unique Hs Ht0 Ht.
by have := Hno (Ordinal (pmsk_twin_lt s t Ht)); rewrite /= Ht.
Qed.

Lemma pmsk_tw_none s : (forall t : 'I_L, ~~ twin s t) -> pmsk_tw s = s.
Proof.
move=> Hno; rewrite /pmsk_tw; case: pickP => [t0 Ht0 | //].
by move: (Hno t0); rewrite Ht0.
Qed.

Lemma pmsk_tw_lt s : s < L -> pmsk_tw s < L.
Proof. by rewrite /pmsk_tw; case: pickP => [t _ _ | _ //]; exact: ltn_ord. Qed.

Lemma pmsk_tw_spec s : pmsk_tw s != s -> twin s (pmsk_tw s).
Proof. by rewrite /pmsk_tw; case: pickP => [t Ht _ | _] //; rewrite eqxx. Qed.

Lemma pmsk_tw_tw s : s < L -> pmsk_tw (pmsk_tw s) = s.
Proof.
move=> Hs; case: (eqVneq (pmsk_tw s) s) => [E | Ne]; first by rewrite !E.
apply: pmsk_tw_twin; first exact: pmsk_tw_lt.
exact: pmsk_twin_sym Hs (pmsk_tw_spec s Ne).
Qed.

Lemma pmsk_tw_lonely (s : 'I_L) : pmst_lonely N d q0 rs ps s = (pmsk_tw s == s).
Proof.
rewrite /pmst_lonely; case: existsP => [[t Ht] | Hno] /=.
  rewrite (pmsk_tw_twin s t (ltn_ord s) Ht) eq_sym.
  exact/esym/negbTE/(pmsk_twin_neq s t Ht).
by rewrite pmsk_tw_none ?eqxx // => t; apply/negP => Ht; apply: Hno; exists t.
Qed.

Lemma pmsk_tw_same s : s < L -> pmst_same N r0 rs s (pmsk_tw s).
Proof.
move=> Hs; case: (eqVneq (pmsk_tw s) s) => [-> | Ne]; first exact: pmst_same_refl.
have Ht := pmsk_tw_spec s Ne.
have Hcs : pin (p s).1 s by rewrite pmst_in_p eqxx.
apply: (pmst_partner N d r0 q0 rs ps HW (p s).1 s (pmsk_tw s) Hs (pmsk_tw_lt s Hs)) => //.
- by rewrite eq_sym.
- by rewrite -(pmsk_twin_in s _ Ht).
- exact: pmsk_twin_n1 Ht.
Qed.

(* Two distinct pairs with the same colors are equal up to order. *)
Lemma pmsk_orient_eq (x y : 'I_d * 'I_d) : x.1 != x.2 -> y.1 != y.2 ->
  (forall c, ((x.1 == c) || (x.2 == c)) = ((y.1 == c) || (y.2 == c))) ->
  x = pmso_orient d (x == y) y.
Proof.
case: x => x1 x2; case: y => y1 y2 /= Hx Hy H.
have H1 := H x1; have H2 := H x2; rewrite eqxx /= in H1; rewrite eqxx orbT in H2.
case: eqP => [E | Ne]; first by rewrite /pmso_orient.
rewrite /pmso_orient /=.
case: (eqVneq y1 x1) H1 H2 Ne => [E1 | N1] /= H1 H2 Ne.
  by move: H2; rewrite E1 (negbTE Hx) /= => /esym /eqP E2; case: Ne; rewrite E1 E2.
move: H1 => /esym /eqP E1; move: H2; rewrite E1 (negbTE Hx) orbF => /esym /eqP E2.
by rewrite E2.
Qed.

Lemma pmsk_tw_pair s : s < L -> p s = pmso_orient d (p s == p (pmsk_tw s)) (p (pmsk_tw s)).
Proof.
move=> Hs; apply: pmsk_orient_eq.
- exact: pmst_distinct N d q0 rs ps HW s Hs.
- exact: pmst_distinct N d q0 rs ps HW _ (pmsk_tw_lt s Hs).
move=> c; rewrite -!pmst_in_p.
case: (eqVneq (pmsk_tw s) s) => [-> // | Ne].
exact: pmsk_twin_in (pmsk_tw_spec s Ne) c.
Qed.

Definition pmsk_closer (s : nat) : bool := pmsk_tw s < s.
Definition pmsk_opener (s : nat) : bool := s < pmsk_tw s.

(* 3. The open steps at a closer. *)
Definition pmsk_ol (s : nat) : seq nat := pmsk_olist N d r0 q0 (take s.+1 rs) (take s ps).

Lemma pmsk_last_take s : s < L -> last r0 (take s.+1 rs) = a s.
Proof. by move=> Hs; rewrite -nth_last size_takel // nth_take. Qed.

Lemma pmsk_ol_closer s : s < L -> pmsk_closer s -> pmsk_tw s \in pmsk_ol s.
Proof.
move=> Hs Hcl; have Hus : pmsk_tw s < s := Hcl.
have Hne : pmsk_tw s != s by rewrite neq_ltn Hus.
have Ht := pmsk_tw_spec s Hne; have HuL : pmsk_tw s < L := ltn_trans Hus Hs.
have Hts := pmsk_twin_sym s _ Hs Ht.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
have Hsz : size (take s ps) = s by rewrite size_takel // Hps ltnW.
rewrite /pmsk_ol /pmsk_olist mem_filter mem_iota Hsz add0n Hus andbT.
rewrite leq0n andbT; apply/andP; split.
  rewrite /pmsk_open Hsz; apply/allP => j; rewrite mem_iota add0n => /andP [_ Hj].
  rewrite !nth_take //; case: (eqVneq j (pmsk_tw s)) => [// | Nju] /=; apply/negP => Hsh.
  have HjL : j < L := ltn_trans Hj Hs.
  have Hc (c : 'I_d) : c \in [:: (p (pmsk_tw s)).1; (p (pmsk_tw s)).2] -> pin c j -> False.
    rewrite !inE => Hc Hcj.
    have Hcu : pin c (pmsk_tw s).
      by rewrite pmst_in_p; case/orP: Hc => /eqP ->; rewrite eqxx ?orbT.
    have Hn : nc c = 2.
      by case/orP: Hc => /eqP ->; [exact: pmsk_twin_n1 Hts | exact: pmsk_twin_n2 Hts].
    have := pmsk_two_only c _ s j HuL Hs HjL (Hne) Hcu _ Hn Hcj.
    have Hcs : pin c s by rewrite -(pmsk_twin_in _ s Hts c).
    move=> /(_ Hcs); rewrite (negbTE Nju) /= => /eqP Ejs; by move: Hj; rewrite Ejs ltnn.
  move: Hsh; rewrite /pmsk_share => /or4P [] H.
  - by apply: (Hc (p (pmsk_tw s)).1); rewrite ?inE ?eqxx // pmst_in_p /pmst_p H.
  - by apply: (Hc (p (pmsk_tw s)).1); rewrite ?inE ?eqxx // pmst_in_p /pmst_p H orbT.
  - by apply: (Hc (p (pmsk_tw s)).2); rewrite ?inE ?eqxx ?orbT // pmst_in_p /pmst_p H.
  - by apply: (Hc (p (pmsk_tw s)).2); rewrite ?inE ?eqxx ?orbT // pmst_in_p /pmst_p H orbT.
have H1 : nth r0 (take s.+1 rs) (pmsk_tw s) = a (pmsk_tw s) by rewrite nth_take // ltnS ltnW.
have H2 : nth r0 (take s.+1 rs) (pmsk_tw s).+1 = b (pmsk_tw s).
  by rewrite nth_take ?ltnS // /pmst_b /pmst_succ (leq_ltn_trans Hus Hs).
rewrite pmsk_last_take // H1 H2; have := pmsk_tw_same s Hs; rewrite /pmst_same.
by case/orP => /andP [/eqP -> _]; rewrite eqxx ?orbT.
Qed.

Lemma pmsk_ol_size s : s < L -> size (pmsk_ol s) < 2 * count_mem (a s) rs.
Proof.
move=> Hs; have Hps : size ps = L := pmst_size_ps N d rs ps HW.
have Hsz : size (take s ps) = s by rewrite size_takel // Hps ltnW.
rewrite /pmsk_ol /pmsk_olist size_filter Hsz pmsk_last_take //.
set v := a s.
have E1 : count (fun u => v == nth r0 rs u) (iota 0 s) = count_mem v (take s rs).
  by rewrite -(map_nth_iota0 r0 (ltnW Hs)) count_map; apply: eq_count => u /=; rewrite eq_sym.
have E2 : count (fun u => v == nth r0 rs u.+1) (iota 0 s) = count_mem v (take s (behead rs)).
  have Hb : s <= size (behead rs) by rewrite size_behead -ltnS (ltn_predK Hs).
  rewrite -(map_nth_iota0 r0 Hb) count_map.
  by apply: eq_count => u /=; rewrite eq_sym nth_behead.
have E3 : {in iota 0 s, (fun u => pmsk_open d q0 (take s ps) u &&
    ((v == nth r0 (take s.+1 rs) u) || (v == nth r0 (take s.+1 rs) u.+1))) =1
  (fun u => pmsk_open d q0 (take s ps) u && ((v == nth r0 rs u) || (v == nth r0 rs u.+1)))}.
  move=> u; rewrite mem_iota add0n => /andP [_ Hu].
  have Hu1 : u < s.+1 by rewrite ltnS ltnW.
  have Hu2 : u.+1 < s.+1 by rewrite ltnS.
  by rewrite (nth_take _ Hu1) (nth_take _ Hu2).
rewrite (eq_in_count E3).
apply: (@leq_ltn_trans (count (fun u => v == nth r0 rs u) (iota 0 s) +
  count (fun u => v == nth r0 rs u.+1) (iota 0 s))).
  rewrite -count_predUI; apply: leq_trans (leq_addr _ _).
  by apply: sub_count => u /andP [_ H]; exact: H.
rewrite E1 E2 mul2n -addnn.
have Hlt : count_mem v (take s rs) < count_mem v rs.
  rewrite -{2}(cat_take_drop s rs) count_cat (drop_nth r0 Hs).
  by rewrite -[X in X < _]addn0 ltn_add2l /= (_ : nth r0 rs s = v) // eqxx.
have Hle : count_mem v (take s (behead rs)) <= count_mem v rs.
  apply: (@leq_trans (count_mem v (behead rs))).
    by rewrite -{2}(cat_take_drop s (behead rs)) count_cat leq_addr.
  by case: (rs) => //= x t; rewrite leq_addl.
by apply: leq_ltn_trans (leq_add (leqnn _) Hle) _; rewrite ltn_add2r.
Qed.

(* 4. The code of a step, and its decoding. *)
Variable n : nat.
Variable Hn : L <= n.+1.

Local Notation hasc c := (fun q : 'I_d * 'I_d => (q.1 == c) || (q.2 == c)).

Definition pmsk_ccode (s : nat) (c : 'I_d) : 'I_d + 'I_n.+1 * bool :=
  if has (hasc c) (take s ps) then
    inr (inord (find (hasc c) ps), (nth q0 ps (find (hasc c) ps)).1 == c)
  else inl c.

Definition pmsk_code (s : nat) : pmsk_sym N d n :=
  if pmsk_closer s then
    inl (if index (pmsk_tw s) (pmsk_ol s) < 3 then inl (inord (index (pmsk_tw s) (pmsk_ol s)))
         else inr (inord (pmsk_tw s)), p s == p (pmsk_tw s))
  else
    inr (if b s \in take s.+1 rs then inr (inord (index (b s) rs)) else inl (b s),
         pmsk_ccode s (p s).1, pmsk_ccode s (p s).2).

Lemma pmsk_index_take (x : 'I_N) k : x \in take k rs -> index x rs < k.
Proof.
move=> Hx; rewrite -(cat_take_drop k rs) index_cat Hx.
apply: leq_trans (_ : size (take k rs) <= k); rewrite ?index_mem // size_take.
by case: ifP => // /negbT; rewrite -leqNgt.
Qed.

Lemma pmsk_b_in s : s < L -> b s \in rs.
Proof. by move=> Hs; rewrite /pmst_b mem_nth // pmst_succ_lt. Qed.

Lemma pmsk_ccode_dec s c : s < L -> pmsk_col d n q0 (take s ps) (pmsk_ccode s c) = c.
Proof.
move=> Hs; rewrite /pmsk_ccode; case: ifP => // Hh.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
have Hf : find (hasc c) ps = find (hasc c) (take s ps).
  by rewrite -{1}(cat_take_drop s ps) find_cat Hh.
have Hfs : find (hasc c) ps < s.
  rewrite Hf; apply: leq_trans (_ : size (take s ps) <= s); rewrite -?has_find //.
  by rewrite size_takel // Hps ltnW.
have HfL : find (hasc c) ps < n.+1 by apply: leq_trans Hn; exact: ltn_trans Hfs Hs.
rewrite /pmsk_col inordK // nth_take //.
have Hhas : has (hasc c) ps by rewrite has_find; apply: leq_trans Hfs _; rewrite Hps ltnW.
have := nth_find q0 Hhas.
by case: (eqVneq (nth q0 ps (find (hasc c) ps)).1 c) => [-> | N1] //= /eqP.
Qed.

Lemma pmsk_dec_closer s : s < L -> pmsk_closer s ->
  (if a s == a (pmsk_tw s) then b (pmsk_tw s) else a (pmsk_tw s)) = b s.
Proof.
move=> Hs Hcl; have Hus : pmsk_tw s < s := Hcl; have HuL : pmsk_tw s < L := ltn_trans Hus Hs.
have Hlu := pmst_loopfree N d r0 q0 rs ps HW _ HuL.
have := pmsk_tw_same s Hs; rewrite /pmst_same.
case: (eqVneq (a s) (a (pmsk_tw s))) => [E | Ne] /=.
  case/orP => [/eqP -> // | /andP [/eqP E1 _]]; by move: Hlu; rewrite -E E1 eqxx.
by case/andP => _ /eqP ->.
Qed.

Lemma pmsk_dec_code s : s < L ->
  pmsk_dec N d n r0 q0 (take s.+1 rs) (take s ps) (pmsk_code s) = (b s, p s).
Proof.
move=> Hs; have Hps : size ps = L := pmst_size_ps N d rs ps HW.
rewrite /pmsk_code; case: ifP => Hcl.
  have Hus : pmsk_tw s < s := Hcl; have HuL : pmsk_tw s < L := ltn_trans Hus Hs.
  set k := (if _ then _ else _).
  have Hu : pmsk_twin_of N d n r0 q0 (take s.+1 rs) (take s ps) k = pmsk_tw s.
    rewrite /k; case: ifP => Hk /=.
      by rewrite inordK //; exact: nth_index (pmsk_ol_closer s Hs Hcl).
    by rewrite inordK // (leq_trans HuL Hn).
  rewrite /pmsk_dec Hu.
  have H1 : nth r0 (take s.+1 rs) (pmsk_tw s) = a (pmsk_tw s) by rewrite nth_take // ltnS ltnW.
  have H2 : nth r0 (take s.+1 rs) (pmsk_tw s).+1 = b (pmsk_tw s).
    by rewrite nth_take ?ltnS // /pmst_b /pmst_succ (leq_ltn_trans Hus Hs).
  rewrite pmsk_last_take // H1 H2 nth_take // (pmsk_dec_closer s Hs Hcl).
  by congr (_, _); rewrite -/(p (pmsk_tw s)) -pmsk_tw_pair.
have Hcol c : pmsk_col d n q0 (take s ps) (pmsk_ccode s c) = c := pmsk_ccode_dec s c Hs.
case: ifP => Hb; rewrite /pmsk_dec; cbv beta iota; rewrite !Hcol -surjective_pairing //.
have Hi := pmsk_index_take (b s) s.+1 Hb.
have HiL : index (b s) rs < n.+1 by apply: leq_trans Hn; rewrite index_mem pmsk_b_in.
by rewrite inordK // nth_take // nth_index // pmsk_b_in.
Qed.

End Code.

(* 5. The code and the root determine the walk. *)
Theorem pmsk_inj (N d n : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d) (rs rs' : seq 'I_N)
    (ps ps' : seq ('I_d * 'I_d)) :
  pmso_valid N d rs ps -> pmso_valid N d rs' ps' -> size rs = size rs' ->
  size rs <= n.+1 -> nth r0 rs 0 = nth r0 rs' 0 ->
  (forall s, s < size rs -> pmsk_code N d r0 q0 rs ps n s = pmsk_code N d r0 q0 rs' ps' n s) ->
  rs = rs' /\ ps = ps'.
Proof.
move=> HW HW' HL Hn H0 Hc.
have Hps := pmst_size_ps N d rs ps HW; have Hps' := pmst_size_ps N d rs' ps' HW'.
have Hn' : size rs' <= n.+1 by rewrite -HL.
case: (posnP (size rs)) => [L0 | LP].
  have E1 : rs = [::] by apply/eqP; rewrite -size_eq0 L0.
  have E2 : rs' = [::] by apply/eqP; rewrite -size_eq0 -HL L0.
  have E3 : ps = [::] by apply/eqP; rewrite -size_eq0 Hps L0.
  have E4 : ps' = [::] by apply/eqP; rewrite -size_eq0 Hps' -HL L0.
  by rewrite E1 E2 E3 E4.
have Step k : k < size rs -> take k.+1 rs = take k.+1 rs' -> take k ps = take k ps' ->
    pmst_b N r0 rs k = pmst_b N r0 rs' k /\ pmst_p d q0 ps k = pmst_p d q0 ps' k.
  move=> Hk E1 E2.
  have Hk' : k < size rs' by rewrite -HL.
  have D := pmsk_dec_code N d r0 q0 rs ps HW n Hn k Hk.
  have D' := pmsk_dec_code N d r0 q0 rs' ps' HW' n Hn' k Hk'.
  by rewrite E1 E2 (Hc k Hk) D' in D; case: D => -> ->.
have Key k : k < size rs -> take k.+1 rs = take k.+1 rs' /\ take k ps = take k ps'.
  elim: k => [|k IH] Hk.
    by rewrite !take0 (take_nth r0 Hk) (take_nth r0 (_ : 0 < size rs')) -?HL // !take0 H0.
  have [E1 E2] := IH (ltnW Hk).
  have [Eb Ep] := Step k (ltnW Hk) E1 E2.
  have Hk' : k.+1 < size rs' by rewrite -HL.
  split.
    rewrite (take_nth r0 Hk) (take_nth r0 Hk') E1; congr rcons.
    by move: Eb; rewrite /pmst_b /pmst_succ Hk Hk'.
  rewrite (take_nth q0 (_ : k < size ps)) ?(take_nth q0 (_ : k < size ps'))
    ?E2 ?Hps ?Hps' -?HL ?(ltnW Hk) //.
  by move: Ep; rewrite /pmst_p => ->.
have Hl : (size rs).-1 < size rs by rewrite ltn_predL.
have [E1 E2] := Key _ Hl; have [_ Ep] := Step _ Hl E1 E2.
split.
  by rewrite -(take_size rs) -(take_size rs') -HL -(prednK LP) E1.
rewrite -(take_size ps) -(take_size ps') Hps Hps' -HL -(prednK LP).
rewrite (take_nth q0 (_ : (size rs).-1 < size ps)) ?Hps //.
rewrite (take_nth q0 (_ : (size rs).-1 < size ps')) ?Hps' -?HL //.
by rewrite E2; move: Ep; rewrite /pmst_p => ->.
Qed.

(* Part 2: fresh values and index slots of the code.
   For a valid walk of length L <= n + 1, summed over the steps:
   - the fresh rows number R - 1, since the root has no fresh arrival
     (pmsk_sum_rf);
   - the fresh colors number C (pmsk_sum_cf);
   - for a terminal walk, the index slots number at most 45 e (pmsk_ix_le).
     Openers and closers pair up (pmsk_pair), so
     2 #idx = e + (L - C) + 3 #lonely + 2 #explicit. There are at most
     27 e lonely steps (pmst_lonely_le), and an explicit twin index occurs
     only at a row visited at least 3 times: at most 3 (L + 1 - 2 R)
     positions, because the root may be visited once and every other row
     at least twice (pmsk_rows3). *)

(* 6. Fresh values and index slots of a symbol. *)
Definition pmsk_cfx (d n : nat) (x : 'I_d + 'I_n.+1 * bool) : nat := if x is inl _ then 1 else 0.

Definition pmsk_rf (N d n : nat) (y : pmsk_sym N d n) : nat :=
  if y is inr (inl _, _, _) then 1 else 0.

Definition pmsk_cf (N d n : nat) (y : pmsk_sym N d n) : nat :=
  if y is inr (_, c1, c2) then pmsk_cfx d n c1 + pmsk_cfx d n c2 else 0.

Definition pmsk_ix (N d n : nat) (y : pmsk_sym N d n) : nat :=
  match y with
  | inl (inl _, _) => 0
  | inl (inr _, _) => 1
  | inr (x, c1, c2) =>
      (if x is inr _ then 1 else 0) + (1 - pmsk_cfx d n c1) + (1 - pmsk_cfx d n c2)
  end.

Local Notation pmsk_hasc c := (fun q => (q.1 == c) || (q.2 == c)).

Lemma pmsk_R_rcons (N : nat) (pr : seq 'I_N) (x : 'I_N) :
  pmsc_R N (rcons pr x) = pmsc_R N pr + (x \notin pr).
Proof.
rewrite /pmsc_R (@eq_card _ _ [predU1 x & [pred r : 'I_N | r \in pr]]).
  by move=> r; rewrite !inE mem_rcons inE.
by rewrite cardU1 addnC inE.
Qed.

Lemma pmsk_C_rcons (d : nat) (pp : seq ('I_d * 'I_d)) (q : 'I_d * 'I_d) : q.1 != q.2 ->
  pmsc_C d (rcons pp q) = pmsc_C d pp + ~~ has (pmsk_hasc q.1) pp + ~~ has (pmsk_hasc q.2) pp.
Proof.
move=> Hq; rewrite /pmsc_C (@eq_card _ _
  [predU1 q.1 & [predU1 q.2 & [pred c : 'I_d | has (pmsk_hasc c) pp]]]).
  by move=> c; rewrite !inE has_rcons /= [c == q.1]eq_sym [c == q.2]eq_sym orbA.
rewrite cardU1 cardU1 !inE (negbTE Hq) /=.
by rewrite addnA addnC addnA.
Qed.

Lemma pmsk_sum_count (T : finType) (s : seq T) (F : T -> nat) :
  \sum_(x <- s) F x = \sum_(v : T) count_mem v s * F v.
Proof.
elim: s => [|x s IH].
  by rewrite big_nil big1 // => v _.
rewrite big_cons IH [RHS](eq_bigr (fun v => (x == v) * F v + count_mem v s * F v)).
  by move=> v _ /=; rewrite mulnDl.
rewrite big_split /=; congr (_ + _).
rewrite (bigD1 x) //= eqxx mul1n big1 ?addn0 //.
by move=> v Hv; rewrite eq_sym (negbTE Hv) mul0n.
Qed.

(* 7. The counts for the code of a walk. *)
Section Cost.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Variables (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).
Variable HW : pmso_valid N d rs ps.
Variable n : nat.
Variable Hn : size rs <= n.+1.

Local Notation L := (size rs).
Local Notation a := (pmst_a N r0 rs).
Local Notation b := (pmst_b N r0 rs).
Local Notation p := (pmst_p d q0 ps).
Local Notation pin := (pmst_in d q0 ps).
Local Notation tw := (pmsk_tw N d q0 rs ps).
Local Notation closer := (pmsk_closer N d q0 rs ps).
Local Notation opener := (pmsk_opener N d q0 rs ps).
Local Notation code := (pmsk_code N d r0 q0 rs ps n).
Local Notation ol := (pmsk_ol N d r0 q0 rs ps).

Lemma pmsk_closer_old s : s < L -> closer s -> b s \in take s.+1 rs.
Proof.
move=> Hs Hcl; have Hus : tw s < s := Hcl.
rewrite -(pmsk_dec_closer N d r0 q0 rs ps HW s Hs Hcl).
have Hin j : j <= s -> nth r0 rs j \in take s.+1 rs.
  move=> Hj; have Hj' : j < s.+1 by rewrite ltnS.
  by rewrite -(nth_take r0 Hj') mem_nth // size_takel.
case: ifP => _; last exact: Hin (ltnW Hus).
by rewrite /pmst_b /pmst_succ (leq_ltn_trans Hus Hs); exact: Hin.
Qed.

Lemma pmsk_closer_cols s c : s < L -> closer s -> pin c s -> has (pmsk_hasc c) (take s ps).
Proof.
move=> Hs Hcl Hc; have Hus : tw s < s := Hcl.
have Hne : tw s != s by rewrite neq_ltn Hus.
have Ht := pmsk_tw_spec N d q0 rs ps s Hne.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
apply/hasP; exists (nth q0 ps (tw s)).
  by rewrite -(nth_take q0 Hus) mem_nth // size_takel // Hps ltnW.
by rewrite -/(p (tw s)) -pmst_in_p -(pmsk_twin_in N d q0 rs ps s _ Ht).
Qed.

Lemma pmsk_code_rf s : s < L -> pmsk_rf N d n (code s) = (b s \notin take s.+1 rs).
Proof.
move=> Hs; rewrite /pmsk_code; case: ifP => Hcl.
  by rewrite (pmsk_closer_old s Hs Hcl).
by case: ifP.
Qed.

Lemma pmsk_code_cf s : s < L -> pmsk_cf N d n (code s) =
  ~~ has (pmsk_hasc (p s).1) (take s ps) + ~~ has (pmsk_hasc (p s).2) (take s ps).
Proof.
move=> Hs; rewrite /pmsk_code; case: ifP => Hcl.
  rewrite (pmsk_closer_cols s (p s).1 Hs Hcl) ?(pmsk_closer_cols s (p s).2 Hs Hcl) //.
    by rewrite pmst_in_p eqxx.
  by rewrite pmst_in_p eqxx orbT.
by rewrite /pmsk_cf /pmsk_ccode; case: ifP; case: ifP.
Qed.

Lemma pmsk_code_ix s : s < L ->
  pmsk_ix N d n (code s) + pmsk_rf N d n (code s) + pmsk_cf N d n (code s) =
  if closer s then nat_of_bool (3 <= index (tw s) (ol s)) else 3.
Proof.
move=> Hs; rewrite /pmsk_code; case: ifP => Hcl.
  by case: ifP => Hk; rewrite /= ?addn0; [rewrite leqNgt Hk | rewrite leqNgt Hk].
rewrite /pmsk_ix /pmsk_rf /pmsk_cf /pmsk_cfx /pmsk_ccode.
by case: ifP; case: ifP; case: ifP.
Qed.

Lemma pmsk_R_take k : k <= L ->
  pmsc_R N (take k rs) = \sum_(0 <= s < k) (nth r0 rs s \notin take s rs).
Proof.
elim: k => [|k IH] Hk.
  by rewrite take0 big_geq // /pmsc_R; apply: eq_card0 => r; rewrite inE.
by rewrite (take_nth r0 Hk) pmsk_R_rcons IH ?(ltnW Hk) // big_nat_recr.
Qed.

Theorem pmsk_sum_rf : \sum_(s < L) pmsk_rf N d n (code s) = pmsc_R N rs - 1.
Proof.
rewrite (eq_bigr (fun s : 'I_L => nat_of_bool (b s \notin take s.+1 rs))).
  by move=> s _; rewrite pmsk_code_rf.
rewrite -(big_mkord xpredT (fun s => nat_of_bool (b s \notin take s.+1 rs))).
have := pmsk_R_take L (leqnn _); rewrite take_size => ->.
case E: L => [|L']; first by rewrite !big_geq.
rewrite big_nat_recr // big_nat_recl // take0 in_nil /= add1n subn1 /=.
have Hb0 : b L' = nth r0 rs 0 by rewrite /pmst_b /pmst_succ E ltnn.
have Hin0 : nth r0 rs 0 \in take L'.+1 rs by rewrite -E take_size mem_nth // E.
rewrite Hb0 Hin0 addn0; apply: eq_big_nat => i /andP [_ Hi].
by rewrite /pmst_b /pmst_succ E ltnS Hi.
Qed.

Lemma pmsk_C_take k : k <= L -> pmsc_C d (take k ps) =
  \sum_(0 <= s < k) (~~ has (pmsk_hasc (p s).1) (take s ps) + ~~ has (pmsk_hasc (p s).2) (take s ps)).
Proof.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
elim: k => [|k IH] Hk.
  by rewrite take0 big_geq // /pmsc_C; apply: eq_card0 => c; rewrite inE.
have Hk' : k < size ps by rewrite Hps.
rewrite (take_nth q0 Hk') pmsk_C_rcons; first exact: pmst_distinct N d q0 rs ps HW k Hk.
by rewrite IH ?(ltnW Hk) // big_nat_recr //= addnA.
Qed.

Theorem pmsk_sum_cf : \sum_(s < L) pmsk_cf N d n (code s) = pmsc_C d ps.
Proof.
have Hps : size ps = L := pmst_size_ps N d rs ps HW.
rewrite (eq_bigr (fun s : 'I_L => ~~ has (pmsk_hasc (p s).1) (take s ps) +
  ~~ has (pmsk_hasc (p s).2) (take s ps))); first by move=> s _; rewrite pmsk_code_cf.
rewrite -(big_mkord xpredT (fun s => ~~ has (pmsk_hasc (p s).1) (take s ps) +
  ~~ has (pmsk_hasc (p s).2) (take s ps))).
by have := pmsk_C_take L (leqnn _); rewrite -Hps take_size => ->.
Qed.

(* Openers and closers pair up. *)
Lemma pmsk_pair : \sum_(s < L) closer s = \sum_(s < L) opener s.
Proof.
have Htw (s : 'I_L) : tw s < L := pmsk_tw_lt N d q0 rs ps s (ltn_ord s).
pose f (s : 'I_L) : 'I_L := Ordinal (Htw s).
have Hf : involutive f by move=> s; apply: val_inj; rewrite /= pmsk_tw_tw.
rewrite (reindex_inj (inv_inj Hf)) /=; apply: eq_bigr => s _.
by rewrite /pmsk_closer /pmsk_opener /= pmsk_tw_tw.
Qed.

Lemma pmsk_three s : closer s + opener s + (tw s == s) = 1.
Proof. by rewrite /pmsk_closer /pmsk_opener; case: ltngtP. Qed.

(* An explicit twin index occurs only at a row visited at least 3 times. *)
Lemma pmsk_su s : s < L -> closer s -> 3 <= index (tw s) (ol s) -> 3 <= count_mem (a s) rs.
Proof.
move=> Hs Hcl Hk.
have H1 : index (tw s) (ol s) < size (ol s).
  by rewrite index_mem; exact: pmsk_ol_closer N d r0 q0 rs ps HW s Hs Hcl.
have H2 := pmsk_ol_size N d r0 q0 rs ps HW s Hs.
by move: Hk H1 H2; rewrite -!multE => /leP Hk /leP H1 /leP H2; apply/leP; lia.
Qed.

Lemma pmsk_rows3 : pmso_fv N rs = L ->
  \sum_(s < L) (3 <= count_mem (a s) rs) <= 3 * (L + 1 - 2 * pmsc_R N rs).
Proof.
move=> HT; case: (leqP L 2) => HL2.
  rewrite big1 // => s _; have := count_size (pred1 (a s)) rs.
  by move=> Hc; apply/eqP; rewrite eqb0 -leqNgt; exact: leq_trans Hc HL2.
have E : \sum_(s < L) (3 <= count_mem (a s) rs) = \sum_(x <- rs) (3 <= count_mem x rs).
  by rewrite (big_nth r0) big_mkord.
rewrite E pmsk_sum_count.
apply: (@leq_trans (\sum_(v : 'I_N) 3 * (count_mem v rs - 2))).
  apply: leq_sum => v _; case: (leqP 3 (count_mem v rs)) => H; rewrite ?muln0 ?muln1 //.
  move: H; set c := count_mem v rs => H; clearbody c.
  by move: H; rewrite -!multE -!minusE => /leP H; apply/leP; lia.
rewrite -big_distrr leq_mul2l /=.
have HS : \sum_(v : 'I_N) ((count_mem v rs - 2) + 2 * (v \in rs)) <=
    \sum_(v : 'I_N) (count_mem v rs + (nth r0 rs 0 == v)).
  apply: leq_sum => v _; case Hv: (v \in rs); last first.
    by rewrite muln0 addn0; apply: leq_trans (leq_subr _ _) (leq_addr _ _).
  have Hc : 0 < count_mem v rs by rewrite -has_pred1 has_count in Hv.
  case: (eqVneq (nth r0 rs 0) v) => [_ | Hne].
    rewrite /= muln1 addn1; move: Hc; set c := count_mem v rs => Hc; clearbody c.
    by move: Hc; rewrite -!minusE -!plusE => /leP Hc; apply/leP; lia.
  have Hi : 0 < index v rs < L.
    rewrite index_mem Hv andbT lt0n; apply/eqP => H0.
    by move: Hne; rewrite -H0 nth_index ?eqxx.
  have := pmst_fv_terminal N r0 rs (index v rs) HT HL2 Hi; rewrite nth_index //.
  rewrite /= muln1 addn0; move: Hc; set c := count_mem v rs => Hc H1; clearbody c.
  by move: Hc H1; rewrite -!minusE -!plusE => /leP Hc /eqP H1; apply/leP; lia.
rewrite !big_split in HS.
have HR : \sum_(v : 'I_N) (v \in rs) = pmsc_R N rs.
  rewrite /pmsc_R -sum1_card [RHS]big_mkcond; apply: eq_bigr => v _; rewrite inE.
  by case: (v \in rs).
rewrite big1_eq HR pmsc_count_sum pmsc_sum_eq1 /= in HS.
move: HS; set X := \sum_(i < N) (count_mem i rs - 2); set R := pmsc_R N rs; clearbody X R.
by rewrite -!multE -!minusE -!plusE => /leP HS; apply/leP; lia.
Qed.

Theorem pmsk_ix_le : pmso_fv N rs = L ->
  \sum_(s < L) pmsk_ix N d n (code s) <= 45 * pmsc_e N d rs ps.
Proof.
move=> HT.
have E1 : \sum_(s < L) pmsk_ix N d n (code s) + \sum_(s < L) pmsk_rf N d n (code s) +
    \sum_(s < L) pmsk_cf N d n (code s) =
    3 * \sum_(s < L) (~~ closer s) + \sum_(s < L) (closer s && (3 <= index (tw s) (ol s))).
  rewrite big_distrr -!big_split /=; apply: eq_bigr => s _; rewrite pmsk_code_ix //.
  by case: (closer s); rewrite /= ?muln0 ?muln1 ?add0n ?addn0.
rewrite pmsk_sum_rf pmsk_sum_cf in E1.
have Hsu : \sum_(s < L) (closer s && (3 <= index (tw s) (ol s))) <=
    \sum_(s < L) (3 <= count_mem (a s) rs).
  apply: leq_sum => s _; case Hcl: (closer s) => //=; case Hk: (3 <= _) => //=.
  by rewrite (pmsk_su s (ltn_ord s) Hcl Hk).
have H3 := pmsk_rows3 HT.
have Hpair := pmsk_pair.
have Hthree : \sum_(s < L) closer s + \sum_(s < L) opener s + \sum_(s < L) (tw s == s) = L.
  rewrite -!big_split /= (eq_bigr (fun _ => 1)); first by move=> s _; exact: pmsk_three.
  by rewrite big_const_ord iter_addn_0 mul1n.
have Hnc : \sum_(s < L) (~~ closer s) = \sum_(s < L) opener s + \sum_(s < L) (tw s == s).
  rewrite -big_split; apply: eq_bigr => s _ /=; have := pmsk_three s.
  case: (closer s) => /=; last by rewrite add0n => ->.
  by rewrite add1n => /eqP; rewrite eqSS addn_eq0 => /andP [/eqP -> /eqP ->].
have Hlo : \sum_(s < L) (tw s == s) <= 27 * pmsc_e N d rs ps.
  have := pmst_lonely_le N d r0 q0 rs ps HW HT; apply: leq_trans.
  rewrite -sum1_card [X in _ <= X]big_mkcond; apply: eq_leq; apply: eq_bigr => s _.
  by rewrite inE pmsk_tw_lonely; case: (_ == _).
have HR := pmst_terminal_R N r0 rs HT; have HV := pmso_valid_bound N d rs ps HW.
have HC := pmst_C_le N d rs ps HW.
rewrite /pmsc_e in Hlo *.
move: E1 Hsu H3 Hpair Hthree Hnc Hlo HR HV HC.
set S := \sum_(s < L) pmsk_ix N d n (code s).
set Snc := \sum_(s < L) ~~ closer s.
set Ssu := \sum_(s < L) closer s && (2 < index (tw s) (ol s)).
set X := \sum_(s < L) (2 < count_mem (a s) rs).
set Scl := \sum_(s < L) closer s.
set Sop := \sum_(s < L) opener s.
set Slo := \sum_(s < L) (tw s == s).
set R := pmsc_R N rs; set C := pmsc_C d ps; set LL := L.
clearbody S Snc Ssu X Scl Sop Slo R C LL.
rewrite -!multE -!minusE -!plusE.
move=> E1 /leP Hsu /leP H3 Hpair Hthree Hnc /leP Hlo /leP HR /leP HV /leP HC; apply/leP; lia.
Qed.

End Cost.
