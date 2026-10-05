(* Removing rows visited once in place (G16, checkpoint B4, item 2).
   A closed walk (rs, ps) of length L >= 3 is reduced at the first non-root
   position j whose row v is visited once (pmso_fv). With w and u the rows
   before and after v:
   - if w != u, the contraction deletes v and its outgoing label: the walk
     stays valid, e is unchanged (pmso_contract, pmso_e_contract), and the
     first such position of the result is j or later (pmso_fv_remc);
   - if w = u, the excursion deletes v, one copy of u and the two labels of
     the excursion: the walk stays valid, e drops by the number of colors of
     the removed label pair that remain (pmso_excursion, pmso_e_excursion),
     and the first such position of the result is j - 1 or later
     (pmso_fv_reme).
   The reduced walk, j, v, an orientation bit and, for an excursion, the
   removed label pair determine the original walk (pmso_rebuild_c,
   pmso_rebuild_e). The root row is never removed, so no step wraps around.
   For the sums S L k of B^(2e) over the valid walks of length L <= L0 whose
   first removable position is k or later, and the sums T L over the walks
   without a removable row, this gives the hypothesis of
   PaperMainSquarefreeWalkShapeRecursion (pmso_step):
     S L k <= T L + sum_(k <= j < L)
       (2 N S (L-1) (j-1) + 2 N (d + L0 B^2)^2 S (L-2) (j-1)),
   so S L 0 <= Lam L * 2^L for every Lam that dominates the recursion
   (pmso_bound). No probability premise. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import PaperMainSquarefreeWalkCount PaperMainSquarefreeWalkExcess
  PaperMainSquarefreeWalkShapeRecursion.

(* 1. Deleting and inserting list entries. *)
Section Lists.
Variable T : Type.
Implicit Types (s : seq T) (x : T).

Definition pmso_del (j : nat) s : seq T := take j s ++ drop j.+1 s.
Definition pmso_ins (j : nat) x s : seq T := take j s ++ x :: drop j s.

Lemma pmso_size_del j s : j < size s -> size (pmso_del j s) = (size s).-1.
Proof.
move=> Hj; rewrite /pmso_del size_cat size_take size_drop Hj.
by move: Hj; case: (size s) => // n Hn; rewrite subSS /= subnKC.
Qed.

Lemma pmso_size_ins j x s : size (pmso_ins j x s) = (size s).+1.
Proof.
rewrite /pmso_ins size_cat /= size_take size_drop addnS.
case: ltnP => H; first by rewrite subnKC // ltnW.
by rewrite (_ : size s - j = 0) ?addn0 //; apply/eqP; rewrite subn_eq0.
Qed.

Lemma pmso_del_ins j x s : j <= size s -> pmso_del j (pmso_ins j x s) = s.
Proof.
move=> Hj; rewrite /pmso_del /pmso_ins.
have Hs : size (take j s) = j by rewrite size_take; case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hj.
by rewrite take_size_cat // -cat1s catA drop_size_cat ?size_cat ?Hs ?addn1 // cat_take_drop.
Qed.

Lemma pmso_ins_del x0 j s : j < size s -> pmso_ins j (nth x0 s j) (pmso_del j s) = s.
Proof.
move=> Hj; rewrite /pmso_del /pmso_ins.
have Hs : size (take j s) = j by rewrite size_take Hj.
by rewrite take_size_cat // drop_size_cat // -drop_nth // cat_take_drop.
Qed.

Lemma pmso_rot_del x0 j s : j < size s -> rot j s = nth x0 s j :: rot j (pmso_del j s).
Proof.
move=> Hj; rewrite /rot /pmso_del (drop_nth x0 Hj).
have Hs : size (take j s) = j by rewrite size_take Hj.
by rewrite drop_size_cat // take_size_cat.
Qed.

Lemma pmso_take_del j i s : i <= j -> take i (pmso_del j s) = take i s.
Proof.
move=> Hij; rewrite /pmso_del.
case: (leqP j (size s)) => Hj.
  rewrite takel_cat ?take_takel //.
  by rewrite size_take; case: ifP => _; [exact: Hij | exact: leq_trans Hij Hj].
rewrite (take_oversize (ltnW Hj)).
by rewrite (drop_oversize (leq_trans (ltnW Hj) (leqnSn _))) cats0.
Qed.

End Lists.

Arguments pmso_del {T}.
Arguments pmso_ins {T}.
Arguments pmso_size_del {T}.
Arguments pmso_size_ins {T}.
Arguments pmso_del_ins {T}.
Arguments pmso_ins_del {T}.
Arguments pmso_rot_del {T}.
Arguments pmso_take_del {T}.

(* 2. The two head reductions of PaperMainSquarefreeWalkCount, refined. *)
Section Head.
Variables N d : nat.
Local Notation chi := (pmsc_chi d).

(* A row visited once between distinct rows carries one label pair. *)
Lemma pmso_contract_chi (v w u : 'I_N) (M : seq 'I_N) (p0 pl : 'I_d * 'I_d)
    (Q : seq ('I_d * 'I_d)) :
  size Q = (size M).+1 -> v \notin w :: rcons M u -> pmsc_distinct d (p0 :: rcons Q pl) ->
  pmsc_even N d (v :: w :: rcons M u) (p0 :: rcons Q pl) -> forall c, chi p0 c = chi pl c.
Proof.
move=> HQ Hv Hd He.
have Hvw : w != v by apply: contraNneq Hv => ->; rewrite mem_head.
have Hvu : u != v by apply: contraNneq Hv => ->; rewrite inE mem_rcons mem_head orbT.
have Hoff : forall e, e \in zip (w :: M) (rcons M u) -> (e.1 != v) && (e.2 != v).
  move=> e He'; apply/andP; split.
    apply: contraNneq Hv => <-.
    have := pmsc_mem_zip1 _ _ _ _ _ He'; rewrite inE => /orP [/eqP ->|H]; first by rewrite mem_head.
    by rewrite inE mem_rcons inE H !orbT.
  apply: contraNneq Hv => <-.
  have := pmsc_mem_zip2 _ _ _ _ _ He' => H.
  by rewrite inE H orbT.
move: (Hd) => /= /andP [Hp0 HdQ].
have Hpl : pl.1 != pl.2 by move: HdQ => /allP; apply; rewrite mem_rcons mem_head.
apply: pmsc_chi_eq => // c; have := He v c.
rewrite pmsc_deg_f (pmsc_steps_contract_old N d v w u M p0 pl Q HQ) big_cons pmsc_sum_rcons.
rewrite pmsc_rows_off //.
by rewrite /pmsc_f /= eqxx (negbTE Hvw) (negbTE Hvu) add0n addn0 !mul1n.
Qed.

(* Two distinct pairs with the same colors are equal up to orientation. *)
Definition pmso_orient (b : bool) (p : 'I_d * 'I_d) : 'I_d * 'I_d := if b then p else (p.2, p.1).

Lemma pmso_chi_orient (p q : 'I_d * 'I_d) : p.1 != p.2 ->
  (forall c, chi p c = chi q c) -> q = pmso_orient (q == p) p.
Proof.
move=> Hp H; case: eqP => [-> // | Hqp] /=.
have H1 := H p.1; have H2 := H p.2.
rewrite /pmsc_chi eqxx in H1; rewrite /pmsc_chi eqxx in H2.
clear H; move: Hp H1 H2 Hqp; case: p => a b; case: q => x y /= Hab.
rewrite eq_sym (negbTE Hab) /= => H1 H2 Hqp.
case: (eqVneq x a) H1 H2 Hqp => [-> | Hxa] H1 H2 Hqp.
  case: (eqVneq y b) H2 Hqp => [-> | Hyb] H2 Hqp; first by case: (Hqp erefl).
  by move: H2; rewrite (negbTE Hab).
case: (eqVneq y a) H1 H2 => [-> | Hya] H1 H2; last by move: H1.
case: (eqVneq x b) H2 => [-> // | Hxb] H2.
by move: H2; rewrite (negbTE Hab).
Qed.

(* The colors of a label list. *)
Definition pmso_cols (ps : seq ('I_d * 'I_d)) : {set 'I_d} :=
  [set c | has (fun p => (p.1 == c) || (p.2 == c)) ps].

Lemma pmso_card_cols ps : #|pmso_cols ps| = pmsc_C d ps.
Proof. by apply: eq_card => c; rewrite !inE. Qed.

(* The number of colors of p that already occur in ps. *)
Definition pmso_old (ps : seq ('I_d * 'I_d)) (p : 'I_d * 'I_d) : nat :=
  ((p.1 \in pmso_cols ps) + (p.2 \in pmso_cols ps))%N.

Lemma pmso_old_le2 ps p : (pmso_old ps p <= 2)%N.
Proof. by rewrite /pmso_old; case: (_ \in _); case: (_ \in _). Qed.

(* The exact color count of an excursion. *)
Lemma pmso_excursion_C (p0 p1 pl : 'I_d * 'I_d) (Q : seq ('I_d * 'I_d)) :
  p0.1 != p0.2 -> (forall c, chi p0 c = chi pl c) ->
  (pmsc_C d (p0 :: p1 :: rcons Q pl) + pmso_old (p1 :: Q) p0 = pmsc_C d (p1 :: Q) + 2)%N.
Proof.
move=> Hp0 Hchi.
have Hor : forall p c, ((p.1 == c) || (p.2 == c)) = (0 < chi p c)%N.
  by move=> p c; rewrite /pmsc_chi addn_gt0 !lt0b.
have E : pmso_cols (p0 :: p1 :: rcons Q pl) = p0.1 |: (p0.2 |: pmso_cols (p1 :: Q)).
  apply/setP => c; rewrite !inE /= has_rcons.
  have -> : ((pl.1 == c) || (pl.2 == c)) = ((p0.1 == c) || (p0.2 == c)) by rewrite !Hor Hchi.
  rewrite ![c == _]eq_sym.
  by case: (p0.1 == c); case: (p0.2 == c); case: (p1.1 == c); case: (p1.2 == c); case: has.
rewrite -!pmso_card_cols E !cardsU1 /pmso_old in_setU1 (negbTE Hp0) /=.
set C := #|pmso_cols (p1 :: Q)|.
by case: (p0.1 \in pmso_cols (p1 :: Q)); case: (p0.2 \in pmso_cols (p1 :: Q)); rewrite /= -!plusE; lia.
Qed.

End Head.

(* 3. Rotations of deleted lists. *)
Section Shapes.
Variable T : Type.
Implicit Types (s : seq T) (x : T).

Lemma pmso_rot_del_eq j s : j < size s -> rot j (pmso_del j s) = drop j.+1 s ++ take j s.
Proof.
move=> Hj; rewrite /rot /pmso_del.
have Hs : size (take j s) = j by rewrite size_take Hj.
by rewrite drop_size_cat // take_size_cat.
Qed.

Lemma pmso_take_last x0 j s : 0 < j -> j <= size s -> take j s = rcons (take j.-1 s) (nth x0 s j.-1).
Proof.
by move=> H0 Hj; rewrite -take_nth ?prednK.
Qed.

(* The deleted list, rotated, as seen from the deleted entry. *)
Lemma pmso_rot_shape x0 j s : 0 < j < size s ->
  rot j (pmso_del j s) = rcons (drop j.+1 s ++ take j.-1 s) (nth x0 s j.-1).
Proof.
case/andP => H0 Hj; rewrite pmso_rot_del_eq // (pmso_take_last x0 j s H0 (ltnW Hj)).
by rewrite rcons_cat.
Qed.

Lemma pmso_rot_head x0 j s : 2 < size s -> 0 < j < size s ->
  exists M, rot j (pmso_del j s) =
    nth x0 s (if j.+1 < size s then j.+1 else 0) :: rcons M (nth x0 s j.-1).
Proof.
move=> Hs Hjs; have /andP [H0 Hj] := Hjs; rewrite (pmso_rot_shape x0 j s Hjs).
case: ifP => Hj1.
  by exists (drop j.+2 s ++ take j.-1 s); rewrite (drop_nth x0 Hj1).
have Ej : j.+1 = size s by apply/eqP; rewrite eqn_leq Hj leqNgt Hj1.
rewrite drop_oversize ?Ej // cat0s.
clear Hjs; case: s Hs Hj Hj1 Ej => [|r rest] //= Hs Hj Hj1 Ej.
case: j H0 Hj Hj1 Ej => [|[|j]] //= H0 Hj Hj1 Ej.
  by move: Hs; rewrite -Ej.
by exists (take j rest).
Qed.

Lemma pmso_del_del j s : pmso_del j (pmso_del j s) = take j s ++ drop j.+2 s.
Proof.
rewrite /pmso_del; case: (leqP j (size s)) => Hj.
  have Hs : size (take j s) = j by rewrite size_take; case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hj.
  rewrite take_size_cat //.
  by rewrite drop_cat Hs ltnNge leqnSn /= subSnn drop_drop add1n.
have H1 : size s <= j.+1 by exact: leq_trans (ltnW Hj) (leqnSn _).
have H2 : size s <= j.+2 by exact: leq_trans H1 (leqnSn _).
rewrite !(take_oversize (ltnW Hj)) (drop_oversize H1) cats0.
by rewrite (take_oversize (ltnW Hj)) (drop_oversize H1) (drop_oversize H2).
Qed.

(* The excursion u -> v -> u, rotated to v. *)
Definition pmso_del2r j s : seq T :=
  if j.+1 < size s then pmso_del j (pmso_del j s) else pmso_del j.-1 (pmso_del j.-1 s).

Lemma pmso_rot_exc x0 j s : 2 < size s -> 0 < j < size s ->
  nth x0 s j.-1 = nth x0 s (if j.+1 < size s then j.+1 else 0) ->
  exists M, rot j s = nth x0 s j :: nth x0 s j.-1 :: rcons M (nth x0 s j.-1) /\
    rot j.-1 (pmso_del2r j s) = nth x0 s j.-1 :: M.
Proof.
move=> Hs /andP [H0 Hj] Hexc; rewrite /pmso_del2r.
case: ifP Hexc => Hj1 Hexc.
  exists (drop j.+2 s ++ take j.-1 s); split.
    rewrite /rot (drop_nth x0 Hj) (drop_nth x0 Hj1) -Hexc (pmso_take_last x0 j s H0 (ltnW Hj)).
    by rewrite /= rcons_cat.
  rewrite pmso_del_del (pmso_take_last x0 j s H0 (ltnW Hj)) cat_rcons.
  have Hs' : size (take j.-1 s) = j.-1 by rewrite size_take (leq_ltn_trans (leq_pred j) Hj).
  by rewrite -{1}Hs' rot_size_cat.
have Ej : j.+1 = size s by apply/eqP; rewrite eqn_leq Hj leqNgt Hj1.
case: s Hs Hj Hj1 Hexc Ej => [|x s1] //= Hs Hj Hj1 Hexc Ej.
case: j H0 Hj Hj1 Hexc Ej => [|[|j]] //= H0 Hj Hj1 Hexc Ej.
  by move: Hs; rewrite -Ej.
have Hs1 : size s1 = j.+2 by case: Ej.
exists (take j s1); split.
  rewrite /rot /= (drop_nth x0 (_ : j.+1 < size s1)) ?Hs1 // drop_oversize ?Hs1 //.
  by rewrite (pmso_take_last x0 j.+1 s1) ?Hs1 //= Hexc.
rewrite pmso_del_del /= drop_oversize ?Hs1 // cats0 Hexc.
have Hsz' : size (x :: take j s1) = j.+1 by rewrite /= size_takel // Hs1 -addn2 leq_addr.
by rewrite -{1}Hsz' rot_size.
Qed.

(* The labels of the excursion, rotated to v. *)
Lemma pmso_rot_exc_lab x0 j s : 2 < size s -> 0 < j < size s ->
  exists Q, rot j s = nth x0 s j :: nth x0 s (if j.+1 < size s then j.+1 else 0) ::
      rcons Q (nth x0 s j.-1) /\
    rot j.-1 (pmso_del j.-1 (pmso_del j.-1 s)) = nth x0 s (if j.+1 < size s then j.+1 else 0) :: Q.
Proof.
move=> Hs /andP [H0 Hj].
have Ej2 : j.-1.+2 = j.+1 by rewrite prednK.
case: ifP => Hj1.
  exists (drop j.+2 s ++ take j.-1 s); split.
    rewrite /rot (drop_nth x0 Hj) (drop_nth x0 Hj1) (pmso_take_last x0 j s H0 (ltnW Hj)).
    by rewrite /= rcons_cat.
  rewrite pmso_del_del Ej2.
  have Hs' : size (take j.-1 s) = j.-1 by rewrite size_take (leq_ltn_trans (leq_pred j) Hj).
  by rewrite -{1}Hs' rot_size_cat (drop_nth x0 Hj1).
have Ej : j.+1 = size s by apply/eqP; rewrite eqn_leq Hj leqNgt Hj1.
case: s Hs Hj Hj1 Ej Ej2 => [|x s1] //= Hs Hj Hj1 Ej Ej2.
case: j H0 Hj Hj1 Ej Ej2 => [|[|j]] //= H0 Hj Hj1 Ej Ej2.
  by move: Hs; rewrite -Ej.
have Hs1 : size s1 = j.+2 by case: Ej.
exists (take j s1); split.
  rewrite /rot /= (drop_nth x0 (_ : j.+1 < size s1)) ?Hs1 // drop_oversize ?Hs1 //.
  by rewrite (pmso_take_last x0 j.+1 s1) ?Hs1.
rewrite pmso_del_del /= drop_oversize ?Hs1 // cats0.
have Hsz' : size (x :: take j s1) = j.+1 by rewrite /= size_takel // Hs1 -addn2 leq_addr.
by rewrite -{1}Hsz' rot_size.
Qed.

End Shapes.

Arguments pmso_rot_del_eq {T}.
Arguments pmso_take_last {T}.
Arguments pmso_rot_shape {T}.
Arguments pmso_rot_head {T}.
Arguments pmso_del_del {T}.
Arguments pmso_del2r {T}.
Arguments pmso_rot_exc {T}.
Arguments pmso_rot_exc_lab {T}.

Lemma pmso_count_rot (T : eqType) n (s : seq T) x : count_mem x (rot n s) = count_mem x s.
Proof. have Hp : perm_eq (rot n s) s by rewrite perm_rot. by move/permP: Hp => ->. Qed.

Lemma pmso_cols_rot d n (ps : seq ('I_d * 'I_d)) : pmso_cols d (rot n ps) = pmso_cols d ps.
Proof. by apply/setP => c; rewrite !inE has_rot. Qed.

Lemma pmso_old_rot d n (ps : seq ('I_d * 'I_d)) p : pmso_old d (rot n ps) p = pmso_old d ps p.
Proof. by rewrite /pmso_old pmso_cols_rot. Qed.

Lemma pmso_old_orient d (ps : seq ('I_d * 'I_d)) b p : pmso_old d ps (pmso_orient d b p) = pmso_old d ps p.
Proof. by case: b; rewrite /pmso_old //= addnC. Qed.

(* 4. Walks. *)
Section Walks.
Variables N d : nat.
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).

Definition pmso_even rs ps : bool :=
  [forall r : 'I_N, [forall c : 'I_d, ~~ odd (pmsc_deg N d rs ps r c)]].

Lemma pmso_evenP rs ps : reflect (pmsc_even N d rs ps) (pmso_even rs ps).
Proof.
apply: (iffP forallP) => [H r c | H r]; first by have /forallP := H r; apply.
by apply/forallP => c; exact: H.
Qed.

Definition pmso_valid rs ps : bool :=
  [&& size ps == size rs, pmsc_loopfree N rs, pmsc_distinct d ps & pmso_even rs ps].

Lemma pmso_valid_rot n rs ps : pmso_valid (rot n rs) (rot n ps) = pmso_valid rs ps.
Proof.
rewrite /pmso_valid !size_rot pmsc_loopfree_rot pmsc_distinct_rot.
case: (eqVneq (size ps) (size rs)) => //= Hs.
by congr (_ && (_ && _)); apply/pmso_evenP/pmso_evenP => H;
  [apply/(pmsc_even_rot N d n rs ps Hs) | apply/(pmsc_even_rot N d n rs ps Hs)].
Qed.

Definition pmso_succ (j : nat) rs : nat := if j.+1 < size rs then j.+1 else 0.

(* The contraction of a row visited once between distinct rows. *)
Lemma pmso_contract r0 q0 rs ps j :
  pmso_valid rs ps -> 2 < size rs -> 0 < j < size rs ->
  count_mem (nth r0 rs j) rs = 1 -> nth r0 rs j.-1 != nth r0 rs (pmso_succ j rs) ->
  [/\ pmso_valid (pmso_del j rs) (pmso_del j ps),
      pmsc_R N rs = (pmsc_R N (pmso_del j rs)).+1,
      pmsc_C d ps = pmsc_C d (pmso_del j ps) &
      nth q0 ps j = pmso_orient d (nth q0 ps j == nth q0 ps j.-1) (nth q0 ps j.-1)].
Proof.
move=> HW H2 Hj Hv Hwu.
move: HW => /and4P [/eqP Hs Hl Hd /pmso_evenP He].
have /andP [H0 Hjs] := Hj.
have Hjp : 0 < j < size ps by rewrite Hs.
have [M HM] := pmso_rot_head r0 j rs H2 Hj.
rewrite -/(pmso_succ j rs) in HM.
set w := nth r0 rs (pmso_succ j rs) in HM Hwu.
set u := nth r0 rs j.-1 in HM Hwu.
set v := nth r0 rs j in Hv.
have Hrot : rot j rs = v :: w :: rcons M u by rewrite (pmso_rot_del r0 j rs Hjs) HM.
set Q := drop j.+1 ps ++ take j.-1 ps.
set p0 := nth q0 ps j; set pl := nth q0 ps j.-1.
have HrotP : rot j ps = p0 :: rcons Q pl.
  by rewrite (pmso_rot_del q0 j ps (proj2 (andP Hjp))) (pmso_rot_shape q0 j ps Hjp).
have HQ : size Q = (size M).+1.
  have := congr1 size Hrot; have := congr1 size HrotP.
  rewrite !size_rot /= !size_rcons Hs => -> [].
  by move=> ->.
have Hv' : v \notin w :: rcons M u.
  apply/count_memPn; move: Hv.
  rewrite -(pmso_count_rot _ j rs v) Hrot /= eqxx add1n.
  by case.
have Hl' : pmsc_loopfree N (v :: w :: rcons M u) by rewrite -Hrot pmsc_loopfree_rot.
have Hd' : pmsc_distinct d (p0 :: rcons Q pl) by rewrite -HrotP pmsc_distinct_rot.
have He' : pmsc_even N d (v :: w :: rcons M u) (p0 :: rcons Q pl).
  by rewrite -Hrot -HrotP; apply/(pmsc_even_rot N d j rs ps Hs).
have [Hl2 Hd2 He2 HR2 HC2] := pmsc_contract N d v w u M p0 pl Q HQ Hv' Hwu Hl' Hd' He'.
have Hchi := pmso_contract_chi N d v w u M p0 pl Q HQ Hv' Hd' He'.
have Hpl : pl.1 != pl.2.
  by move: Hd' => /= /andP [_ /allP]; apply; rewrite mem_rcons mem_head.
have HrotDP : rot j (pmso_del j ps) = rcons Q pl by rewrite (pmso_rot_shape q0 j ps Hjp).
split.
- rewrite -(pmso_valid_rot j) HM HrotDP /pmso_valid Hl2 Hd2 /= !size_rcons HQ.
  by rewrite eqxx /=; apply/pmso_evenP.
- by rewrite -(pmsc_R_rot N j rs) Hrot HR2 -HM pmsc_R_rot.
- by rewrite -(pmsc_C_rot d j ps) HrotP HC2 -HrotDP pmsc_C_rot.
- by apply: (pmso_chi_orient d) => // c; rewrite Hchi.
Qed.

(* The excursion u -> v -> u through a row visited once. *)
Lemma pmso_excursion r0 q0 rs ps j :
  pmso_valid rs ps -> 2 < size rs -> 0 < j < size rs ->
  count_mem (nth r0 rs j) rs = 1 -> nth r0 rs j.-1 = nth r0 rs (pmso_succ j rs) ->
  [/\ pmso_valid (pmso_del2r j rs) (pmso_del j.-1 (pmso_del j.-1 ps)),
      pmsc_R N rs = (pmsc_R N (pmso_del2r j rs)).+1,
      (pmsc_C d ps + pmso_old d (pmso_del j.-1 (pmso_del j.-1 ps)) (nth q0 ps j.-1) =
         pmsc_C d (pmso_del j.-1 (pmso_del j.-1 ps)) + 2)%N &
      nth q0 ps j = pmso_orient d (nth q0 ps j == nth q0 ps j.-1) (nth q0 ps j.-1)].
Proof.
move=> HW H2 Hj Hv Hexc.
move: HW => /and4P [/eqP Hs Hl Hd /pmso_evenP He].
have Hjp : 0 < j < size ps by rewrite Hs.
have H2p : 2 < size ps by rewrite Hs.
have [M [HrotM HremM]] := pmso_rot_exc r0 j rs H2 Hj Hexc.
have [Q [HrotQ HremQ]] := pmso_rot_exc_lab q0 j ps H2p Hjp.
set u := nth r0 rs j.-1 in HrotM HremM.
set v := nth r0 rs j in Hv HrotM.
set p0 := nth q0 ps j in HrotQ.
set p1 := nth q0 ps (if j.+1 < size ps then j.+1 else 0) in HrotQ HremQ.
set pl := nth q0 ps j.-1 in HrotQ.
have HQ : size Q = size M.
  have := congr1 size HrotM; have := congr1 size HrotQ.
  rewrite !size_rot /= !size_rcons Hs => -> [].
  by move=> ->.
have Hv' : v \notin u :: rcons M u.
  apply/count_memPn; move: Hv.
  rewrite -(pmso_count_rot _ j rs v) HrotM /= eqxx add1n.
  by case.
have Hl' : pmsc_loopfree N (v :: u :: rcons M u) by rewrite -HrotM pmsc_loopfree_rot.
have Hd' : pmsc_distinct d (p0 :: p1 :: rcons Q pl) by rewrite -HrotQ pmsc_distinct_rot.
have He' : pmsc_even N d (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl).
  by rewrite -HrotM -HrotQ; apply/(pmsc_even_rot N d j rs ps Hs).
have [Hl2 Hd2 He2 HR2 _] := pmsc_excursion N d v u M p0 p1 pl Q HQ Hv' Hl' Hd' He'.
have Hchi := pmsc_excursion_chi N d v u M p0 p1 pl Q HQ Hv' Hd' He'.
have Hp0 : p0.1 != p0.2 by move: Hd' => /= /and3P [].
have Hpl : pl.1 != pl.2.
  by move: Hd' => /= /and3P [_ _ /allP]; apply; rewrite mem_rcons mem_head.
have HC := pmso_excursion_C d p0 p1 pl Q Hp0 Hchi.
have Hor : p0 = pmso_orient d (p0 == pl) pl.
  by apply: (pmso_chi_orient d) => // c; rewrite Hchi.
split.
- rewrite -(pmso_valid_rot j.-1) HremM HremQ /pmso_valid Hl2 Hd2 /= HQ eqxx /=.
  by apply/pmso_evenP.
- by rewrite -(pmsc_R_rot N j rs) HrotM HR2 -HremM pmsc_R_rot.
- rewrite -(pmsc_C_rot d j ps) HrotQ.
  rewrite -(pmsc_C_rot d j.-1 (pmso_del j.-1 (pmso_del j.-1 ps))) HremQ.
  rewrite -(pmso_old_rot d j.-1) HremQ.
  by rewrite -(pmso_old_orient d (p1 :: Q) (p0 == pl) pl) -Hor.
- exact: Hor.
Qed.

End Walks.

(* 5. Counts after deletions. *)
Section Counts.
Variable T : eqType.
Implicit Types (s : seq T) (x : T).

Lemma pmso_nth_del x0 j i s : i < j -> nth x0 (pmso_del j s) i = nth x0 s i.
Proof.
move=> Hij; rewrite /pmso_del nth_cat size_take.
case: ifP => Hj.
  by rewrite nth_take.
case: (ltnP j (size s)) Hj => Hjs Hj; first by rewrite Hij in Hj.
have Hd : size s <= j.+1 by exact: leq_trans Hjs (leqnSn _).
by rewrite (drop_oversize Hd) nth_nil nth_default // leqNgt Hj.
Qed.

Lemma pmso_count_del x0 x j s : j < size s ->
  count_mem x s = (count_mem x (pmso_del j s) + (nth x0 s j == x))%N.
Proof.
move=> Hj; rewrite -{1}(cat_take_drop j s) (drop_nth x0 Hj) /pmso_del !count_cat /=.
by rewrite addnCA addnC eq_sym.
Qed.

Lemma pmso_count2 x0 x s i1 i2 : i1 < i2 -> i2 < size s ->
  nth x0 s i1 = x -> nth x0 s i2 = x -> 2 <= count_mem x s.
Proof.
move=> H12 H2s H1 H2.
rewrite -(cat_take_drop i2 s) count_cat (drop_nth x0 H2s) /= H2 eqxx.
have Hin : x \in take i2 s.
  by apply/(nthP x0); exists i1; [rewrite size_take H2s | rewrite nth_take].
rewrite -has_pred1 has_count in Hin.
by rewrite addnCA add1n ltnS addn_gt0 Hin.
Qed.

End Counts.

Arguments pmso_nth_del {T}.
Arguments pmso_count_del {T}.
Arguments pmso_count2 {T}.

Lemma pmso_nth_del_ge (T : Type) (x0 : T) j i s : j <= i ->
  nth x0 (pmso_del j s) i = nth x0 s i.+1.
Proof.
move=> Hji; rewrite /pmso_del nth_cat size_take.
case: (ltnP j (size s)) => Hjs.
  by rewrite ltnNge Hji /= nth_drop addSn subnKC.
case: ifP => Hi.
  by have := leq_trans Hjs Hji; rewrite leqNgt Hi.
have Hd : size s <= j.+1 by exact: leq_trans Hjs (leqnSn _).
rewrite (drop_oversize Hd) nth_nil nth_default //.
by apply: leq_trans (leqnSn _); rewrite leqNgt Hi.
Qed.

Arguments pmso_nth_del_ge {T}.

(* 6. The first removable position. *)
Section First.
Variables N d : nat.
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).

Definition pmso_once rs (v : 'I_N) : bool := count_mem v rs == 1.

(* The first non-root position whose row is visited once, for L >= 3;
   otherwise the length. *)
Definition pmso_fv rs : nat :=
  if 2 < size rs then (if rs is r :: rest then (find (pmso_once rs) rest).+1 else 0)
  else size rs.

Lemma pmso_fv_le rs : pmso_fv rs <= size rs.
Proof. by rewrite /pmso_fv; case: ifP => // _; case: rs => //= r rest; rewrite ltnS find_size. Qed.

Lemma pmso_fvP r0 rs j : pmso_fv rs = j -> j < size rs ->
  [/\ 2 < size rs, 0 < j, count_mem (nth r0 rs j) rs = 1 &
      forall i, 0 < i < j -> count_mem (nth r0 rs i) rs != 1].
Proof.
rewrite /pmso_fv; case: ifP => H2; last by move=> <-; rewrite ltnn.
case: rs H2 => [|r rest] //= H2 <- Hj.
have Hhas : has (pmso_once (r :: rest)) rest by rewrite has_find -ltnS.
split => //.
- by apply/eqP; have := nth_find r0 Hhas.
- move=> i /andP [Hi0 Hi]; case: i Hi0 Hi => [|i] // _ Hi /=.
  by have := before_find r0 Hi; rewrite /pmso_once => ->.
Qed.

Lemma pmso_fv_ge r0 rs k : k <= size rs ->
  (forall i, 0 < i < k -> count_mem (nth r0 rs i) rs != 1) -> k <= pmso_fv rs.
Proof.
rewrite /pmso_fv; case: ifP => // H2 Hk H.
case: rs H2 Hk H => [|r rest] //= H2 Hk H.
case: k Hk H => [|k] // Hk H; rewrite ltnS.
rewrite leqNgt; apply/negP => Hf.
have Hhas : has (pmso_once (r :: rest)) rest by rewrite has_find (leq_trans Hf).
have := nth_find r0 Hhas; rewrite /pmso_once => /eqP Hc.
have Hi : 0 < (find (pmso_once (r :: rest)) rest).+1 < k.+1 by rewrite /= ltnS Hf.
by move: (H _ Hi) Hc => /= /eqP H1 H3; apply: H1.
Qed.

(* A contraction keeps the earlier positions non-removable. *)
Lemma pmso_fv_remc (r0 : 'I_N) rs j : pmso_fv rs = j -> j < size rs -> j <= pmso_fv (pmso_del j rs).
Proof.
move=> Hf Hj; have [H2 H0 Hv Hfirst] := pmso_fvP r0 rs j Hf Hj.
apply: (pmso_fv_ge r0); first by rewrite pmso_size_del // -ltnS prednK // (leq_ltn_trans (leq0n _) Hj).
move=> i /andP [Hi0 Hi]; rewrite (pmso_nth_del r0 j i rs Hi).
have Hx : (nth r0 rs j == nth r0 rs i) = false.
  apply/negbTE/eqP => Hji.
  have := pmso_count2 r0 (nth r0 rs j) rs i j Hi Hj (esym Hji) erefl.
  by rewrite Hv.
have := pmso_count_del r0 (nth r0 rs i) j rs Hj; rewrite Hx addn0 => <-.
by apply: Hfirst; rewrite Hi0.
Qed.

(* An excursion keeps the positions before j - 1 non-removable. *)
Lemma pmso_fv_reme r0 rs j : pmso_fv rs = j -> j < size rs ->
  nth r0 rs j.-1 = nth r0 rs (if j.+1 < size rs then j.+1 else 0) ->
  j.-1 <= pmso_fv (pmso_del2r j rs).
Proof.
move=> Hf Hj Hexc; have [H2 H0 Hv Hfirst] := pmso_fvP r0 rs j Hf Hj.
set u := nth r0 rs j.-1 in Hexc.
set v := nth r0 rs j in Hv.
have Hj1 : j.-1 < j by rewrite prednK.
have Hjs : j.-1 < size rs by exact: ltn_trans Hj1 Hj.
have Hsz : size (pmso_del2r j rs) = (size rs).-2.
  rewrite /pmso_del2r; case: ifP => Hj2.
    rewrite (pmso_size_del j (pmso_del j rs)) (pmso_size_del j rs) //.
    by rewrite ltn_predRL.
  rewrite (pmso_size_del j.-1 (pmso_del j.-1 rs)) (pmso_size_del j.-1 rs) //.
  by rewrite ltn_predRL prednK.
apply: (pmso_fv_ge r0).
  by rewrite Hsz -!subn1; apply/leP; move/leP: Hj; rewrite -!minusE; lia.
move=> i /andP [Hi0 Hi].
have Hij : i < j by exact: ltn_trans Hi Hj1.
have Hnth : nth r0 (pmso_del2r j rs) i = nth r0 rs i.
  rewrite /pmso_del2r; case: ifP => _.
    by rewrite !(pmso_nth_del r0 j i).
  by rewrite !(pmso_nth_del r0 j.-1 i).
rewrite Hnth.
have Hxv : (v == nth r0 rs i) = false.
  apply/negbTE/eqP => Hji.
  have := pmso_count2 r0 v rs i j Hij Hj (esym Hji) erefl.
  by rewrite Hv.
have Hisz : i < size (pmso_del2r j rs).
  by rewrite Hsz -!subn1; apply/leP; move/leP: Hj; move/leP: Hi; rewrite -!minusE; lia.
case: (eqVneq (nth r0 rs i) u) => Hxu.
  (* the row u keeps two copies *)
  rewrite Hxu; apply/negP => /eqP Hc1.
  suff : 2 <= count_mem u (pmso_del2r j rs) by rewrite Hc1.
  move: Hisz; rewrite /pmso_del2r; case: ifP Hexc => Hj2 Hexc Hisz.
    apply: (pmso_count2 r0 u _ i j.-1 Hi).
    - move: Hsz; rewrite /pmso_del2r Hj2 => ->.
      by rewrite -!subn1; apply/leP; move/leP: Hj2; move/leP: H0; rewrite -!minusE; lia.
    - by rewrite !(pmso_nth_del r0 j i) // Hxu.
    - by rewrite !(pmso_nth_del r0 j j.-1).
  apply: (pmso_count2 r0 u _ 0 i Hi0) => //.
  - have Hj0 : 0 < j.-1 by exact: ltn_trans Hi0 Hi.
    by rewrite !(pmso_nth_del r0 j.-1 0) // Hexc.
  - by rewrite !(pmso_nth_del r0 j.-1 i) // Hxu.
(* any other row keeps its count *)
have Hcount : count_mem (nth r0 rs i) rs = count_mem (nth r0 rs i) (pmso_del2r j rs).
  rewrite /pmso_del2r; case: ifP Hexc => Hj2 Hexc.
    have Hjd : j < size (pmso_del j rs) by rewrite pmso_size_del // ltn_predRL.
    rewrite (pmso_count_del r0 (nth r0 rs i) j rs Hj).
    rewrite (pmso_count_del r0 (nth r0 rs i) j (pmso_del j rs) Hjd).
    rewrite (pmso_nth_del_ge r0 j j rs (leqnn j)) -Hexc -/v Hxv eq_sym (negbTE Hxu).
    by rewrite !addn0.
  have Hjd : j.-1 < size (pmso_del j.-1 rs) by rewrite pmso_size_del // ltn_predRL prednK.
  rewrite (pmso_count_del r0 (nth r0 rs i) j.-1 rs Hjs).
  rewrite (pmso_count_del r0 (nth r0 rs i) j.-1 (pmso_del j.-1 rs) Hjd).
  rewrite (pmso_nth_del_ge r0 j.-1 j.-1 rs (leqnn _)) prednK // -/v Hxv -/u eq_sym (negbTE Hxu).
  by rewrite !addn0.
by rewrite -Hcount; apply: Hfirst; rewrite Hi0 Hij.
Qed.

End First.

Lemma pmso_nth_ins (T : Type) (x0 : T) j x i s : i < j -> j <= size s ->
  nth x0 (pmso_ins j x s) i = nth x0 s i.
Proof.
move=> Hij Hj; rewrite /pmso_ins nth_cat size_take.
have Hs : (if j < size s then j else size s) = j by case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hj.
by rewrite Hs Hij nth_take.
Qed.

Lemma pmso_nth_ins_at (T : Type) (x0 : T) j x s : j <= size s -> nth x0 (pmso_ins j x s) j = x.
Proof.
move=> Hj; rewrite /pmso_ins nth_cat size_take.
have Hs : (if j < size s then j else size s) = j by case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hj.
by rewrite Hs ltnn subnn.
Qed.

Arguments pmso_nth_ins {T}.
Arguments pmso_nth_ins_at {T}.

(* 7. Rebuilding a walk from its reduction. *)
Section Rebuild.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).

Definition pmso_insc_labs j (b : bool) ps : seq ('I_d * 'I_d) :=
  pmso_ins j (pmso_orient d b (nth q0 ps j.-1)) ps.

Definition pmso_inse_rows j (v : 'I_N) rs : seq 'I_N :=
  if j <= size rs then pmso_ins j v (pmso_ins j (nth r0 rs j.-1) rs)
  else pmso_ins j.-1 (nth r0 rs 0) (pmso_ins j.-1 v rs).

Definition pmso_inse_labs j (q : 'I_d * 'I_d) (b : bool) ps : seq ('I_d * 'I_d) :=
  pmso_ins j.-1 q (pmso_ins j.-1 (pmso_orient d b q) ps).

Lemma pmso_size_inse_rows j v rs : size (pmso_inse_rows j v rs) = (size rs).+2.
Proof. by rewrite /pmso_inse_rows; case: ifP => _; rewrite !pmso_size_ins. Qed.

Lemma pmso_size_inse_labs j q b ps : size (pmso_inse_labs j q b ps) = (size ps).+2.
Proof. by rewrite /pmso_inse_labs !pmso_size_ins. Qed.

(* Removal followed by insertion. *)
Lemma pmso_rebuild_c rs ps j : pmso_valid N d rs ps -> pmso_fv N rs = j -> j < size rs ->
  nth r0 rs j.-1 != nth r0 rs (pmso_succ N j rs) ->
  rs = pmso_ins j (nth r0 rs j) (pmso_del j rs) /\
  ps = pmso_insc_labs j (nth q0 ps j == nth q0 ps j.-1) (pmso_del j ps).
Proof.
move=> HW Hf Hj Hk; have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
have [_ _ _ Hor] := pmso_contract N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
have Hs : size ps = size rs by move: HW => /and4P [/eqP].
split; first by rewrite pmso_ins_del.
have Hjp : j < size ps by rewrite Hs.
have Hj1 : j.-1 < j by rewrite prednK.
rewrite /pmso_insc_labs (pmso_nth_del q0 j j.-1 ps Hj1).
by rewrite -Hor pmso_ins_del.
Qed.

Lemma pmso_rebuild_e rs ps j : pmso_valid N d rs ps -> pmso_fv N rs = j -> j < size rs ->
  nth r0 rs j.-1 = nth r0 rs (pmso_succ N j rs) ->
  rs = pmso_inse_rows j (nth r0 rs j) (pmso_del2r j rs) /\
  ps = pmso_inse_labs j (nth q0 ps j.-1) (nth q0 ps j == nth q0 ps j.-1)
         (pmso_del j.-1 (pmso_del j.-1 ps)).
Proof.
move=> HW Hf Hj Hk; have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
have [_ _ _ Hor] := pmso_excursion N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
have Hs : size ps = size rs by move: HW => /and4P [/eqP].
have Hj1 : j.-1 < j by rewrite prednK.
have Hjs : j.-1 < size rs by exact: ltn_trans Hj1 Hj.
split.
  rewrite /pmso_inse_rows /pmso_del2r /pmso_succ in Hk *.
  case: ifP Hk => Hj2 Hk.
    have Hsz : j <= size (pmso_del j (pmso_del j rs)).
      by rewrite !pmso_size_del ?pmso_size_del // -!subn1; apply/leP; move/leP: Hj2; rewrite -!minusE; lia.
    rewrite Hsz !(pmso_nth_del r0 j j.-1) // Hk -(pmso_nth_del_ge r0 j j rs (leqnn _)).
    have Hjd : j < size (pmso_del j rs) by rewrite pmso_size_del // ltn_predRL.
    by rewrite (pmso_ins_del r0 j (pmso_del j rs) Hjd) pmso_ins_del.
  have Hsz : (j <= size (pmso_del j.-1 (pmso_del j.-1 rs))) = false.
    rewrite (pmso_size_del j.-1 (pmso_del j.-1 rs)) ?(pmso_size_del j.-1 rs) //; last first.
      apply/negbTE; rewrite -ltnNge -!subn1; apply/leP; move/leP: Hj; move/negbT: Hj2.
      rewrite -leqNgt; move=> /leP H1 H3; move/leP: H2 => H4; rewrite -!minusE; lia.
    by rewrite ltn_predRL prednK.
  rewrite Hsz.
  have Hj0 : 0 < j.-1.
    rewrite -ltnS prednK //; apply/leP; move/leP: H2; move/leP: Hj; move/negbT: Hj2.
    rewrite -leqNgt => /leP; lia.
  rewrite !(pmso_nth_del r0 j.-1 0) // -Hk.
  have Ev : nth r0 rs j = nth r0 (pmso_del j.-1 rs) j.-1.
    by rewrite (pmso_nth_del_ge r0 j.-1 j.-1 rs (leqnn _)) prednK.
  have Hjd : j.-1 < size (pmso_del j.-1 rs) by rewrite pmso_size_del // ltn_predRL prednK.
  by rewrite Ev (pmso_ins_del r0 j.-1 (pmso_del j.-1 rs) Hjd) pmso_ins_del.
have Hjp : j.-1 < size ps by rewrite Hs.
have Ep : nth q0 ps j = nth q0 (pmso_del j.-1 ps) j.-1.
  by rewrite (pmso_nth_del_ge q0 j.-1 j.-1 ps (leqnn _)) prednK.
have Hjd : j.-1 < size (pmso_del j.-1 ps) by rewrite pmso_size_del // ltn_predRL prednK // Hs.
by rewrite /pmso_inse_labs -Hor Ep (pmso_ins_del q0 j.-1 (pmso_del j.-1 ps) Hjd) pmso_ins_del.
Qed.

End Rebuild.

(* 8. The deficiency under the two reductions. *)
Section Deficiency.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).

Lemma pmso_valid_bound rs ps : pmso_valid N d rs ps ->
  (2 * pmsc_R N rs + pmsc_C d ps <= 2 * size rs + 2)%N.
Proof.
move=> /and4P [/eqP Hs Hl Hd /pmso_evenP He].
exact: pmsc_rows_colors_le N d rs ps Hs Hl Hd He.
Qed.

Lemma pmso_e_contract rs ps j : pmso_valid N d rs ps -> pmso_fv N rs = j -> j < size rs ->
  nth r0 rs j.-1 != nth r0 rs (pmso_succ N j rs) ->
  pmsc_e N d rs ps = pmsc_e N d (pmso_del j rs) (pmso_del j ps).
Proof.
move=> HW Hf Hj Hk; have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
have [HW' HR HC _] := pmso_contract N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
have B1 := pmso_valid_bound rs ps HW; have B2 := pmso_valid_bound _ _ HW'.
rewrite /pmsc_e pmso_size_del // HR HC in B1 *; rewrite pmso_size_del // in B2.
move: B1 B2 H2; rewrite -!subn1 -!plusE -!multE -!minusE => /leP B1 /leP B2 /leP H2'.
by apply/eqP; rewrite -(eqn_add2r 0) ?addn0; apply/eqP; lia.
Qed.

Lemma pmso_e_excursion rs ps j : pmso_valid N d rs ps -> pmso_fv N rs = j -> j < size rs ->
  nth r0 rs j.-1 = nth r0 rs (pmso_succ N j rs) ->
  pmsc_e N d rs ps = (pmsc_e N d (pmso_del2r j rs) (pmso_del j.-1 (pmso_del j.-1 ps)) +
    pmso_old d (pmso_del j.-1 (pmso_del j.-1 ps)) (nth q0 ps j.-1))%N.
Proof.
move=> HW Hf Hj Hk; have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
have [HW' HR HC _] := pmso_excursion N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
have B1 := pmso_valid_bound rs ps HW; have B2 := pmso_valid_bound _ _ HW'.
have Hold := pmso_old_le2 d (pmso_del j.-1 (pmso_del j.-1 ps)) (nth q0 ps j.-1).
have Hsz : size (pmso_del2r j rs) = (size rs).-2.
  rewrite /pmso_del2r; case: ifP => Hj2.
    rewrite (pmso_size_del j (pmso_del j rs)) (pmso_size_del j rs) //.
    by rewrite ltn_predRL.
  have Hjs : j.-1 < size rs by rewrite (leq_ltn_trans (leq_pred j)).
  rewrite (pmso_size_del j.-1 (pmso_del j.-1 rs)) (pmso_size_del j.-1 rs) //.
  by rewrite ltn_predRL prednK.
rewrite HR in B1; rewrite Hsz in B2; rewrite /pmsc_e Hsz HR.
move: B1 B2 H2 HC Hold; set C := pmsc_C d ps; set C2 := pmsc_C d _; set o := pmso_old d _ _.
rewrite -!subn1 -!plusE -!multE -!minusE => /leP B1 /leP B2 /leP H2' HC /leP Hold.
lia.
Qed.

End Deficiency.

(* 9. Covering a finite sum by the images of a map. *)
Lemma pmso_cover (I J : finType) (P : pred I) (Q : pred J) (g : J -> I) (f : I -> nat) :
  (forall x, P x -> exists2 y, Q y & g y = x) ->
  (\sum_(x | P x) f x <= \sum_(y | Q y) P (g y) * f (g y))%N.
Proof.
move=> H.
have E : (\sum_(y | Q y) P (g y) * f (g y) =
    \sum_(y | Q y) (if P (g y) then f (g y) else 0))%N.
  by apply: eq_bigr => y _; case: (P (g y)); rewrite ?mul1n ?mul0n.
rewrite E -big_mkcondr /= (partition_big g P) /=.
  by move=> y /andP [].
apply: leq_sum => x Px.
have [y Qy Hy] := H x Px.
rewrite (bigD1 y) /=; first by rewrite Qy Hy Px eqxx.
by rewrite Hy leq_addr.
Qed.

(* 10. Tuples. *)
Lemma pmso_tins_size {T : Type} {n} j (x : T) (t : n.-tuple T) : size (pmso_ins j x t) == n.+1.
Proof. by rewrite pmso_size_ins size_tuple. Qed.

Definition pmso_tins {T : Type} {n} j (x : T) (t : n.-tuple T) : n.+1.-tuple T :=
  Tuple (pmso_tins_size j x t).

Lemma pmso_tdel_size {T : Type} {n} j (t : n.+1.-tuple T) : j < n.+1 -> size (pmso_del j t) == n.
Proof. by move=> Hj; rewrite pmso_size_del ?size_tuple. Qed.

Lemma pmso_sum_pair (A B : finType) (P : pred A) (F : A -> nat) :
  (\sum_(y : A * B | P y.1) F y.1 = #|B| * \sum_(a | P a) F a)%N.
Proof.
rewrite (eq_bigl (fun y : A * B => P y.1 && xpredT y.2)); first last.
  rewrite -(pair_big P xpredT (fun a _ => F a)) /= big_distrr /=.
  by apply: eq_bigr => a _; rewrite big_const iter_addn_0 mulnC.
by move=> y /=; rewrite andbT.
Qed.

(* 11. One step of the recursion, for contractions. *)
Section StepC.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d) (B : nat).

Definition pmso_w (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)) : nat :=
  (pmso_valid N d rs ps * B ^ (2 * pmsc_e N d rs ps))%N.

Lemma pmso_w_valid rs ps : (0 < pmso_w rs ps)%N -> pmso_valid N d rs ps.
Proof. by rewrite /pmso_w; case: (pmso_valid N d rs ps). Qed.

Definition pmso_kc (rs : seq 'I_N) (j : nat) : bool := nth r0 rs j.-1 != nth r0 rs (pmso_succ N j rs).

Lemma pmso_step_c L (j : nat) : j < L.+1 ->
  (\sum_(W : L.+1.-tuple 'I_N * L.+1.-tuple ('I_d * 'I_d))
     ((pmso_fv N W.1 == j) && pmso_kc W.1 j) * pmso_w W.1 W.2 <=
   2 * N * \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
     (j.-1 <= pmso_fv N W.1) * pmso_w W.1 W.2)%N.
Proof.
move=> HjL.
set I := (L.+1.-tuple 'I_N * L.+1.-tuple ('I_d * 'I_d))%type.
set J := ((L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N * bool)%type.
pose P (W : I) := [&& pmso_fv N W.1 == j, pmso_kc W.1 j & pmso_valid N d W.1 W.2].
pose Q (y : J) := (j.-1 <= pmso_fv N y.1.1.1).
pose g (y : J) : I := (pmso_tins j y.1.2 y.1.1.1,
  pmso_tins j (pmso_orient d y.2 (nth q0 y.1.1.2 j.-1)) y.1.1.2).
have -> : (\sum_(W : I) ((pmso_fv N W.1 == j) && pmso_kc W.1 j) * pmso_w W.1 W.2 =
    \sum_(W | P W) pmso_w W.1 W.2)%N.
  rewrite [RHS]big_mkcond /=; apply: eq_bigr => W _; rewrite /P /pmso_w.
  by case: (_ == j); case: pmso_kc; case: pmso_valid; rewrite ?mul0n ?mul1n ?muln0.
apply: (leq_trans (pmso_cover _ _ P Q g (fun W => pmso_w W.1 W.2) _)).
  move=> [rs ps] /and3P [/eqP Hf Hk HW].
  have Hj : j < size rs by rewrite size_tuple.
  have [Hr Hp] := pmso_rebuild_c N d r0 q0 rs ps j HW Hf Hj Hk.
  exists ((Tuple (pmso_tdel_size j rs HjL), Tuple (pmso_tdel_size j ps HjL)), nth r0 rs j,
    nth q0 ps j == nth q0 ps j.-1).
    by rewrite /Q /=; apply: leq_trans (pmso_fv_remc N r0 rs j Hf Hj); exact: leq_pred.
  rewrite /g /=; congr (_, _); apply: val_inj => /=; [exact: (esym Hr) | exact: (esym Hp)].
apply: (@leq_trans (\sum_(y | Q y) pmso_w y.1.1.1 y.1.1.2)).
  apply: leq_sum => [[[[rs' ps'] v] b]] Qy.
  case HP: (P _); rewrite ?mul0n // mul1n.
  move: HP; rewrite /P /g /= => /and3P [/eqP Hf Hk HW].
  set rs := pmso_ins j v rs' in Hf Hk HW *.
  set ps := pmso_ins j (pmso_orient d b (nth q0 ps' j.-1)) ps' in HW *.
  have Hj : j < size rs by rewrite pmso_size_ins size_tuple.
  have Ers : pmso_del j rs = rs' by rewrite /rs pmso_del_ins // size_tuple -ltnS.
  have Eps : pmso_del j ps = ps' by rewrite /ps pmso_del_ins // size_tuple -ltnS.
  have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
  have [HW' _ _ _] := pmso_contract N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
  have He := pmso_e_contract N d r0 q0 rs ps j HW Hf Hj Hk.
  by rewrite /pmso_w HW He Ers Eps; rewrite Ers Eps in HW'; rewrite HW'.
rewrite (pmso_sum_pair _ _ (fun x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N =>
    j.-1 <= pmso_fv N x.1.1) (fun x => pmso_w x.1.1 x.1.2)).
rewrite (pmso_sum_pair _ _ (fun W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d) =>
    j.-1 <= pmso_fv N W.1) (fun W => pmso_w W.1 W.2)).
rewrite card_bool card_ord mulnA.
rewrite leq_mul2l; apply/orP; right; rewrite big_mkcond /=; apply: leq_sum => W _.
by case: ifP => _; rewrite ?mul1n ?mul0n.
Qed.

End StepC.

(* 12. One step of the recursion, for excursions. *)
Lemma pmso_size_del2r (T : Type) j (s : seq T) : 0 < j < size s ->
  size (pmso_del2r j s) = (size s).-2.
Proof.
case/andP => H0 Hj; rewrite /pmso_del2r; case: ifP => Hj2.
  rewrite (pmso_size_del j (pmso_del j s)) (pmso_size_del j s) //.
  by rewrite ltn_predRL.
have Hjs : j.-1 < size s by rewrite (leq_ltn_trans (leq_pred j)).
rewrite (pmso_size_del j.-1 (pmso_del j.-1 s)) (pmso_size_del j.-1 s) //.
by rewrite ltn_predRL prednK.
Qed.

Section StepE.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d) (B : nat).
Local Notation pmso_w := (pmso_w N d B).

Definition pmso_ke (rs : seq 'I_N) (j : nat) : bool := nth r0 rs j.-1 == nth r0 rs (pmso_succ N j rs).

Lemma pmso_tinse_rows_size n j (v : 'I_N) (t : n.-tuple 'I_N) :
  size (pmso_inse_rows N r0 j v t) == n.+2.
Proof. by rewrite pmso_size_inse_rows size_tuple. Qed.

Lemma pmso_tinse_labs_size n j (q : 'I_d * 'I_d) b (t : n.-tuple ('I_d * 'I_d)) :
  size (pmso_inse_labs d j q b t) == n.+2.
Proof. by rewrite pmso_size_inse_labs size_tuple. Qed.

Lemma pmso_del2r_inse j v (s : seq 'I_N) : j <= (size s).+1 ->
  pmso_del2r j (pmso_inse_rows N r0 j v s) = s.
Proof.
move=> Hj; rewrite /pmso_del2r pmso_size_inse_rows /pmso_inse_rows ltnS ltnS.
case: ifP => Hjs.
  rewrite Hjs pmso_del_ins; first by rewrite pmso_size_ins (leq_trans Hjs (leqnSn _)).
  by rewrite pmso_del_ins.
have Hj1 : j.-1 <= size s by rewrite -subn1 leq_subLR add1n.
rewrite Hjs pmso_del_ins; first by rewrite pmso_size_ins (leq_trans Hj1 (leqnSn _)).
by rewrite pmso_del_ins.
Qed.

Lemma pmso_del2l_inse j q b (s : seq ('I_d * 'I_d)) : j.-1 <= size s ->
  pmso_del j.-1 (pmso_del j.-1 (pmso_inse_labs d j q b s)) = s /\
  nth q0 (pmso_inse_labs d j q b s) j.-1 = q.
Proof.
move=> Hj; rewrite /pmso_inse_labs; split.
  rewrite pmso_del_ins; first by rewrite pmso_size_ins (leq_trans Hj (leqnSn _)).
  by rewrite pmso_del_ins.
by rewrite pmso_nth_ins_at // pmso_size_ins (leq_trans Hj (leqnSn _)).
Qed.

Lemma pmso_sum_old (ps : seq ('I_d * 'I_d)) :
  (\sum_(q : 'I_d * 'I_d) B ^ (2 * pmso_old d ps q) <= (d + #|pmso_cols d ps| * B ^ 2) ^ 2)%N.
Proof.
set C := pmso_cols d ps.
pose F (a : 'I_d) := (B ^ (2 * (a \in C)))%N.
have E1 : (\sum_(q : 'I_d * 'I_d) B ^ (2 * pmso_old d ps q) =
    \sum_(q : 'I_d * 'I_d) F q.1 * F q.2)%N.
  by apply: eq_bigr => q _; rewrite /pmso_old /F mulnDr expnD.
rewrite E1 -(pair_bigA _ (fun a b => F a * F b)) /= -big_distrlr /= expnS expn1.
have Hs : (\sum_(a : 'I_d) F a <= d + #|C| * B ^ 2)%N.
  rewrite (bigID (mem C)) /= addnC.
  apply: leq_add.
    rewrite -[X in (_ <= X)%N]card_ord -sum1_card.
    rewrite big_mkcond /=; apply: leq_sum => a _.
    by rewrite /F; case: (a \in C).
  rewrite (eq_bigr (fun _ => B ^ 2)%N); first by move=> a Ha; rewrite /F Ha muln1.
  by rewrite sum_nat_const mulnC.
by apply: leq_mul.
Qed.

Lemma pmso_sum_pair2 (A C : finType) (P : pred A) (G : A -> C -> nat) :
  (\sum_(y : A * C | P y.1) G y.1 y.2 = \sum_(a | P a) \sum_(c : C) G a c)%N.
Proof.
rewrite (eq_bigl (fun y : A * C => P y.1 && xpredT y.2)); first last.
  by rewrite -(pair_big P xpredT G).
by move=> y /=; rewrite andbT.
Qed.

Lemma pmso_step_e L (j : nat) : j < L.+2 ->
  (\sum_(W : L.+2.-tuple 'I_N * L.+2.-tuple ('I_d * 'I_d))
     ((pmso_fv N W.1 == j) && pmso_ke W.1 j) * pmso_w W.1 W.2 <=
   2 * N * (d + L * B ^ 2) ^ 2 * \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
     (j.-1 <= pmso_fv N W.1) * pmso_w W.1 W.2)%N.
Proof.
move=> HjL.
set I := (L.+2.-tuple 'I_N * L.+2.-tuple ('I_d * 'I_d))%type.
set J := (((L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N) * ('I_d * 'I_d) * bool)%type.
pose P (W : I) := [&& pmso_fv N W.1 == j, pmso_ke W.1 j & pmso_valid N d W.1 W.2].
pose Q (y : J) := (j.-1 <= pmso_fv N y.1.1.1.1).
pose g (y : J) : I := (Tuple (pmso_tinse_rows_size _ j y.1.1.2 y.1.1.1.1),
  Tuple (pmso_tinse_labs_size _ j y.1.2 y.2 y.1.1.1.2)).
have -> : (\sum_(W : I) ((pmso_fv N W.1 == j) && pmso_ke W.1 j) * pmso_w W.1 W.2 =
    \sum_(W | P W) pmso_w W.1 W.2)%N.
  rewrite [RHS]big_mkcond /=; apply: eq_bigr => W _; rewrite /P.
  case: (_ == j); case: pmso_ke; rewrite ?mul0n ?mul1n //.
  by rewrite /pmso_w; case: pmso_valid; rewrite ?mul0n.
apply: (leq_trans (pmso_cover _ _ P Q g (fun W => pmso_w W.1 W.2) _)).
  move=> [rs ps] /and3P [/eqP Hf /eqP Hk HW].
  have Hj : j < size rs by rewrite size_tuple.
  have [H2 H0 _ _] := pmso_fvP N r0 rs j Hf Hj.
  have [Hr Hp] := pmso_rebuild_e N d r0 q0 rs ps j HW Hf Hj Hk.
  have Hsz1 : size (pmso_del2r j rs) == L.
    by rewrite pmso_size_del2r ?H0 ?Hj // size_tuple.
  have Hj1 : j.-1 < L.+2 by rewrite (leq_ltn_trans (leq_pred j)).
  have Hsz2 : size (pmso_del j.-1 (pmso_del j.-1 ps)) == L.
    rewrite (pmso_size_del j.-1 (pmso_del j.-1 ps)) ?(pmso_size_del j.-1 ps) ?size_tuple //.
    by rewrite ltn_predRL prednK.
  exists ((((Tuple Hsz1, Tuple Hsz2), nth r0 rs j), nth q0 ps j.-1), nth q0 ps j == nth q0 ps j.-1).
    by rewrite /Q /=; exact: (pmso_fv_reme N r0 rs j Hf Hj Hk).
  rewrite /g /=; congr (_, _); apply: val_inj => /=; [exact: (esym Hr) | exact: (esym Hp)].
apply: (@leq_trans (\sum_(y | Q y)
    pmso_w y.1.1.1.1 y.1.1.1.2 * B ^ (2 * pmso_old d y.1.1.1.2 y.1.2))).
  apply: leq_sum => [[[[[rs'' ps''] v] q] b]] Qy.
  case HP: (P _); rewrite ?mul0n // mul1n.
  move: HP; rewrite /P /g /= => /and3P [/eqP Hf /eqP Hk HW].
  set rs := pmso_inse_rows N r0 j v rs'' in Hf Hk HW *.
  set ps := pmso_inse_labs d j q b ps'' in HW *.
  have Hj : j < size rs by rewrite pmso_size_inse_rows size_tuple.
  have Ers : pmso_del2r j rs = rs'' by rewrite /rs pmso_del2r_inse // size_tuple -ltnS.
  have Hj1 : j.-1 <= size ps'' by rewrite size_tuple -subn1 leq_subLR add1n -ltnS.
  have [Eps Eq] := pmso_del2l_inse j q b ps'' Hj1.
  have [H2 H0 Hv _] := pmso_fvP N r0 rs j Hf Hj.
  have [HW' _ _ _] := pmso_excursion N d r0 q0 rs ps j HW H2 (introT andP (conj H0 Hj)) Hv Hk.
  have He := pmso_e_excursion N d r0 q0 rs ps j HW Hf Hj Hk.
  rewrite /ps Eps Eq Ers in He; rewrite /ps Eps Ers in HW'.
  rewrite /pmso_w HW HW' /= !mul1n.
  by rewrite /ps He mulnDr expnD.
set K := ((d + L * B ^ 2) ^ 2)%N.
rewrite (pmso_sum_pair _ _ (fun z : ((L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N) * ('I_d * 'I_d) =>
    j.-1 <= pmso_fv N z.1.1.1) (fun z => pmso_w z.1.1.1 z.1.1.2 * B ^ (2 * pmso_old d z.1.1.2 z.2))%N).
rewrite (pmso_sum_pair2 _ _ (fun x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N =>
    j.-1 <= pmso_fv N x.1.1) (fun x q => pmso_w x.1.1 x.1.2 * B ^ (2 * pmso_old d x.1.2 q))%N).
have Hin : forall x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N,
    (\sum_(c : 'I_d * 'I_d) pmso_w x.1.1 x.1.2 * B ^ (2 * pmso_old d x.1.2 c) <=
     pmso_w x.1.1 x.1.2 * K)%N.
  move=> x; rewrite -big_distrr /= leq_mul2l.
  case: eqP => [// | /eqP Hw].
  have Hw' : (0 < pmso_w x.1.1 x.1.2)%N by rewrite lt0n.
  rewrite orFb; apply: (leq_trans (pmso_sum_old x.1.2)).
  have HV := pmso_w_valid N d B x.1.1 x.1.2 Hw'.
  move: HV => /and4P [/eqP Hs Hl Hd /pmso_evenP He].
  have HC := pmsc_colors_le N d x.1.1 x.1.2 Hs Hl Hd He.
  rewrite /K leq_exp2r // leq_add2l leq_mul2r; apply/orP; right.
  by rewrite pmso_card_cols (leq_trans HC) // size_tuple.
have H1 : forall F1 F2 : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N -> nat,
    (forall x, F1 x <= F2 x) ->
    (\sum_(x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N | j.-1 <= pmso_fv N x.1.1) F1 x <=
     \sum_(x : (L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) * 'I_N | j.-1 <= pmso_fv N x.1.1) F2 x)%N.
  by move=> F1 F2 H; apply: leq_sum => x _; exact: H.
rewrite card_bool -!mulnA leq_mul2l /=.
apply: leq_trans (H1 _ _ Hin) _.
rewrite (pmso_sum_pair _ _ (fun W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d) =>
    j.-1 <= pmso_fv N W.1) (fun W => pmso_w W.1 W.2 * K)%N) card_ord leq_mul2l.
apply/orP; right; rewrite mulnA mulnn -/K -big_distrl /= mulnC leq_mul2l; apply/orP; right.
rewrite big_mkcond /=; apply: leq_sum => W _.
by case: ifP => _; rewrite ?mul1n ?mul0n.
Qed.

End StepE.

(* 13. The recursion hypothesis of PaperMainSquarefreeWalkShapeRecursion. *)
Lemma pmso_split_ge (x k L : nat) : x <= L -> k <= L ->
  ((k <= x) = (x == L) + \sum_(k <= j < L) (x == j) :> nat)%N.
Proof.
move=> HxL HkL.
have Hsum : forall k', k' <= L ->
    (\sum_(k' <= j < L) (x == j) = (k' <= x) && (x < L) :> nat)%N.
  move=> k' Hk'; have [m Hm] := ubnP (L - k'); elim: m k' Hk' Hm => // m IH k' Hk' Hm.
  case: (ltngtP k' L) Hk' => [Hk'L _ | // | -> _]; last by rewrite big_geq // ltnNge andbN.
  rewrite big_ltn // IH //; last first.
    case: (ltngtP k' x) => [Hkx | Hxk | <-] //.
    by rewrite Hk'L.
  by move: Hm; rewrite subnS ltnS; apply: leq_trans; rewrite ltn_predL subn_gt0.
rewrite Hsum //.
case: (ltngtP x L) HxL => [Hx | // | ->] _.
  by rewrite andbT.
by rewrite andbF HkL addn0.
Qed.

Section Sums.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d) (B L0 : nat).
Local Notation pmso_w := (pmso_w N d B).

Definition pmso_S (L k : nat) : nat :=
  if L <= L0 then \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
    (k <= pmso_fv N W.1) * pmso_w W.1 W.2 else 0.

Definition pmso_T (L : nat) : nat :=
  if L <= L0 then \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
    (pmso_fv N W.1 == L) * pmso_w W.1 W.2 else 0.

Theorem pmso_step L k : k <= L ->
  (pmso_S L k <= pmso_T L + \sum_(k <= j < L)
    (2 * N * pmso_S L.-1 j.-1 + 2 * N * (d + L0 * B ^ 2) ^ 2 * pmso_S L.-2 j.-1))%N.
Proof.
move=> HkL; rewrite /pmso_S /pmso_T.
case: (leqP L L0) => HL; last by [].
have HL1 : L.-1 <= L0 by exact: leq_trans (leq_pred L) HL.
have HL2 : L.-2 <= L0 by exact: leq_trans (leq_pred _) HL1.
rewrite HL1 HL2.
set E := fun j : nat => (\sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
  (pmso_fv N W.1 == j) * pmso_w W.1 W.2)%N.
have Hdec : (\sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d))
      (k <= pmso_fv N W.1) * pmso_w W.1 W.2 =
    \sum_(W : L.-tuple 'I_N * L.-tuple ('I_d * 'I_d)) (pmso_fv N W.1 == L) * pmso_w W.1 W.2 +
    \sum_(k <= j < L) E j)%N.
  rewrite /E exchange_big /= -big_split /=; apply: eq_bigr => W _.
  have Hfv : pmso_fv N W.1 <= L by have := pmso_fv_le N W.1; rewrite size_tuple.
  by rewrite (pmso_split_ge _ _ _ Hfv HkL) mulnDl big_distrl.
rewrite Hdec leq_add2l big_nat [X in (_ <= X)%N]big_nat; apply: leq_sum => j /andP [Hkj HjL].
rewrite /E; clear Hdec E.
case: L HkL HL HL1 HL2 HjL => [|[|[|L']]] HkL HL HL1 HL2 HjL //.
- rewrite big1 // => W _; rewrite /pmso_fv size_tuple /=.
  by move: HjL; rewrite ltnS leqn0 => /eqP ->.
- rewrite big1 // => W _; rewrite /pmso_fv size_tuple /=.
  by case: j HjL Hkj => [|[|]].
have Hs : (\sum_(W : L'.+3.-tuple 'I_N * L'.+3.-tuple ('I_d * 'I_d))
      (pmso_fv N W.1 == j) * pmso_w W.1 W.2 =
    \sum_(W : L'.+3.-tuple 'I_N * L'.+3.-tuple ('I_d * 'I_d))
      ((pmso_fv N W.1 == j) && pmso_kc N r0 W.1 j) * pmso_w W.1 W.2 +
    \sum_(W : L'.+3.-tuple 'I_N * L'.+3.-tuple ('I_d * 'I_d))
      ((pmso_fv N W.1 == j) && pmso_ke N r0 W.1 j) * pmso_w W.1 W.2)%N.
  rewrite -big_split /=; apply: eq_bigr => W _.
  rewrite /pmso_kc /pmso_ke -mulnDl; congr (_ * _).
  by case: (_ == j); case: (_ == _).
rewrite Hs; apply: leq_add.
  exact: (pmso_step_c N d r0 q0 B L'.+2 j HjL).
apply: leq_trans (pmso_step_e N d r0 q0 B L'.+1 j HjL) _.
rewrite leq_mul2r; apply/orP; right; rewrite leq_mul2l; apply/orP; right.
by rewrite leq_exp2r // leq_add2l leq_mul2r; apply/orP; right; apply: leq_trans HL2.
Qed.

End Sums.

(* 14. Phase 1 of the shape count: the walk sums in terms of the sums over
   walks without a removable row. *)
Corollary pmso_bound (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d) (B L0 : nat) (Lam : nat -> nat) :
  pmso_T N d B L0 0 <= Lam 0 ->
  (forall L, 0 < L -> pmso_T N d B L0 L + 2 * (2 * N) * Lam L.-1 +
     2 * N * (d + L0 * B ^ 2) ^ 2 * Lam L.-2 <= Lam L) ->
  forall L, pmso_S N d B L0 L 0 <= Lam L * 2 ^ L.
Proof.
move=> H0 HL L.
have := pmsr_bound (pmso_S N d B L0) (pmso_T N d B L0) Lam (2 * N)
  (2 * N * (d + L0 * B ^ 2) ^ 2) (pmso_step N d r0 q0 B L0) H0 HL L 0 (leq0n _).
by rewrite subn0.
Qed.
