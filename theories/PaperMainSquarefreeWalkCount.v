(* Rows and colors of even square-free walks (G16, checkpoint B2).
   A closed walk of length K is a list rs of K rows (step s goes from
   rs_s to rs_(s+1 mod K)) and a list ps of K label pairs p_s = (a_s, b_s)
   with a_s != b_s. It is loop-free when consecutive rows differ, and even
   when for every row r and color c the degree
     sum_s ([rs_s = r] + [rs_(s+1) = r]) ([a_s = c] + [b_s = c])
   is even. By PaperMainSquarefreeWalkWeight these are the walks with a
   nonzero moment. With R distinct rows and C distinct colors:
   - C <= K (pmsc_colors_le): the steps whose labels contain a color form
     an even set of at least two steps, and each step has two colors;
   - 2 R + C <= 2 K + 2 (pmsc_rows_colors_le), the degree-two case of
     Delta >= 0 in Kogan-Nandy-Huang (Definition 3.7). The proof is an
     induction on K: a row visited once is contracted (its two steps carry
     the same label pair), or its excursion u -> v -> u is removed; if every
     row is visited at least twice, then 2 R <= K.
   No probability premise. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect_compat.

Section Walks.
Variables N d : nat.
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).

Definition pmsc_steps rs ps : seq ('I_N * 'I_N * ('I_d * 'I_d)) :=
  zip (zip rs (rot 1 rs)) ps.

Definition pmsc_chi (p : 'I_d * 'I_d) (c : 'I_d) : nat := ((p.1 == c) + (p.2 == c))%N.

Definition pmsc_deg rs ps (r : 'I_N) (c : 'I_d) : nat :=
  \sum_(e <- pmsc_steps rs ps) ((e.1.1 == r) + (e.1.2 == r)) * pmsc_chi e.2 c.

Definition pmsc_even rs ps : Prop := forall r c, ~~ odd (pmsc_deg rs ps r c).

Definition pmsc_loopfree rs : bool := all (fun e => e.1 != e.2) (zip rs (rot 1 rs)).

Definition pmsc_distinct ps : bool := all (fun p => p.1 != p.2) ps.

Definition pmsc_R rs : nat := #|[pred r : 'I_N | r \in rs]|.

Definition pmsc_C ps : nat := #|[pred c : 'I_d | has (fun p => (p.1 == c) || (p.2 == c)) ps]|.

(* 1. Rotations. *)
Lemma pmsc_zip_nil (S T : Type) (s : seq S) : zip s ([::] : seq T) = [::].
Proof. by case: s. Qed.

Lemma pmsc_drop_zip (S T : Type) n (s : seq S) (t : seq T) :
  drop n (zip s t) = zip (drop n s) (drop n t).
Proof.
elim: n s t => [|n IH] [|x s] [|y t] //=; rewrite ?drop0 ?pmsc_zip_nil //.
  by case: (drop n t).
by case: (drop n s).
Qed.

Lemma pmsc_take_zip (S T : Type) n (s : seq S) (t : seq T) :
  take n (zip s t) = zip (take n s) (take n t).
Proof.
elim: n s t => [|n IH] [|x s] [|y t] //=; rewrite ?take0 ?pmsc_zip_nil ?IH //.
Qed.

Lemma pmsc_zip_rot (S T : Type) n (s : seq S) (t : seq T) : size s = size t ->
  zip (rot n s) (rot n t) = rot n (zip s t).
Proof.
move=> Hs; rewrite /rot.
have Hd : size (drop n s) = size (drop n t) by rewrite !size_drop Hs.
by rewrite (zip_cat _ _ Hd) -pmsc_drop_zip -pmsc_take_zip.
Qed.

Lemma pmsc_steps_rot n rs ps : size ps = size rs ->
  pmsc_steps (rot n rs) (rot n ps) = rot n (pmsc_steps rs ps).
Proof.
move=> Hs; rewrite /pmsc_steps rot_rot pmsc_zip_rot ?size_rot //.
by rewrite pmsc_zip_rot // size_zip size_rot minnn.
Qed.

Lemma pmsc_deg_rot n rs ps r c : size ps = size rs ->
  pmsc_deg (rot n rs) (rot n ps) r c = pmsc_deg rs ps r c.
Proof.
by move=> Hs; rewrite /pmsc_deg pmsc_steps_rot //; apply: perm_big; rewrite perm_rot.
Qed.

Lemma pmsc_even_rot n rs ps : size ps = size rs ->
  pmsc_even (rot n rs) (rot n ps) <-> pmsc_even rs ps.
Proof.
by move=> Hs; split => H r c; [rewrite -(pmsc_deg_rot n) | rewrite pmsc_deg_rot].
Qed.

Lemma pmsc_loopfree_rot n rs : pmsc_loopfree (rot n rs) = pmsc_loopfree rs.
Proof.
rewrite /pmsc_loopfree rot_rot pmsc_zip_rot ?size_rot //.
by apply: eq_all_r => e; rewrite mem_rot.
Qed.

Lemma pmsc_distinct_rot n ps : pmsc_distinct (rot n ps) = pmsc_distinct ps.
Proof. by apply: eq_all_r => p; rewrite mem_rot. Qed.

Lemma pmsc_R_rot n rs : pmsc_R (rot n rs) = pmsc_R rs.
Proof. by apply: eq_card => r; rewrite !inE mem_rot. Qed.

Lemma pmsc_C_rot n ps : pmsc_C (rot n ps) = pmsc_C ps.
Proof. by apply: eq_card => c; rewrite !inE has_rot. Qed.

(* 2. Colors: each color class is an even set of at least two steps. *)
Lemma pmsc_chi_le1 p c : p.1 != p.2 -> (pmsc_chi p c <= 1)%N.
Proof.
rewrite /pmsc_chi => Hp; case: (eqVneq p.1 c) => [<-|_] //=.
  by rewrite eq_sym (negbTE Hp).
by case: (p.2 == c).
Qed.

Lemma pmsc_sum_eq1 (T : finType) (a : T) : (\sum_(c : T) (a == c) = 1)%N.
Proof.
rewrite (bigD1 a) //= eqxx big1 ?addn0 // => c Hc.
by rewrite eq_sym (negbTE Hc).
Qed.

Lemma pmsc_chi_sum p : (\sum_(c : 'I_d) pmsc_chi p c = 2)%N.
Proof. by rewrite /pmsc_chi big_split /= !pmsc_sum_eq1. Qed.

(* The labels of the steps are the labels of the walk. *)
Lemma pmsc_steps_labels rs ps : size ps = size rs ->
  [seq e.2 | e <- pmsc_steps rs ps] = ps.
Proof.
by move=> Hs; rewrite /pmsc_steps -/(unzip2 _) unzip2_zip // size_zip size_rot minnn Hs.
Qed.

Lemma pmsc_mem_zip1 (S T : eqType) (s : seq S) (t : seq T) x : x \in zip s t -> x.1 \in s.
Proof.
elim: s t => [|a s IH] [|b t] //=.
rewrite !inE => /orP [/eqP -> | Hx]; first by rewrite eqxx.
by rewrite (IH t Hx) orbT.
Qed.

Lemma pmsc_mem_zip2 (S T : eqType) (s : seq S) (t : seq T) x : x \in zip s t -> x.2 \in t.
Proof.
elim: s t => [|a s IH] [|b t] //=.
rewrite !inE => /orP [/eqP -> | Hx]; first by rewrite eqxx.
by rewrite (IH t Hx) orbT.
Qed.

Lemma pmsc_steps_loopfree rs ps e : pmsc_loopfree rs -> e \in pmsc_steps rs ps -> e.1.1 != e.1.2.
Proof.
move=> /allP Hl He; apply: Hl.
exact: pmsc_mem_zip1 He.
Qed.

Definition pmsc_n ps (c : 'I_d) : nat := \sum_(p <- ps) pmsc_chi p c.

Lemma pmsc_ends_le1 (u w r : 'I_N) : u != w -> ((u == r) + (w == r) <= 1)%N.
Proof.
case: (eqVneq u r) => [<-|_] Huw; last by case: (w == r).
by rewrite eq_sym (negbTE Huw).
Qed.

Lemma pmsc_n_steps rs ps c : size ps = size rs ->
  (\sum_(e <- pmsc_steps rs ps) pmsc_chi e.2 c = pmsc_n ps c)%N.
Proof. by move=> Hs; rewrite /pmsc_n -{2}(pmsc_steps_labels _ _ Hs) big_map. Qed.

Lemma pmsc_used_n ps c :
  has (fun p => (p.1 == c) || (p.2 == c)) ps = (0 < pmsc_n ps c)%N.
Proof.
rewrite /pmsc_n; elim: ps => [|p ps IH]; first by rewrite big_nil.
rewrite big_cons /= IH /pmsc_chi addn_gt0.
by case: (p.1 == c); case: (p.2 == c).
Qed.

Lemma pmsc_sum_ge (T : eqType) (r : seq T) (F : T -> nat) x : x \in r ->
  (F x <= \sum_(y <- r) F y)%N.
Proof. by move=> Hx; rewrite (big_rem x Hx) /= leq_addr. Qed.

(* A used color labels at least two steps. *)
Lemma pmsc_n_ge2 rs ps c : size ps = size rs -> pmsc_loopfree rs -> pmsc_distinct ps ->
  pmsc_even rs ps -> (0 < pmsc_n ps c)%N -> (2 <= pmsc_n ps c)%N.
Proof.
move=> Hs Hl /allP Hd He Hn.
rewrite ltnNge; apply/negP => Hn1.
have Hn1' : pmsc_n ps c = 1%N by apply/eqP; rewrite eqn_leq Hn1 Hn.
have : has (fun e => 0 < pmsc_chi e.2 c)%N (pmsc_steps rs ps).
  apply/negPn/negP; rewrite -all_predC => /allP H0.
  move: Hn; rewrite -(pmsc_n_steps _ _ c Hs) big_seq big1 // => e /H0 /=.
  by rewrite lt0n negbK => /eqP.
case/hasP => e0 He0 Hchi.
have Hloop := pmsc_steps_loopfree _ _ _ Hl He0.
have Hp0 : e0.2.1 != e0.2.2.
  by apply: Hd; rewrite -(pmsc_steps_labels _ _ Hs); exact: map_f.
have Hchi1 : pmsc_chi e0.2 c = 1%N.
  by apply/eqP; rewrite eqn_leq pmsc_chi_le1.
have Hlow : (1 <= pmsc_deg rs ps e0.1.1 c)%N.
  have := pmsc_sum_ge _ _ (fun e => ((e.1.1 == e0.1.1) + (e.1.2 == e0.1.1)) * pmsc_chi e.2 c)%N _ He0.
  by rewrite eqxx /= Hchi1 muln1 /pmsc_deg; apply: leq_trans.
have Hup : (pmsc_deg rs ps e0.1.1 c <= 1)%N.
  rewrite -Hn1' -(pmsc_n_steps _ _ c Hs) /pmsc_deg big_seq [X in (_ <= X)%N]big_seq.
  apply: leq_sum => e He'.
  rewrite -[X in (_ <= X)%N]mul1n leq_mul2r pmsc_ends_le1 ?orbT //.
  exact: pmsc_steps_loopfree _ _ _ Hl He'.
have Hdeg : pmsc_deg rs ps e0.1.1 c = 1%N by apply/eqP; rewrite eqn_leq Hup Hlow.
by move: (He e0.1.1 c); rewrite Hdeg.
Qed.

Theorem pmsc_colors_le rs ps : size ps = size rs -> pmsc_loopfree rs -> pmsc_distinct ps ->
  pmsc_even rs ps -> (pmsc_C ps <= size rs)%N.
Proof.
move=> Hs Hl Hd He.
rewrite -leq_double -!mul2n.
have Htot : (\sum_(c : 'I_d) pmsc_n ps c = 2 * size rs)%N.
  rewrite /pmsc_n exchange_big /= (eq_bigr (fun _ => 2%N)); first by move=> p _; exact: pmsc_chi_sum.
  by rewrite -Hs; elim: ps {Hs Hd He} => [|p ps IH]; rewrite ?big_nil ?big_cons ?IH //= mulnS.
rewrite -Htot /pmsc_C -sum1_card big_mkcond /= big_distrr /=.
apply: leq_sum => c _; rewrite inE pmsc_used_n.
case Hc: (0 < pmsc_n ps c)%N; last by rewrite muln0.
rewrite muln1; exact: (pmsc_n_ge2 _ _ _ Hs Hl Hd He Hc).
Qed.

(* 3. Every row visited twice. *)
Lemma pmsc_count_sum rs : (\sum_(r : 'I_N) count_mem r rs = size rs)%N.
Proof.
elim: rs => [|x rs IH] /=; first by rewrite big1.
by rewrite big_split /= IH pmsc_sum_eq1 add1n.
Qed.

Lemma pmsc_terminal rs : (forall r, r \in rs -> 1 < count_mem r rs)%N ->
  (2 * pmsc_R rs <= size rs)%N.
Proof.
move=> H; rewrite -pmsc_count_sum /pmsc_R -sum1_card big_mkcond /= big_distrr /=.
apply: leq_sum => r _; rewrite inE; case Hr: (r \in rs); last by rewrite muln0.
by rewrite muln1; exact: H.
Qed.

Lemma pmsc_R_le rs : (pmsc_R rs <= size rs)%N.
Proof.
rewrite -pmsc_count_sum /pmsc_R -sum1_card big_mkcond /=.
apply: leq_sum => r _; rewrite inE; case Hr: (r \in rs) => //.
by rewrite -has_pred1 has_count in Hr.
Qed.

Lemma pmsc_R_cons (v : 'I_N) rs : v \notin rs -> pmsc_R (v :: rs) = (pmsc_R rs).+1.
Proof.
move=> Hv; rewrite /pmsc_R.
have -> : #|[pred r : 'I_N | r \in v :: rs]| = #|[predU1 v & [pred r : 'I_N | r \in rs]]|.
  by apply: eq_card => r; rewrite !inE.
by rewrite cardU1 inE Hv.
Qed.

(* 4. The two reductions. *)
Definition pmsc_f (r : 'I_N) (c : 'I_d) (e : 'I_N * 'I_N * ('I_d * 'I_d)) : nat :=
  ((e.1.1 == r) + (e.1.2 == r)) * pmsc_chi e.2 c.

Lemma pmsc_deg_f rs ps r c : pmsc_deg rs ps r c = \sum_(e <- pmsc_steps rs ps) pmsc_f r c e.
Proof. by []. Qed.

Lemma pmsc_sum_rcons (T : Type) (s : seq T) x (F : T -> nat) :
  (\sum_(y <- rcons s x) F y = \sum_(y <- s) F y + F x)%N.
Proof. by rewrite -cats1 big_cat big_seq1. Qed.

Lemma pmsc_chi_eq p q : p.1 != p.2 -> q.1 != q.2 ->
  (forall c, ~~ odd (pmsc_chi p c + pmsc_chi q c)) -> forall c, pmsc_chi p c = pmsc_chi q c.
Proof.
move=> Hp Hq H c; have := H c.
have := pmsc_chi_le1 p c Hp; have := pmsc_chi_le1 q c Hq.
by case: (pmsc_chi p c) => [|[|]] //; case: (pmsc_chi q c) => [|[|]].
Qed.

Lemma pmsc_colors_chi ps c :
  has (fun p => (p.1 == c) || (p.2 == c)) ps = has (fun p => 0 < pmsc_chi p c)%N ps.
Proof.
by apply: eq_has => p; rewrite /pmsc_chi addn_gt0 !lt0b.
Qed.

Lemma pmsc_rows_off (v : 'I_N) (rows : seq ('I_N * 'I_N)) (Q : seq ('I_d * 'I_d)) c :
  (forall e, e \in rows -> (e.1 != v) && (e.2 != v)) ->
  (\sum_(e <- zip rows Q) pmsc_f v c e = 0)%N.
Proof.
move=> H; rewrite big_seq big1 // => e He.
have /H /andP [H1 H2] := pmsc_mem_zip1 _ _ _ _ _ He.
by rewrite /pmsc_f (negbTE H1) (negbTE H2).
Qed.

Section Contract.
Variables (v w u : 'I_N) (M : seq 'I_N) (p0 pl : 'I_d * 'I_d) (Q : seq ('I_d * 'I_d)).
Variable HQ : size Q = (size M).+1.

Local Notation Z := (zip (w :: M) (rcons M u)).

Lemma pmsc_steps_contract_old :
  pmsc_steps (v :: w :: rcons M u) (p0 :: rcons Q pl) =
  ((v, w), p0) :: rcons (zip Z Q) ((u, v), pl).
Proof.
rewrite /pmsc_steps rot1_cons /= -rcons_cons zip_rcons ?size_rcons //.
by rewrite zip_rcons // size_zip /= size_rcons minnn.
Qed.

Lemma pmsc_steps_contract_new :
  pmsc_steps (w :: rcons M u) (rcons Q pl) = rcons (zip Z Q) ((u, w), pl).
Proof.
rewrite /pmsc_steps rot1_cons -rcons_cons zip_rcons ?size_rcons //.
by rewrite zip_rcons // size_zip /= size_rcons minnn.
Qed.

Lemma pmsc_rowpairs_contract_old :
  zip (v :: w :: rcons M u) (rot 1 (v :: w :: rcons M u)) = (v, w) :: rcons Z (u, v).
Proof. by rewrite rot1_cons /= -rcons_cons zip_rcons ?size_rcons. Qed.

Lemma pmsc_rowpairs_contract_new :
  zip (w :: rcons M u) (rot 1 (w :: rcons M u)) = rcons Z (u, w).
Proof. by rewrite rot1_cons -rcons_cons zip_rcons ?size_rcons. Qed.

Lemma pmsc_contract :
  v \notin w :: rcons M u -> u != w ->
  pmsc_loopfree (v :: w :: rcons M u) -> pmsc_distinct (p0 :: rcons Q pl) ->
  pmsc_even (v :: w :: rcons M u) (p0 :: rcons Q pl) ->
  [/\ pmsc_loopfree (w :: rcons M u), pmsc_distinct (rcons Q pl),
      pmsc_even (w :: rcons M u) (rcons Q pl),
      pmsc_R (v :: w :: rcons M u) = (pmsc_R (w :: rcons M u)).+1 &
      pmsc_C (p0 :: rcons Q pl) = pmsc_C (rcons Q pl)].
Proof.
move=> Hv Huw Hl Hd He.
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
have Hchi : forall c, pmsc_chi p0 c = pmsc_chi pl c.
  apply: pmsc_chi_eq => // c; have := He v c.
  rewrite pmsc_deg_f pmsc_steps_contract_old big_cons pmsc_sum_rcons pmsc_rows_off //.
  by rewrite /pmsc_f /= eqxx (negbTE Hvw) (negbTE Hvu) add0n addn0 !mul1n.
split.
- move: Hl; rewrite /pmsc_loopfree pmsc_rowpairs_contract_old pmsc_rowpairs_contract_new /=.
  by rewrite !all_rcons /= Huw => /and3P [_ _ ->].
- exact: HdQ.
- move=> r c; have := He r c.
  rewrite !pmsc_deg_f pmsc_steps_contract_old pmsc_steps_contract_new big_cons !pmsc_sum_rcons.
  rewrite /pmsc_f /= Hchi.
  set S := \sum_(e <- zip Z Q) _.
  set k := pmsc_chi pl c.
  have E : (((v == r) + (w == r)) * k + (S + ((u == r) + (v == r)) * k) =
      S + ((u == r) + (w == r)) * k + ((v == r) * k).*2)%N.
    rewrite -addnn !mulnDl -!plusE -!multE; lia.
  by rewrite E oddD odd_double addbF.
- exact: pmsc_R_cons.
- rewrite /pmsc_C; apply: eq_card => c; rewrite !inE.
  rewrite !pmsc_colors_chi /= Hchi.
  case Hc: (0 < pmsc_chi pl c)%N => //=; symmetry; apply/hasP; exists pl => //.
  by rewrite mem_rcons mem_head.
Qed.

End Contract.

Lemma pmsc_card_or (A B : pred 'I_d) : (#|[pred c | A c || B c]| <= #|A| + #|B|)%N.
Proof.
rewrite -!sum1_card.
rewrite [X in (X <= _)%N]big_mkcond [X in (_ <= X + _)%N]big_mkcond.
rewrite [X in (_ <= _ + X)%N]big_mkcond -big_split /=.
apply: leq_sum => c _; rewrite !inE !unfold_in.
by case: (A c); case: (B c).
Qed.

Lemma pmsc_card_pair (p : 'I_d * 'I_d) :
  (#|[pred c : 'I_d | (p.1 == c) || (p.2 == c)]| <= 2)%N.
Proof.
rewrite -(pmsc_chi_sum p) -sum1_card big_mkcond /=.
apply: leq_sum => c _; rewrite inE /pmsc_chi.
by case: (p.1 == c); case: (p.2 == c).
Qed.

Section Excursion.
Variables (v u : 'I_N) (M : seq 'I_N) (p0 p1 pl : 'I_d * 'I_d) (Q : seq ('I_d * 'I_d)).
Variable HQ : size Q = size M.

Local Notation Z := (zip (u :: M) (rcons M u)).

Lemma pmsc_rowpairs_excursion_old :
  zip (v :: u :: rcons M u) (rot 1 (v :: u :: rcons M u)) = (v, u) :: rcons Z (u, v).
Proof. by rewrite rot1_cons /= -rcons_cons zip_rcons ?size_rcons. Qed.

Lemma pmsc_steps_excursion_old :
  pmsc_steps (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) =
  ((v, u), p0) :: rcons (zip Z (p1 :: Q)) ((u, v), pl).
Proof.
rewrite /pmsc_steps pmsc_rowpairs_excursion_old.
have E : [:: p0, p1 & rcons Q pl] = p0 :: rcons (p1 :: Q) pl by [].
have Zc : forall (A B : Type) (x : A) (y : B) s t, zip (x :: s) (y :: t) = (x, y) :: zip s t.
  by [].
rewrite E Zc zip_rcons //.
by rewrite size_zip size_rcons /= HQ minnn.
Qed.

Lemma pmsc_steps_excursion_new : pmsc_steps (u :: M) (p1 :: Q) = zip Z (p1 :: Q).
Proof. by rewrite /pmsc_steps rot1_cons. Qed.

Lemma pmsc_excursion :
  v \notin u :: rcons M u ->
  pmsc_loopfree (v :: u :: rcons M u) -> pmsc_distinct (p0 :: p1 :: rcons Q pl) ->
  pmsc_even (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) ->
  [/\ pmsc_loopfree (u :: M), pmsc_distinct (p1 :: Q), pmsc_even (u :: M) (p1 :: Q),
      pmsc_R (v :: u :: rcons M u) = (pmsc_R (u :: M)).+1 &
      (pmsc_C (p0 :: p1 :: rcons Q pl) <= pmsc_C (p1 :: Q) + 2)%N].
Proof.
move=> Hv Hl Hd He.
have Hvu : u != v by apply: contraNneq Hv => ->; rewrite mem_head.
have Hoff : forall e, e \in Z -> (e.1 != v) && (e.2 != v).
  move=> e He'; apply/andP; split.
    apply: contraNneq Hv => <-.
    have := pmsc_mem_zip1 _ _ _ _ _ He'; rewrite inE => /orP [/eqP ->|H]; first by rewrite mem_head.
    by rewrite inE mem_rcons inE H !orbT.
  apply: contraNneq Hv => <-.
  have := pmsc_mem_zip2 _ _ _ _ _ He' => H.
  by rewrite inE H orbT.
move: (Hd) => /= /and3P [Hp0 Hp1 HdQ].
have Hpl : pl.1 != pl.2 by move: HdQ => /allP; apply; rewrite mem_rcons mem_head.
have Hchi : forall c, pmsc_chi p0 c = pmsc_chi pl c.
  apply: pmsc_chi_eq => // c; have := He v c.
  rewrite pmsc_deg_f pmsc_steps_excursion_old big_cons pmsc_sum_rcons pmsc_rows_off //.
  by rewrite /pmsc_f /= eqxx (negbTE Hvu) add0n addn0 !mul1n.
split.
- move: Hl; rewrite /pmsc_loopfree pmsc_rowpairs_excursion_old /= all_rcons rot1_cons.
  by case/and3P.
- by rewrite /pmsc_distinct /= Hp1; move: HdQ; rewrite /pmsc_distinct all_rcons => /andP [_ ->].
- move=> r c; have := He r c.
  rewrite !pmsc_deg_f pmsc_steps_excursion_old pmsc_steps_excursion_new big_cons pmsc_sum_rcons.
  rewrite /pmsc_f /= Hchi.
  set S := \sum_(e <- zip Z (p1 :: Q)) _.
  set k := pmsc_chi pl c.
  have E : (((v == r) + (u == r)) * k + (S + ((u == r) + (v == r)) * k) =
      S + ((v == r) * k + (u == r) * k).*2)%N.
    rewrite -addnn !mulnDl -!plusE -!multE; lia.
  by rewrite E oddD odd_double addbF.
- rewrite pmsc_R_cons //; congr _.+1; apply: eq_card => r.
  by rewrite !inE mem_rcons inE orbA orbb.
- have Hor : forall p c, ((p.1 == c) || (p.2 == c)) = (0 < pmsc_chi p c)%N.
    by move=> p c; rewrite /pmsc_chi addn_gt0 !lt0b.
  apply: (@leq_trans #|[pred c : 'I_d | has (fun p => (p.1 == c) || (p.2 == c)) (p1 :: Q) ||
      ((p0.1 == c) || (p0.2 == c))]|).
    apply: subset_leq_card; apply/subsetP => c; rewrite !inE /= has_rcons.
    have Hplc : ((pl.1 == c) || (pl.2 == c)) = ((p0.1 == c) || (p0.2 == c)).
      by rewrite !Hor Hchi.
    rewrite Hplc.
    by case: (p0.1 == c); case: (p0.2 == c); case: (p1.1 == c); case: (p1.2 == c); case: has.
  apply: (leq_trans (pmsc_card_or _ _)); rewrite leq_add2l.
  exact: pmsc_card_pair.
Qed.

End Excursion.

(* 5. Rotating a row visited once to the head. *)
Lemma pmsc_rot_head rs (v : 'I_N) : v \in rs -> count_mem v rs = 1%N ->
  exists rest, rot (index v rs) rs = v :: rest /\ v \notin rest.
Proof.
move=> Hin Hc.
have Hi : (index v rs < size rs)%N by rewrite index_mem.
exists (drop (index v rs).+1 rs ++ take (index v rs) rs); split.
  by rewrite /rot (drop_nth v Hi) nth_index.
have Hrc : count_mem v (rot (index v rs) rs) = 1%N.
  have Hp : perm_eq (rot (index v rs) rs) rs by rewrite perm_rot.
  by move/permP: Hp => ->.
move: Hrc; rewrite /rot (drop_nth v Hi) nth_index //= eqxx add1n => /eqP.
by rewrite eqSS => /eqP /count_memPn.
Qed.

(* 6. The bound 2 R + C <= 2 K + 2. *)
Theorem pmsc_rows_colors_le rs ps : size ps = size rs -> pmsc_loopfree rs -> pmsc_distinct ps ->
  pmsc_even rs ps -> (2 * pmsc_R rs + pmsc_C ps <= 2 * size rs + 2)%N.
Proof.
have [K HK] := ubnP (size rs); elim: K rs ps HK => // K IH rs ps HK Hs Hl Hd He.
have HC := pmsc_colors_le rs ps Hs Hl Hd He.
have HR := pmsc_R_le rs.
case: (boolP [exists v : 'I_N, (v \in rs) && (count_mem v rs == 1%N)]); last first.
  rewrite negb_exists => /forallP Hall.
  have H2 : (2 * pmsc_R rs <= size rs)%N.
    apply: pmsc_terminal => r Hr.
    have := Hall r; rewrite Hr /= => Hr1.
    have : (0 < count_mem r rs)%N by rewrite -has_pred1 has_count in Hr.
    by case: (count_mem r rs) Hr1 => [|[|k]].
  apply/leP; move/leP: H2; move/leP: HC; rewrite -!plusE -!multE; lia.
case/existsP => v /andP [Hvin /eqP Hv1].
have [rest [Hrot Hvr]] := pmsc_rot_head rs v Hvin Hv1.
set n := index v rs in Hrot.
rewrite -(pmsc_R_rot n rs) -(pmsc_C_rot n ps) -(size_rot n rs).
have Hs' : size (rot n ps) = size (rot n rs) by rewrite !size_rot.
have Hl' : pmsc_loopfree (rot n rs) by rewrite pmsc_loopfree_rot.
have Hd' : pmsc_distinct (rot n ps) by rewrite pmsc_distinct_rot.
have He' : pmsc_even (rot n rs) (rot n ps) by apply/(pmsc_even_rot n rs ps Hs).
have HK' : (size (rot n rs) < K.+1)%N by rewrite size_rot.
move: (rot n ps) Hs' Hd' He' => ps' Hs' Hd' He'.
rewrite Hrot in HK' Hl' Hs' He' *.
case: rest Hrot Hvr HK' Hl' Hs' He' => [|w rest'] Hrot Hvr HK' Hl' Hs' He'.
  by move: Hl'; rewrite /pmsc_loopfree rot1_cons /= eqxx.
case/lastP: rest' Hrot Hvr HK' Hl' Hs' He' => [|M u] Hrot Hvr HK' Hl' Hs' He'.
  have HR' := pmsc_R_le [:: v; w].
  have HC' := pmsc_colors_le [:: v; w] ps' Hs' Hl' Hd' He'.
  apply/leP; move/leP: HR'; move/leP: HC'; rewrite /= -!plusE -!multE; lia.
case: ps' Hs' Hd' He' => [|p0 ps1] Hs' Hd' He' //.
case/lastP: ps1 Hs' Hd' He' => [|Q pl] Hs' Hd' He'.
  by move: Hs'; rewrite /= size_rcons.
have HQ : size Q = (size M).+1 by move: Hs'; rewrite /= !size_rcons => -[].
case: (eqVneq u w) => [Euw | Huw].
- subst w.
  case: Q HQ Hs' Hd' He' => [|p1 Q'] HQ Hs' Hd' He' //.
  have HQ' : size Q' = size M by case: HQ.
  have [Hl2 Hd2 He2 HR2 HC2] := pmsc_excursion v u M p0 p1 pl Q' HQ' Hvr Hl' Hd' He'.
  have Hs2 : size (p1 :: Q') = size (u :: M) by rewrite /= HQ'.
  have HK2 : (size (u :: M) < K)%N.
    by move: HK'; rewrite /= size_rcons !ltnS => /ltnW.
  have IH2 := IH (u :: M) (p1 :: Q') HK2 Hs2 Hl2 Hd2 He2.
  rewrite HR2 /= size_rcons.
  apply/leP; move/leP: IH2; move/leP: HC2; rewrite /= -!plusE -!multE; lia.
- have [Hl2 Hd2 He2 HR2 HC2] := pmsc_contract v w u M p0 pl Q HQ Hvr Huw Hl' Hd' He'.
  have Hs2 : size (rcons Q pl) = size (w :: rcons M u) by rewrite /= !size_rcons HQ.
  have HK2 : (size (w :: rcons M u) < K)%N by move: HK'; rewrite /= !ltnS.
  have IH2 := IH (w :: rcons M u) (rcons Q pl) HK2 Hs2 Hl2 Hd2 He2.
  rewrite HR2 HC2 /=.
  apply/leP; move/leP: IH2; rewrite /= -!plusE -!multE; lia.
Qed.

End Walks.
