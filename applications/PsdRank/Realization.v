From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum zmodp matrix reals.
From mathcomp Require Import fingroup perm.
From GaussianApplications Require Import PsdRankDefinitions.
From GaussianApplications.PsdRank Require Import Model.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the realization of the cells      *)
(*                                                                            *)
(* Item A5 of phase 14 (AGENTS.md, section Phase 14; the plan                 *)
(* notes/phase14-plan.md, section 6.3): the realization of the restrictions   *)
(* of the cells by odd sets and perfect matchings, from 'Exponential PSD rank *)
(* of positively shifted matching matrices' (family 126 of the OpenAI math    *)
(* collection, revision 1581d4cbd, source/sections/matching.tex, lines        *)
(* 68-101), a Rocq formalization of the credited argument, with the encoding  *)
(* of the PSD audit (reviews/phase13-psd-audit/realization.md). It uses the   *)
(* frame of the cells of PsdRank/Model.v and nothing of the local averaging.  *)
(*                                                                            *)
(* realization: let n and k be even with 2 d <= k for d = 100 (departure 2    *)
(* of phase 14: the lemma states k even and 2d <= k, and the theorem file     *)
(* chooses k), t = l + l cells with k t <= n, the graph of 100 permutations   *)
(* sigma j of 'I_l, and charges b of total 1 in 'F_2. Then there are a row    *)
(* U x (an odd set) for every tuple x of local points and a column Mm m (a    *)
(* perfect matching) for every tuple m of local data, such that               *)
(* A_n(rho)(U x, Mm m) = f_eps sigma b (1 - rho) y whenever every cell i      *)
(* is in the support of its restriction, cell_support (b i) (m i) (y i)       *)
(* (x i).                                                                     *)
(*                                                                            *)
(* The construction:                                                          *)
(* - the vertices: a bijection vtx from ('I_t * 'I_k) + 'I_r onto 'I_n, with  *)
(*   r = n - k t, so that cell i holds the vertices vtx (inl (i, c)) and the  *)
(*   remainder the vertices vtx (inr v); the positions within K_n do not      *)
(*   matter;                                                                  *)
(* - the column: the partner function qpart of the local data m, a            *)
(*   fixed-point-free involution: the terminal at position j < 100 of cell i  *)
(*   goes to the terminal at position j of the neighbor cell across the edges *)
(*   of label j (cell_nbr), an internal position p of a cell to std_partner p *)
(*   (the pairs 100 + 2q, 101 + 2q), and a remainder vertex to its            *)
(*   std_partner. Through pairing_matching of Model.v it is a perfect         *)
(*   matching, data_matching m;                                               *)
(* - the row: the union of the local points of the cells, cut_vset x, odd     *)
(*   on the support since its size is the sum of the w(b i) (cut_odd);        *)
(* - the count: on the support an internal pair is inside or outside the      *)
(*   row, so only terminals cross; the crossing terminals are those of bit 1  *)
(*   whose neighbor has bit 0 (cross_zset), and they correspond one to one    *)
(*   to the edges whose two incidence bits differ (cross_pairs_card), so the  *)
(*   crossing number is disagreements sigma b y.                              *)
(*                                                                            *)
(* The row is total: off the support it is a fixed odd set {v0}. Each edge    *)
(* (j, u) of H is counted once, by the end with bit 1, not once per           *)
(* incidence (realization.md, lines 294-297).                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The neighbor of cell i across the edges of label j: the edge (j, u) joins
   lshift l u and rshift l (sigma j u). *)
Definition cell_nbr (l : nat) (sigma : 'I_100 -> {perm 'I_l}) (i : 'I_(l + l))
    (j : 'I_100) : 'I_(l + l) :=
  match split i with
  | inl u => rshift l (sigma j u)
  | inr u => lshift l (((sigma j)^-1)%g u)
  end.

Lemma cell_nbrK l sigma i j : @cell_nbr l sigma (cell_nbr sigma i j) j = i.
Proof.
rewrite -(splitK i); case: (split i) => u; rewrite /cell_nbr unsplitK /=.
  by rewrite (unsplitK (inr _ : 'I_l + 'I_l)) /= permK.
by rewrite (unsplitK (inl _ : 'I_l + 'I_l)) /= permKV.
Qed.

(* A cell is never its own neighbor: the edges go between the two sides. *)
Lemma cell_nbr_neq l sigma i j : @cell_nbr l sigma i j != i.
Proof.
rewrite /cell_nbr; case: splitP => u iu; rewrite -val_eqE /= iu.
  by rewrite gtn_eqF // (leq_trans (ltn_ord u) (leq_addr _ _)).
by rewrite ltn_eqF // (leq_trans (ltn_ord _) (leq_addr _ _)).
Qed.

(* std_partner on 'I_q, q even: an involution without fixed points, which
   keeps the positions >= 100 at or above 100. *)
Lemma std_partnerK q : ~~ odd q -> involutive (@std_partner q).
Proof. by move=> eq v; have /forallP/(_ v)/andP[/eqP] := std_pairing eq. Qed.

Lemma std_partner_neq q (v : 'I_q) : ~~ odd q -> std_partner v != v.
Proof. by move=> eq; have /forallP/(_ v)/andP[] := std_pairing eq. Qed.

Lemma std_partner_ge q (v : 'I_q) : (100 <= v)%N -> (100 <= std_partner v)%N.
Proof.
move=> v100; rewrite /std_partner val_insubd; case: ifP => _ //.
case: ifP => ov; last exact: leqW.
have v100' : (100 < v)%N.
  by rewrite ltn_neqAle v100 andbT; apply/eqP => e; move: ov; rewrite -e.
by rewrite -ltnS prednK // (leq_trans _ v100').
Qed.

(* The arithmetic of the internal pairs (100 + 2q, 101 + 2q). *)
Lemma internal_pair_odd q : odd q -> (100 < q)%N ->
  [&& (99 < q.-1)%N, ~~ odd (q.-1 - 100) & q == q.-1.+1].
Proof.
case: q => [|q] //= oq q101; move: q101; rewrite ltnS => q100.
by rewrite q100 eqxx andbT /= oddB // (negbTE oq).
Qed.

Lemma internal_pair_even q : ~~ odd q -> (100 <= q)%N ->
  [&& (99 < q)%N, ~~ odd (q - 100) & q.+1 == q.+1].
Proof. by move=> eq q100; rewrite q100 eqxx andbT /= oddB // (negbTE eq). Qed.

(* In 'F_2, of two distinct values exactly one is zero. *)
Lemma F2_neq (a c : 'F_2) : a != c -> (a != 0) = (c == 0).
Proof. by case: a => [[|[|//]]] ?; case: c => [[|[|//]]] ?. Qed.

(* In 'F_2, a sum is nonzero exactly when an odd number of terms are. *)
Lemma F2_addn0 (a c : 'F_2) : (a + c != 0) = (a != 0) (+) (c != 0).
Proof. by case: a => [[|[|//]]] ?; case: c => [[|[|//]]] ?. Qed.

Lemma F2_sum_neq0 (q : nat) (F : 'I_q -> 'F_2) :
  (\sum_(i < q) F i != 0) = \big[addb/false]_(i < q) (F i != 0).
Proof. by elim/big_rec2: _ => // i a c _ <-; rewrite F2_addn0. Qed.

(* The left end of the edge of label j at cell i. *)
Definition edge_left (l : nat) (sigma : 'I_100 -> {perm 'I_l}) (i : 'I_(l + l))
    (j : 'I_100) : 'I_l :=
  match split i with
  | inl u => u
  | inr u => ((sigma j)^-1)%g u
  end.

(* The two ends of an edge are i and its neighbor. *)
Lemma edge_ends l sigma i j (u := @edge_left l sigma i j) :
  (i == lshift l u) && (cell_nbr sigma i j == rshift l (sigma j u)) ||
  (i == rshift l (sigma j u)) && (cell_nbr sigma i j == lshift l u).
Proof.
rewrite /u /edge_left /cell_nbr -{1 3 5 7}(splitK i).
case: (split i) => w /=; rewrite ?permKV !eqxx ?orbT //.
  by rewrite (unsplitK (inl _ : 'I_l + 'I_l)) eqxx.
by rewrite (unsplitK (inr _ : 'I_l + 'I_l)) eqxx orbT.
Qed.

Lemma edge_left_l l sigma u j : @edge_left l sigma (lshift l u) j = u.
Proof. by rewrite /edge_left (unsplitK (inl _ : 'I_l + 'I_l)). Qed.

Lemma edge_left_r l sigma u j :
  @edge_left l sigma (rshift l (sigma j u)) j = u.
Proof. by rewrite /edge_left (unsplitK (inr _ : 'I_l + 'I_l)) permK. Qed.

Lemma cell_nbr_l l sigma u j :
  @cell_nbr l sigma (lshift l u) j = rshift l (sigma j u).
Proof. by rewrite /cell_nbr (unsplitK (inl _ : 'I_l + 'I_l)). Qed.

Lemma cell_nbr_r l sigma u j :
  @cell_nbr l sigma (rshift l (sigma j u)) j = lshift l u.
Proof. by rewrite /cell_nbr (unsplitK (inr _ : 'I_l + 'I_l)) permK. Qed.

Section realization.
Variables (n k l : nat) (sigma : 'I_100 -> {perm 'I_l}).
Hypotheses (en : ~~ odd n) (ek : ~~ odd k) (k200 : (2 * 100 <= k)%N).
Hypothesis ktn : (k * (l + l) <= n)%N.
Local Notation t := (l + l)%N.
Local Notation r := (n - k * t)%N.
Local Notation T := (('I_t * 'I_k) + 'I_r)%type.

Lemma card_T : #|{: T}| = n.
Proof. by rewrite card_sum card_prod !card_ord mulnC subnKC. Qed.

Definition vtx (z : T) : 'I_n := cast_ord card_T (enum_rank z).
Definition vtx_inv (v : 'I_n) : T := enum_val (cast_ord (esym card_T) v).

Let er : ~~ odd r.
Proof. by rewrite oddB // oddM (negbTE ek) /= (negbTE en). Qed.

Lemma vtxK : cancel vtx vtx_inv.
Proof. by move=> z; rewrite /vtx /vtx_inv cast_ordK enum_rankK. Qed.

Lemma vtx_invK : cancel vtx_inv vtx.
Proof. by move=> v; rewrite /vtx /vtx_inv enum_valK cast_ordKV. Qed.


Section partner.
Variable m : t.-tuple {perm 'I_k}.

(* The partner of a vertex: a terminal (position p < 100 of cell i) is matched
   to the terminal at the same position of the neighbor cell across the edges
   of label p; an internal position p of cell i to std_partner p of the same
   cell; a remainder vertex to its std_partner. *)
Definition qpart (z : T) : T :=
  match z with
  | inl ic =>
      let p := ((tnth m ic.1)^-1)%g ic.2 in
      if (p < 100)%N then
        let i' := cell_nbr sigma ic.1 (inord p) in inl (i', tnth m i' p)
      else inl (ic.1, tnth m ic.1 (std_partner p))
  | inr v => inr (std_partner v)
  end.

Lemma qpartK : involutive qpart.
Proof.
case => [[i c]|v] /=; last by rewrite std_partnerK.
set p := ((tnth m i)^-1)%g c.
case: ifP => p100 /=; first by rewrite permK p100 cell_nbrK /p permKV.
rewrite permK; have -> : (std_partner p < 100)%N = false.
  by apply/negbTE; rewrite -leqNgt std_partner_ge // leqNgt p100.
by rewrite std_partnerK // /p permKV.
Qed.

Lemma qpart_neq z : qpart z != z.
Proof.
case: z => [[i c]|v] /=.
  set p := ((tnth m i)^-1)%g c; case: ifP => p100.
    apply/eqP => -[e _]; move: (cell_nbr_neq sigma i (inord p)).
    by rewrite e eqxx.
  apply/eqP => -[e].
  have h : std_partner p = p.
    by apply: (@perm_inj _ (tnth m i)); rewrite e /p permKV.
  by move: (std_partner_neq p ek); rewrite h eqxx.
by apply/eqP => -[] /eqP; apply/negP; rewrite std_partner_neq.
Qed.

(* The partner function on the vertices 'I_n of K_n. *)
Definition vpart (v : 'I_n) : 'I_n := vtx (qpart (vtx_inv v)).

Lemma vpart_pairing : pairing vpart.
Proof.
apply/forallP => v; apply/andP; split.
  by rewrite /vpart vtxK qpartK vtx_invK.
rewrite /vpart; apply/negP => /eqP /(congr1 vtx_inv); rewrite vtxK => e.
by move: (qpart_neq (vtx_inv v)); rewrite e eqxx.
Qed.

(* The perfect matching M(m) of the local data m. *)
Definition data_matching : perfect_matching n := pairing_matching vpart_pairing.

End partner.

Let le100k : (100 <= k)%N.
Proof. by apply: leq_trans k200; rewrite leq_pmull. Qed.

(* The terminal vertex of cell i at position j < 100. *)
Definition term (m : t.-tuple {perm 'I_k}) (i : 'I_t) (j : 'I_100) : T :=
  inl (i, tnth m i (widen_ord le100k j)).

Lemma qpart_term m i j : qpart m (term m i j) = term m (cell_nbr sigma i j) j.
Proof.
by rewrite /term /= permK /= ltn_ord inord_val.
Qed.

Lemma term_inj m : injective (fun ij : 'I_t * 'I_100 => term m ij.1 ij.2).
Proof.
move=> [i1 j1] [i2 j2] /= [e1]; rewrite e1 => /perm_inj /(congr1 val) /= e2.
by congr (_, _); apply: val_inj.
Qed.

(* The set of the vertices of the cut row: the local points of the cells. *)
Definition cut_zset (x : t.-tuple {set 'I_k}) : {set T} :=
  [set z : T | if z is inl ic then ic.2 \in tnth x ic.1 else false].

Definition cut_vset (x : t.-tuple {set 'I_k}) : {set 'I_n} := vtx @: cut_zset x.

Section support.
Variables (b : 'rV['F_2]_t) (m : t.-tuple {perm 'I_k})
  (x : t.-tuple {set 'I_k}) (y : 'M['F_2]_(t, 99)).
Hypothesis hsupp : forall i, cell_support (b 0 i) (tnth m i) (row i y) (tnth x i).

Lemma term_in i j : (term m i j \in cut_zset x) = (inc_bit b y i j != 0).
Proof.
have /and3P[_ /forallP ht _] := hsupp i.
have /forallP/(_ (widen_ord le100k j)) := ht j.
by rewrite /= eqxx /= => /eqP <-; rewrite inE.
Qed.

Lemma internal_in i c : (100 <= ((tnth m i)^-1)%g c)%N ->
  (qpart m (inl (i, c)) \in cut_zset x) = (inl (i, c) \in cut_zset x).
Proof.
move=> p100; rewrite /= leqNgt in p100 *; rewrite (negbTE p100) !inE /=.
set p := ((tnth m i)^-1)%g c in p100 *.
have cE : c = tnth m i p by rewrite /p permKV.
rewrite [in RHS]cE.
have /and3P[_ _ /forallP hp] := hsupp i.
have p100' : (100 <= p)%N by rewrite leqNgt.
have vsp : val (std_partner p) = if odd p then (val p).-1 else (val p).+1.
  rewrite /std_partner val_insubd; case: ifP => // /negbT; case: ifP => op.
    move=> kp; exfalso; move: kp.
    by rewrite -leqNgt leqNgt (leq_ltn_trans (leq_pred _) (ltn_ord p)).
  rewrite -leqNgt => kp; exfalso; move: ek.
  have e : (val p).+1 = k by apply/eqP; rewrite eqn_leq kp ltn_ord.
  by rewrite -e /= op.
case op: (odd p).
  have p101 : (100 < p)%N.
    by rewrite ltn_neqAle p100' andbT; apply/eqP => e; move: op; rewrite -e.
  have /forallP/(_ p)/implyP h := hp (std_partner p).
  apply/eqP; apply: h.
  have vsp' : nat_of_ord (std_partner p) = (val p).-1.
    by rewrite -[LHS]/(val _) vsp op.
  by rewrite vsp' vsp op; exact: (internal_pair_odd op p101).
have /forallP/(_ (std_partner p))/implyP h := hp p.
apply/esym/eqP; apply: h; rewrite vsp op.
by apply: internal_pair_even => //; rewrite op.
Qed.

(* The crossing vertices of the cut row: the terminals of the cells whose
   bit is 1 at a position where the neighbor cell has bit 0. *)
Definition cross_pairs : {set 'I_t * 'I_100} :=
  [set ij | (inc_bit b y ij.1 ij.2 != 0) &&
            (inc_bit b y (cell_nbr sigma ij.1 ij.2) ij.2 == 0)].

Lemma cross_zset : [set z in cut_zset x | qpart m z \notin cut_zset x] =
  (fun ij => term m ij.1 ij.2) @: cross_pairs.
Proof.
apply/setP => z; rewrite inE.
apply/andP/imsetP => [[zin zout]|[[i j]]]; last first.
  rewrite inE /= => /andP[h1 h2] ->; split; first by rewrite term_in.
  by rewrite qpart_term term_in (eqP h2) eqxx.
case: z zin zout => [[i c]|v] zin zout; last by move: zin; rewrite inE.
set p := ((tnth m i)^-1)%g c.
have cE : c = tnth m i p by rewrite /p permKV.
case: (ltnP p 100) => p100; last by move: zout; rewrite internal_in // zin.
have zE : inl (i, c) = term m i (Ordinal p100).
  by rewrite /term {1}cE; do 3 congr (_ _); exact: val_inj.
exists (i, Ordinal p100) => //; rewrite inE /= -term_in -zE zin /=.
by move: zout; rewrite zE qpart_term term_in negbK.
Qed.

Lemma cross_pairs_card : #|cross_pairs| = disagreements sigma b y.
Proof.
pose phi (ij : 'I_t * 'I_100) := (ij.2, edge_left sigma ij.1 ij.2).
have inj : {in cross_pairs &, injective phi}.
  move=> [i1 j1] [i2 j2]; rewrite !inE /= => /andP[a1 b1] /andP[a2 b2] [ej].
  rewrite -ej => eu; have := edge_ends sigma i1 j1.
  have := edge_ends sigma i2 j1; rewrite -eu.
  move: a2 b2; rewrite -ej => a2 b2 /=; set u := edge_left sigma i1 j1.
  case/orP => /andP[/eqP h2 /eqP n2]; case/orP => /andP[/eqP h1 /eqP n1].
  - by rewrite h1 h2.
  - by move: a2; rewrite h2 -n1 (eqP b1) eqxx.
  - by move: a2; rewrite h2 -n1 (eqP b1) eqxx.
  - by rewrite h1 h2.
rewrite /disagreements -(card_in_imset inj).
apply: eq_card => -[j u]; rewrite inE.
apply/imsetP/idP => [[[i j']]|dis].
  rewrite inE /= => /andP[a1 b1] [-> ->].
  have := edge_ends sigma i j'; case/orP => /andP[/eqP h /eqP hn].
    by rewrite -h -hn (eqP b1).
  by rewrite -h -hn (eqP b1) eq_sym.
rewrite /= in dis; case: (boolP (inc_bit b y (lshift l u) j != 0)) => hL.
  exists (lshift l u, j); last by rewrite /phi /= edge_left_l.
  by rewrite inE /= hL cell_nbr_l -(F2_neq dis) hL.
exists (rshift l (sigma j u), j); last by rewrite /phi /= edge_left_r.
have dis' : inc_bit b y (rshift l (sigma j u)) j != inc_bit b y (lshift l u) j.
  by rewrite eq_sym.
by rewrite inE /= cell_nbr_r (F2_neq dis') -[_ == 0]negbK hL.
Qed.

End support.

(* The crossing vertices of the cut row in 'I_n are those of cut_zset. *)
Lemma cut_cross m x : #|[set v in cut_vset x | vpart m v \notin cut_vset x]| =
  #|[set z in cut_zset x | qpart m z \notin cut_zset x]|.
Proof.
have vinj : injective vtx := can_inj vtxK.
rewrite -(card_imset _ vinj); apply: eq_card => v.
rewrite -[v]vtx_invK !inE (mem_imset _ _ vinj) /vpart vtxK (mem_imset _ _ vinj).
by rewrite inE (mem_imset _ _ vinj) !inE.
Qed.

Lemma card_cut_zset x : #|cut_zset x| = (\sum_(i < t) #|tnth x i|)%N.
Proof.
rewrite -sum1_card big_mkcond /= big_sumType /=.
have -> : (\sum_(i < r) (if inr i \in cut_zset x then 1 else 0))%N = 0%N.
  by apply: big1 => v _; rewrite inE.
rewrite addn0.
have -> : (\sum_(p : 'I_t * 'I_k) (if inl p \in cut_zset x then 1 else 0))%N =
    (\sum_(i < t) \sum_(c < k) (if inl (i, c) \in cut_zset x then 1 else 0))%N.
  by rewrite pair_bigA; apply: eq_bigr => -[].
apply: eq_bigr => i _; rewrite -sum1_card big_mkcond /= [RHS]big_mkcond /=.
by apply: eq_bigr => c _; rewrite inE.
Qed.

Lemma cut_odd (b : 'rV['F_2]_t) (m : t.-tuple {perm 'I_k})
    (x : t.-tuple {set 'I_k}) (y : 'M['F_2]_(t, 99)) :
  (forall i, cell_support (b 0 i) (tnth m i) (row i y) (tnth x i)) ->
  \sum_(i < t) b 0 i = 1 -> odd #|cut_vset x|.
Proof.
move=> hs hb; rewrite /cut_vset (card_imset _ (can_inj vtxK)) card_cut_zset.
have -> : (\sum_(i < t) #|tnth x i|)%N =
    (\sum_(i < t) cell_weight k (b ord0 i))%N.
  by apply: eq_bigr => i _; have /and3P[/eqP -> _ _] := hs i.
rewrite (@big_morph _ _ odd false addb 0%N addn oddD (erefl _)).
under eq_bigr do rewrite cell_weight_odd.
by rewrite -F2_sum_neq0 (_ : \sum_(i < t) b ord0 i = 1) //; exact: hb.
Qed.

Lemma realization_sec (R : realType) (b : 'rV['F_2]_t) :
  \sum_(i < t) b 0 i = 1 ->
  exists (U : t.-tuple {set 'I_k} -> odd_set n)
         (Mm : t.-tuple {perm 'I_k} -> perfect_matching n),
  forall (rho : R) (m : t.-tuple {perm 'I_k}) (x : t.-tuple {set 'I_k})
         (y : 'M['F_2]_(t, 99)),
    (forall i, cell_support (b 0 i) (tnth m i) (row i y) (tnth x i)) ->
    shifted_matching_mx rho (U x) (Mm m) = f_eps sigma b (1 - rho) y.
Proof.
move=> hb; have tpos : (0 < t)%N.
  case: (posnP t) => [t0|//].
  have e : \sum_(i < t) b 0 i = 0.
    apply: big1 => i _; exfalso; move: (ltn_ord i); move: (nat_of_ord i) => j.
    by rewrite t0.
  by move: hb; rewrite e => /esym/eqP; rewrite oner_eq0.
have n0 : (0 < n)%N.
  by apply: leq_trans ktn; rewrite muln_gt0 tpos andbT (leq_trans _ le100k).
have o1 : odd #|[set Ordinal n0]| by rewrite cards1.
pose U0 : odd_set n := Sub [set Ordinal n0] o1.
exists (fun x => insubd U0 (cut_vset x)), data_matching => rho m x y hs.
rewrite /shifted_matching_mx /f_eps /data_matching.
rewrite (pairing_crossing (vpart_pairing m)) val_insubd (cut_odd hs hb).
rewrite cut_cross (cross_zset hs) (card_imset _ (@term_inj m)) cross_pairs_card.
by rewrite opprB addrA addrAC.
Qed.

End realization.

(* The realization of the restrictions by matchings (matching.tex, lines
   68-101), with departure 2: k even and 2d <= k, d = 100. *)
Lemma realization (R : realType) (n k l : nat) (sigma : 'I_100 -> {perm 'I_l})
    (b : 'rV['F_2]_(l + l)) :
  ~~ odd n -> ~~ odd k -> (2 * 100 <= k)%N -> (k * (l + l) <= n)%N ->
  \sum_(i < l + l) b 0 i = 1 ->
  exists (U : (l + l).-tuple {set 'I_k} -> odd_set n)
         (Mm : (l + l).-tuple {perm 'I_k} -> perfect_matching n),
  forall (rho : R) (m : (l + l).-tuple {perm 'I_k})
         (x : (l + l).-tuple {set 'I_k}) (y : 'M['F_2]_(l + l, 99)),
    (forall i, cell_support (b 0 i) (tnth m i) (row i y) (tnth x i)) ->
    shifted_matching_mx rho (U x) (Mm m) = f_eps sigma b (1 - rho) y.
Proof. by move=> en ek k200 ktn; exact: realization_sec. Qed.
