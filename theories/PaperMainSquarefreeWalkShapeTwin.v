(* Twin steps of terminal square-free walks (G16, checkpoint B4, item 3).
   For a valid closed walk (rs, ps) of length L, step s goes from rs_s to
   rs_(s+1 mod L) with label pair ps_s, and the multiplicity n_c of a color
   is the number of steps whose pair contains c. Two steps are twins when
   they carry the same colors and both colors have multiplicity 2; a step
   without a twin is lonely. By evenness, the two steps of a color of
   multiplicity 2 join the same two rows (pmst_partner).
   For a terminal walk, where every non-root row is visited at least twice,
   the lonely steps number at most 27 e (pmst_lonely_le), with
   e = 2 L + 2 - 2 R - C:
   - steps with a color of multiplicity >= 3 number at most 6 (L - C)
     (pmst_multi_le), and L - C <= e for terminal walks;
   - a step alone on its row pair has such a color (pmst_alone);
   - the steps on row pairs used >= 3 times number at most 3 (E1 + e), with
     E1 the number of steps alone on their row pair (pmst_M3_le), because
     the first arrivals at the R - 1 non-root rows use distinct row pairs
     (pmst_first_rows);
   - a lonely step has a color of multiplicity >= 3 or lies on a row pair
     used >= 3 times (pmst_lonely_cases).
   No probability premise. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import PaperMainSquarefreeWalkCount PaperMainSquarefreeWalkExcess
  PaperMainSquarefreeWalkShapeOnce.

(* In a terminal walk, the non-root rows are not visited once. *)
Lemma pmst_fv_terminal (N : nat) (r0 : 'I_N) (rs : seq 'I_N) (i : nat) :
  pmso_fv N rs = size rs -> 2 < size rs -> 0 < i < size rs -> count_mem (nth r0 rs i) rs != 1.
Proof.
rewrite /pmso_fv; case: rs => [|r rest] //= HT H2 /andP [Hi0 Hi].
rewrite H2 in HT; case: HT => HT; case: i Hi0 Hi => [|i] //= _ Hi.
have Hf : i < find (pmso_once N (r :: rest)) rest by rewrite HT.
by have := before_find r0 Hf; rewrite /pmso_once /= => /negbT.
Qed.

Section Twin.
Variables (N d : nat) (r0 : 'I_N) (q0 : 'I_d * 'I_d).
Variables (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).
Variable HW : pmso_valid N d rs ps.

Local Notation L := (size rs).
Local Notation chi := (pmsc_chi d).

(* 1. Steps by index. *)
Definition pmst_succ (s : nat) : nat := if s.+1 < L then s.+1 else 0.
Definition pmst_a (s : nat) : 'I_N := nth r0 rs s.
Definition pmst_b (s : nat) : 'I_N := nth r0 rs (pmst_succ s).
Definition pmst_p (s : nat) : 'I_d * 'I_d := nth q0 ps s.
Definition pmst_in (c : 'I_d) (s : nat) : bool := (0 < chi (pmst_p s) c)%N.
Definition pmst_n (c : 'I_d) : nat := \sum_(s < L) pmst_in c s.

Lemma pmst_size_ps : size ps = L.
Proof. by move: HW => /and4P [/eqP]. Qed.

Lemma pmst_succ_lt s : s < L -> pmst_succ s < L.
Proof. by rewrite /pmst_succ; case: ifP => // _ Hs; exact: leq_ltn_trans (leq0n _) Hs. Qed.

Lemma pmst_steps_nth s : s < L ->
  nth ((r0, r0), q0) (pmsc_steps N d rs ps) s = ((pmst_a s, pmst_b s), pmst_p s).
Proof.
move=> Hs; rewrite /pmsc_steps nth_zip.
  by rewrite size_zip size_rot minnn pmst_size_ps.
rewrite nth_zip; first by rewrite size_rot.
rewrite /pmst_a /pmst_b /pmst_p /pmst_succ; congr ((_, _), _).
rewrite /rot nth_cat size_drop subn1.
have E : (s < L.-1) = (s.+1 < L) by rewrite -ltn_predRL.
rewrite E; case: ifP => Hs1.
  by rewrite nth_drop add1n.
have HL : 0 < L by exact: leq_ltn_trans (leq0n s) Hs.
have Es : s - L.-1 = 0 by apply/eqP; rewrite subn_eq0 -ltnS prednK.
by rewrite Es nth_take.
Qed.

Lemma pmst_size_steps : size (pmsc_steps N d rs ps) = L.
Proof. by rewrite /pmsc_steps size_zip size_zip size_rot minnn pmst_size_ps minnn. Qed.

Lemma pmst_deg_eq (r : 'I_N) (c : 'I_d) : pmsc_deg N d rs ps r c =
  \sum_(s < L) ((pmst_a s == r) + (pmst_b s == r)) * chi (pmst_p s) c.
Proof.
rewrite /pmsc_deg (big_nth ((r0, r0), q0)) pmst_size_steps big_mkord.
by apply: eq_bigr => s _; rewrite pmst_steps_nth.
Qed.

Lemma pmst_distinct s : s < L -> (pmst_p s).1 != (pmst_p s).2.
Proof.
move: HW => /and4P [_ _ /allP Hd _] Hs; apply: Hd.
by rewrite mem_nth // pmst_size_ps.
Qed.

Lemma pmst_chi_in s c : s < L -> chi (pmst_p s) c = pmst_in c s.
Proof.
move=> Hs; rewrite /pmst_in; have := pmsc_chi_le1 d _ c (pmst_distinct s Hs).
by case: (chi _ c) => [|[|]].
Qed.

Lemma pmst_n_eq c : pmsc_n d ps c = pmst_n c.
Proof.
rewrite /pmsc_n (big_nth q0) pmst_size_ps big_mkord; apply: eq_bigr => s _.
by rewrite /pmst_p pmst_chi_in.
Qed.

Lemma pmst_loopfree s : s < L -> pmst_a s != pmst_b s.
Proof.
move=> Hs; move: HW => /and4P [_ Hl _ _].
have Hm : nth ((r0, r0), q0) (pmsc_steps N d rs ps) s \in pmsc_steps N d rs ps.
  by rewrite mem_nth // pmst_size_steps.
by have := pmsc_steps_loopfree N d rs ps _ Hl Hm; rewrite pmst_steps_nth.
Qed.

Lemma pmst_even (r : 'I_N) (c : 'I_d) :
  ~~ odd (\sum_(s < L) ((pmst_a s == r) + (pmst_b s == r)) * pmst_in c s).
Proof.
move: HW => /and4P [_ _ _ /pmso_evenP He]; have := He r c.
rewrite pmst_deg_eq; congr (~~ odd _); apply: eq_bigr => s _.
by rewrite pmst_chi_in.
Qed.

(* 2. Two steps of a color of multiplicity two join the same rows. *)
Definition pmst_same (s t : nat) : bool :=
  ((pmst_a s == pmst_a t) && (pmst_b s == pmst_b t)) ||
  ((pmst_a s == pmst_b t) && (pmst_b s == pmst_a t)).

Lemma pmst_two (c : 'I_d) (s t : nat) (G : nat -> nat) : s < L -> t < L -> s != t ->
  pmst_in c s -> pmst_in c t -> pmst_n c = 2 ->
  (\sum_(u < L) G u * pmst_in c u = G s + G t)%N.
Proof.
move=> Hs Ht Hst Hcs Hct Hn.
have Hts : Ordinal Ht != Ordinal Hs by apply: contra Hst => /eqP [->].
move: Hn; rewrite /pmst_n (bigD1 (Ordinal Hs)) // (bigD1 (Ordinal Ht)) /=; first by rewrite Hts.
rewrite Hcs Hct => /eqP; rewrite add1n add1n eqSS eqSS => /eqP H0.
rewrite (bigD1 (Ordinal Hs)) // (bigD1 (Ordinal Ht)) /=; first by rewrite Hts.
rewrite Hcs Hct !muln1 big1 ?addn0 // => u /andP [Hu1 Hu2].
move: H0; rewrite (bigD1 u) /=; first by rewrite Hu1 Hu2.
by case: (pmst_in c u) => //; rewrite muln0.
Qed.

Lemma pmst_partner (c : 'I_d) (s t : nat) : s < L -> t < L -> s != t ->
  pmst_in c s -> pmst_in c t -> pmst_n c = 2 -> pmst_same s t.
Proof.
move=> Hs Ht Hst Hcs Hct Hn.
have Ea := pmst_even (pmst_a s) c; have Eb := pmst_even (pmst_b s) c.
rewrite (pmst_two c s t (fun u => (pmst_a u == pmst_a s) + (pmst_b u == pmst_a s))
  Hs Ht Hst Hcs Hct Hn) in Ea.
rewrite (pmst_two c s t (fun u => (pmst_a u == pmst_b s) + (pmst_b u == pmst_b s))
  Hs Ht Hst Hcs Hct Hn) in Eb.
have Hs' := pmst_loopfree s Hs; have Ht' := pmst_loopfree t Ht.
have Hs2 : (pmst_b s == pmst_a s) = false by rewrite eq_sym (negbTE Hs').
rewrite eqxx Hs2 in Ea; rewrite eqxx (negbTE Hs') in Eb.
rewrite /pmst_same.
case: (eqVneq (pmst_a t) (pmst_a s)) Ea Eb => [Eat | Nat] Ea Eb.
  have Hbt : (pmst_b t == pmst_a s) = false by rewrite -Eat eq_sym (negbTE Ht').
  rewrite Hbt in Ea; rewrite Eat (negbTE Hs') /= in Eb.
  by move: Eb; rewrite negbK !add0n eq_sym; case: (pmst_b s == pmst_b t).
have Hbt : pmst_b t == pmst_a s by move: Ea; case: (pmst_b t == pmst_a s).
have Hbs : (pmst_b t == pmst_b s) = false by rewrite (eqP Hbt) (negbTE Hs').
rewrite Hbs /= addn0 in Eb.
have Hat : pmst_a t == pmst_b s by move: Eb; case: (pmst_a t == pmst_b s).
by rewrite (eqP Hbt) (eqP Hat) !eqxx orbT.
Qed.

(* 3. Twins, lonely steps and row pairs. *)
Definition pmst_twin (s t : nat) : bool :=
  [&& s != t, t < L, [forall c, pmst_in c s == pmst_in c t],
      pmst_n (pmst_p s).1 == 2 & pmst_n (pmst_p s).2 == 2].

Definition pmst_lonely (s : 'I_L) : bool := ~~ [exists t : 'I_L, pmst_twin s t].

Definition pmst_P (s : nat) : nat := \sum_(t < L) pmst_same s t.

Definition pmst_multi (s : nat) : bool := [exists c, pmst_in c s && (2 < pmst_n c)].

Lemma pmst_in_p s c : pmst_in c s = ((pmst_p s).1 == c) || ((pmst_p s).2 == c).
Proof. by rewrite /pmst_in /pmsc_chi addn_gt0 !lt0b. Qed.

Lemma pmst_same_refl s : pmst_same s s.
Proof. by rewrite /pmst_same !eqxx. Qed.

Lemma pmst_same_sym s t : pmst_same s t = pmst_same t s.
Proof.
rewrite /pmst_same.
by case: (eqVneq (pmst_a s) (pmst_a t)); case: (eqVneq (pmst_b s) (pmst_b t));
  case: (eqVneq (pmst_a s) (pmst_b t)); case: (eqVneq (pmst_b s) (pmst_a t)) => //= *;
  rewrite ?eqxx // eq_sym //; subst; rewrite ?eqxx ?andbF ?andbT ?orbF ?orbT // eq_sym.
Qed.

Lemma pmst_same_trans s t u : pmst_same s t -> pmst_same t u -> pmst_same s u.
Proof.
rewrite /pmst_same => /orP [/andP [/eqP H1 /eqP H2] | /andP [/eqP H1 /eqP H2]] /orP
  [/andP [/eqP H3 /eqP H4] | /andP [/eqP H3 /eqP H4]];
  by rewrite H1 H2 ?H3 ?H4 !eqxx ?orbT.
Qed.

Lemma pmst_P_ge1 s : s < L -> 0 < pmst_P s.
Proof.
move=> Hs; rewrite /pmst_P (bigD1 (Ordinal Hs)) //=.
by rewrite pmst_same_refl.
Qed.

Lemma pmst_P_same s t : pmst_same s t -> pmst_P s = pmst_P t.
Proof.
move=> Hst; apply: eq_bigr => u _.
have Hts : pmst_same t s by rewrite pmst_same_sym.
case Hsu: (pmst_same s u); case Htu: (pmst_same t u) => //.
  by move: Htu; rewrite (pmst_same_trans _ _ _ Hts Hsu).
by move: Hsu; rewrite (pmst_same_trans _ _ _ Hst Htu).
Qed.

(* 4. Steps with a color of multiplicity three or more. *)
Lemma pmst_sum_n : (\sum_(c : 'I_d) pmst_n c = 2 * L)%N.
Proof.
rewrite -(eq_bigr _ (fun c _ => pmst_n_eq c)) /pmsc_n exchange_big /=.
rewrite (eq_bigr (fun _ => 2%N)); first by move=> p _; exact: pmsc_chi_sum.
by rewrite big_const_seq count_predT iter_addn_0 pmst_size_ps mulnC.
Qed.

Lemma pmst_n_ge2 c : (0 < pmst_n c)%N -> (2 <= pmst_n c)%N.
Proof.
move: HW => /and4P [/eqP Hs Hl Hd /pmso_evenP He]; rewrite -!pmst_n_eq.
exact: pmsc_n_ge2 N d rs ps c Hs Hl Hd He.
Qed.

Lemma pmst_sum_excess : (\sum_(c : 'I_d) (pmst_n c - 2) = 2 * L - 2 * pmsc_C d ps)%N.
Proof.
have E : (\sum_(c : 'I_d) ((pmst_n c - 2) + 2 * (0 < pmst_n c)) = 2 * L)%N.
  rewrite -pmst_sum_n; apply: eq_bigr => c _.
  case: (posnP (pmst_n c)) => [-> // | Hc].
  by rewrite muln1 subnK // pmst_n_ge2.
rewrite big_split /= -big_distrr /= in E.
have HC : pmsc_C d ps = (\sum_(c : 'I_d) (0 < pmst_n c))%N.
  by rewrite pmsc_C_sum; apply: eq_bigr => c _; rewrite pmst_n_eq.
by rewrite HC -E addnK.
Qed.

Lemma pmst_multi_le : (#|[pred s : 'I_L | pmst_multi s]| <= 3 * (2 * L - 2 * pmsc_C d ps))%N.
Proof.
rewrite -pmst_sum_excess big_distrr /= -sum1_card.
apply: (@leq_trans (\sum_(s : 'I_L) \sum_(c : 'I_d) (pmst_in c s && (2 < pmst_n c)))).
  rewrite big_mkcond /=; apply: leq_sum => s _; rewrite inE.
  case: (boolP (pmst_multi s)) => // /existsP [c Hc].
  by rewrite (bigD1 c) //= Hc.
rewrite exchange_big /=; apply: leq_sum => c _.
case: (ltnP 2 (pmst_n c)) => Hc.
  rewrite (eq_bigr (fun i : 'I_L => pmst_in c i : nat)); first by move=> i _; rewrite andbT.
  rewrite -/(pmst_n c); move: Hc; set n := pmst_n c => Hc.
  by apply/leP; move/leP: Hc; rewrite -!multE -!minusE; lia.
by rewrite big1 // => s _; rewrite andbF.
Qed.

(* 5. Partners, steps alone on their row pair, and lonely steps. *)
Lemma pmst_partner_ex (c : 'I_d) (s : nat) : s < L -> pmst_in c s -> pmst_n c = 2 ->
  exists2 t : 'I_L, (t : nat) != s & pmst_in c t.
Proof.
move=> Hs Hcs Hn.
move: Hn; rewrite /pmst_n (bigD1 (Ordinal Hs)) //= Hcs add1n => -[] H1.
case: (boolP [exists t : 'I_L, (t != Ordinal Hs) && pmst_in c t]) => [/existsP [t /andP [Ht1 Ht2]] | Hno].
  by exists t => //; apply: contra Ht1 => /eqP Ht; apply/eqP; apply: val_inj.
move: H1; rewrite big1 // => i Hi; move: Hno; rewrite negb_exists => /forallP /(_ i).
by rewrite Hi /=; case: (pmst_in c i).
Qed.

Lemma pmst_P_ge2 (s t : 'I_L) : (t : nat) != s -> pmst_same s t -> 2 <= pmst_P s.
Proof.
move=> Hts Hst; have Hts' : t != s by apply: contra Hts => /eqP ->.
rewrite /pmst_P (bigD1 s) //= (bigD1 t) /=; first by rewrite Hts'.
by rewrite pmst_same_refl Hst add1n ltnS addn_gt0 ltnSn.
Qed.

Lemma pmst_alone (s : 'I_L) : pmst_P s = 1 -> pmst_multi s.
Proof.
move=> HP; apply/existsP; exists (pmst_p s).1.
have Hin : pmst_in (pmst_p s).1 s by rewrite pmst_in_p eqxx.
rewrite Hin /= ltnNge; apply/negP => Hle.
have Hn : pmst_n (pmst_p s).1 = 2.
  apply/eqP; rewrite eqn_leq Hle pmst_n_ge2 //.
  by rewrite /pmst_n (bigD1 s) //= Hin.
have [t Hts Hct] := pmst_partner_ex _ s (ltn_ord s) Hin Hn.
have Hst : (s : nat) != t by rewrite eq_sym.
have Hsame := pmst_partner _ s t (ltn_ord s) (ltn_ord t) Hst Hin Hct Hn.
have := pmst_P_ge2 s t Hts Hsame.
by rewrite HP.
Qed.

(* A pair of distinct colors determines the pair of a step up to order. *)
Lemma pmst_in_pair (s t : nat) : s < L -> t < L ->
  pmst_in (pmst_p s).1 t -> pmst_in (pmst_p s).2 t ->
  forall c, pmst_in c s = pmst_in c t.
Proof.
move=> Hs Ht H1 H2 c; rewrite !pmst_in_p in H1 H2 *.
have Ds := pmst_distinct s Hs; have Dt := pmst_distinct t Ht.
move: H1 H2 Ds Dt.
case: (pmst_p s) => a b; case: (pmst_p t) => x y /=.
case: (eqVneq x a) => [-> | Hxa] /=.
  case: (eqVneq y b) => [-> // | Hyb] /=.
  by rewrite orbF => _ /eqP Hab; rewrite Hab eqxx.
move=> /eqP ->.
case: (eqVneq x b) => [-> | Hxb] /=; first by rewrite orbC.
by move=> /eqP Hab; rewrite Hab eqxx.
Qed.

(* A lonely step has a color of multiplicity three or more, or lies on a
   row pair used three times or more. *)
Lemma pmst_lonely_cases (s : 'I_L) : pmst_lonely s -> pmst_multi s || (2 < pmst_P s).
Proof.
move=> Hl; case: (boolP (pmst_multi s)) => //= Hm.
have Hn : forall c, pmst_in c s -> pmst_n c = 2.
  move=> c Hc; apply/eqP; rewrite eqn_leq [(2 <= _)%N]pmst_n_ge2 ?andbT; last first.
    rewrite leqNgt; apply/negP => H3; move/negP: Hm; apply; apply/existsP; exists c.
    by rewrite Hc H3.
  by rewrite /pmst_n (bigD1 s) //= Hc.
have Ha : pmst_in (pmst_p s).1 s by rewrite pmst_in_p eqxx.
have Hb : pmst_in (pmst_p s).2 s by rewrite pmst_in_p eqxx orbT.
have [ta Hta Hcta] := pmst_partner_ex _ s (ltn_ord s) Ha (Hn _ Ha).
have [tb Htb Hctb] := pmst_partner_ex _ s (ltn_ord s) Hb (Hn _ Hb).
case: (eqVneq ta tb) => [Etab | Ntab].
  move: Hl; rewrite /pmst_lonely negb_exists => /forallP /(_ ta).
  rewrite -Etab in Hctb.
  have Heq := pmst_in_pair s ta (ltn_ord s) (ltn_ord ta) Hcta Hctb.
  rewrite /pmst_twin eq_sym Hta ltn_ord /= (Hn _ Ha) (Hn _ Hb) eqxx andbT.
  by have -> : [forall c, pmst_in c s == pmst_in c ta] by apply/forallP => c; rewrite Heq.
have Hsta : (s : nat) != ta by rewrite eq_sym.
have Hstb : (s : nat) != tb by rewrite eq_sym.
have Hsa := pmst_partner _ s ta (ltn_ord s) (ltn_ord ta) Hsta Ha Hcta (Hn _ Ha).
have Hsb := pmst_partner _ s tb (ltn_ord s) (ltn_ord tb) Hstb Hb Hctb (Hn _ Hb).
have Hta' : ta != s by apply: contra Hta => /eqP ->.
have Htb' : tb != s by apply: contra Htb => /eqP ->.
rewrite /pmst_P (bigD1 s) //= (bigD1 ta) /=; first by rewrite Hta'.
rewrite (bigD1 tb) /=; first by rewrite Htb' eq_sym Ntab.
by rewrite pmst_same_refl Hsa Hsb.
Qed.

(* 6. Row pairs: first steps and the partition by pairs. *)
Definition pmst_first (s : 'I_L) : bool := [forall t : 'I_L, (t < s) ==> ~~ pmst_same s t].

Lemma pmst_first_unique (s1 s2 : 'I_L) (t : nat) : pmst_first s1 -> pmst_first s2 ->
  pmst_same s1 t -> pmst_same s2 t -> s1 = s2.
Proof.
move=> /forallP F1 /forallP F2 H1 H2.
have H12 : pmst_same s1 s2 by apply: pmst_same_trans H1 _; rewrite pmst_same_sym.
case: (ltngtP s1 s2) => [Hlt | Hgt | Heq]; last by apply: val_inj.
- by have := F2 s1; rewrite Hlt /= pmst_same_sym H12.
- by have := F1 s2; rewrite Hgt /= H12.
Qed.

Lemma pmst_first_exists (t : 'I_L) : exists2 s : 'I_L, pmst_first s & pmst_same s t.
Proof.
have Hex : exists n, (n < L) && pmst_same n t by exists t; rewrite ltn_ord pmst_same_refl.
case: (ex_minnP Hex) => m /andP [HmL Hmt] Hmin.
exists (Ordinal HmL) => //=.
apply/forallP => u; apply/implyP => Hu /=; apply/negP => Hmu.
have Hut : pmst_same u t by apply: pmst_same_trans Hmt; rewrite pmst_same_sym.
by have := Hmin u; rewrite ltn_ord Hut /= => /(_ isT); rewrite leqNgt Hu.
Qed.

Lemma pmst_partition (K : pred nat) :
  (\sum_(s : 'I_L) (pmst_first s && K (pmst_P s)) * pmst_P s =
   #|[pred t : 'I_L | K (pmst_P t)]|)%N.
Proof.
rewrite -sum1_card [RHS]big_mkcond /=.
under eq_bigr => s _ do rewrite {2}/pmst_P big_distrr /=.
rewrite exchange_big /=; apply: eq_bigr => t _.
rewrite inE.
have [s0 Hs0 Hs0t] := pmst_first_exists t.
rewrite (bigD1 s0) //= big1 ?addn0.
  move=> s Hs; case Hf: (pmst_first s) => //=; case Hst: (pmst_same s t); rewrite ?muln0 //.
  by move: Hs; rewrite (pmst_first_unique s s0 t Hf Hs0 Hst Hs0t) eqxx.
by rewrite Hs0 Hs0t (pmst_P_same _ _ Hs0t) muln1; case: (K _).
Qed.

Lemma pmst_D_le : (6 * #|[pred s : 'I_L | pmst_first s]| <=
  6 * #|[pred s : 'I_L | pmst_P s == 1]| + 3 * #|[pred s : 'I_L | pmst_P s == 2]| +
  2 * #|[pred s : 'I_L | 2 < pmst_P s]|)%N.
Proof.
rewrite -(pmst_partition (fun k => k == 1)) -(pmst_partition (fun k => k == 2)).
rewrite -(pmst_partition (fun k => 2 < k)) -sum1_card !big_distrr -!big_split /=.
rewrite big_mkcond /=; apply: leq_sum => s _; rewrite inE.
case: (pmst_first s) => //=; have := pmst_P_ge1 _ (ltn_ord s).
case: (pmst_P s) => [|[|[|k]]] //= _; rewrite ?muln0 ?mul1n ?addn0 ?add0n.
by rewrite muln1 (leq_mul2l 2 3 k.+3) /= ltnS ltnS ltnS leq0n.
Qed.

Lemma pmst_L_split : (L = #|[pred s : 'I_L | pmst_P s == 1]| +
  #|[pred s : 'I_L | pmst_P s == 2]| + #|[pred s : 'I_L | 2 < pmst_P s]|)%N.
Proof.
rewrite -{1}(card_ord L) -!sum1_card !big_mkcond /=.
rewrite [X in _ = X + _ + _]big_mkcond [X in _ = _ + X + _]big_mkcond.
rewrite [X in _ = _ + X]big_mkcond -!big_split /=; apply: eq_bigr => s _; rewrite !inE.
have := pmst_P_ge1 _ (ltn_ord s); case: (pmst_P s) => [|[|[|k]]] //=.
Qed.

(* The first arrival at a non-root row is a first step. *)
Lemma pmst_first_rows : (pmsc_R N rs <= #|[pred s : 'I_L | pmst_first s]|.+1)%N.
Proof.
rewrite /pmsc_R (cardD1 (nth r0 rs 0)) -add1n; apply: leq_add; first by case: (_ \in _).
apply: leq_trans (leq_imset_card (fun s : 'I_L => pmst_b s) [pred s : 'I_L | pmst_first s]).
apply: subset_leq_card; apply/subsetP => x; rewrite !inE => /andP [Hx0 Hx].
have Hi : index x rs < L by rewrite index_mem.
have Hi0 : 0 < index x rs.
  by rewrite lt0n; apply/eqP => H0; move: Hx0; rewrite -H0 nth_index ?eqxx.
have Hbef j : j < index x rs -> (nth r0 rs j == x) = false.
  by move=> Hj; exact: (before_find r0 Hj).
have Hs : (index x rs).-1 < L by exact: leq_ltn_trans (leq_pred _) Hi.
have Hb : pmst_b (index x rs).-1 = x by rewrite /pmst_b /pmst_succ prednK // Hi nth_index.
apply/imsetP; exists (Ordinal Hs) => //=; rewrite inE; apply/forallP => t; apply/implyP => Ht.
have Ht1 : t.+1 < index x rs by apply: leq_ltn_trans Ht _; rewrite ltn_predL.
have Hat : (pmst_a t == x) = false by apply: Hbef; exact: ltnW.
have Hbt : (pmst_b t == x) = false.
  by rewrite /pmst_b /pmst_succ (ltn_trans Ht1 Hi); exact: Hbef.
by rewrite /pmst_same /= Hb [x == pmst_b t]eq_sym [x == pmst_a t]eq_sym Hat Hbt !andbF.
Qed.

(* Steps on row pairs used at least three times. *)
Lemma pmst_C_le : (pmsc_C d ps <= L)%N.
Proof. by case/and4P: HW => /eqP Hs Hl Hd /pmso_evenP He; exact: pmsc_colors_le. Qed.

Lemma pmst_M3_le : (#|[pred s : 'I_L | 2 < pmst_P s]| <=
  3 * #|[pred s : 'I_L | pmst_P s == 1]| + 3 * pmsc_e N d rs ps)%N.
Proof.
have HD := pmst_D_le; have HR := pmst_first_rows; have HL := pmst_L_split.
have HV := pmso_valid_bound N d rs ps HW; have HC := pmst_C_le.
move: HD HR HL HV HC; rewrite /pmsc_e -!plusE -!multE -!minusE.
by move=> /leP HD /leP HR HL /leP HV /leP HC; apply/leP; lia.
Qed.

(* 7. Terminal walks. *)
Lemma pmst_terminal_R : pmso_fv N rs = L -> (2 * pmsc_R N rs <= L + 2)%N.
Proof.
move=> HT; have [H2|H2] := leqP L 2.
  have := pmsc_R_le N rs; move/leP: H2; rewrite -!plusE -!multE => H2 /leP H.
  by apply/leP; lia.
rewrite -(pmsc_count_sum N rs) /pmsc_R -sum1_card big_mkcond /= big_distrr /=.
apply: (@leq_trans (\sum_(x : 'I_N) (count_mem x rs + (nth r0 rs 0 == x)))).
  apply: leq_sum => x _; rewrite inE; case Hx: (x \in rs); last by rewrite muln0.
  have Hc : 0 < count_mem x rs by rewrite -has_pred1 has_count in Hx.
  rewrite muln1; case: (eqVneq (nth r0 rs 0) x) => [_|Hne] /=; first by rewrite addn1 ltnS.
  have Hi : 0 < index x rs < L.
    rewrite index_mem Hx andbT lt0n; apply/eqP => H0.
    by move: Hne; rewrite -H0 nth_index ?eqxx.
  have := pmst_fv_terminal N r0 rs (index x rs) HT H2 Hi; rewrite nth_index // addn0.
  by move: Hc; case: (count_mem x rs) => [|[|k]].
by rewrite big_split /= pmsc_sum_eq1 leq_add2l.
Qed.

Theorem pmst_lonely_le : pmso_fv N rs = L ->
  (#|[pred s : 'I_L | pmst_lonely s]| <= 27 * pmsc_e N d rs ps)%N.
Proof.
move=> HT; have HR := pmst_terminal_R HT; have HV := pmso_valid_bound N d rs ps HW.
have HC := pmst_C_le; have HM := pmst_multi_le; have H3 := pmst_M3_le.
have H1 : (#|[pred s : 'I_L | pmst_P s == 1]| <= #|[pred s : 'I_L | pmst_multi s]|)%N.
  by apply: subset_leq_card; apply/subsetP => s; rewrite !inE => /eqP; exact: pmst_alone.
have HU : (#|[pred s : 'I_L | pmst_lonely s]| <=
    #|[pred s : 'I_L | pmst_multi s]| + #|[pred s : 'I_L | 2 < pmst_P s]|)%N.
  apply: (@leq_trans #|[predU [pred s : 'I_L | pmst_multi s] & [pred s : 'I_L | 2 < pmst_P s]]|).
    by apply: subset_leq_card; apply/subsetP => s; rewrite !inE; exact: pmst_lonely_cases.
  by rewrite -cardUI leq_addr.
move: HR HV HC HM H3 H1 HU; rewrite /pmsc_e -!plusE -!multE -!minusE.
by move=> /leP HR /leP HV /leP HC /leP HM /leP H3 /leP H1 /leP HU; apply/leP; lia.
Qed.

End Twin.


