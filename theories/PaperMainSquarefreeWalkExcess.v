(* The multiplicity excess of even square-free walks (G16, checkpoint B3).
   For a closed walk (rs, ps) of PaperMainSquarefreeWalkCount, with row-color
   degrees deg (r, c), let
     X = sum_(r, c) (deg (r, c) / 2 - [deg (r, c) > 0])
   be the multiplicity excess (the exponent of the weight bound of
   PaperMainSquarefreeWalkWeight) and e = 2 K + 2 - 2 R - C the deficiency.
   For even loop-free walks with distinct label pairs:
   - X + 2 C <= 2 K (pmsc_X_colors_le): each used color c labels n_c steps,
     its degrees add up to 2 n_c and are positive at two rows at least;
   - X <= 2 e, that is X + 2 (2 R + C) <= 2 (2 K + 2) (pmsc_X_le). The
     proof is the induction of PaperMainSquarefreeWalkCount: a contraction
     keeps X, R - K and C (pmsc_contract_X); an excursion lowers K by 2,
     R by 1 and X + C by at most 2 (pmsc_excursion_X); in the terminal case
     2 R <= K.
   No probability premise and no axiom. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import PaperMainSquarefreeWalkCount.

Section Excess.
Variables N d : nat.
Implicit Types (rs : seq 'I_N) (ps : seq ('I_d * 'I_d)).

Local Notation deg := (pmsc_deg N d).
Local Notation chi := (pmsc_chi d).

Definition pmsc_term rs ps (r : 'I_N) (c : 'I_d) : nat :=
  ((deg rs ps r c)./2 - (0 < deg rs ps r c))%N.

Definition pmsc_X rs ps : nat := \sum_(r : 'I_N) \sum_(c : 'I_d) pmsc_term rs ps r c.

Lemma pmsc_X_rot n rs ps : size ps = size rs -> pmsc_X (rot n rs) (rot n ps) = pmsc_X rs ps.
Proof.
move=> Hs; apply: eq_bigr => r _; apply: eq_bigr => c _.
by rewrite /pmsc_term pmsc_deg_rot.
Qed.

(* A row outside the walk has degree 0. *)
Lemma pmsc_deg_notin rs ps r c : r \notin rs -> deg rs ps r c = 0%N.
Proof.
move=> Hr; rewrite /pmsc_deg big_seq big1 // => e He.
have H1 : e.1.1 \in rs.
  by have := pmsc_mem_zip1 _ _ _ _ _ (pmsc_mem_zip1 _ _ _ _ _ He).
have H2 : e.1.2 \in rs.
  have := pmsc_mem_zip2 _ _ _ _ _ (pmsc_mem_zip1 _ _ _ _ _ He).
  by rewrite mem_rot.
have E1 : (e.1.1 == r) = false by apply: contraNF Hr => /eqP <-.
have E2 : (e.1.2 == r) = false by apply: contraNF Hr => /eqP <-.
by rewrite E1 E2.
Qed.

(* The degrees of a color add up to twice its number of steps. *)
Lemma pmsc_deg_sum rs ps c : size ps = size rs ->
  (\sum_(r : 'I_N) deg rs ps r c = 2 * pmsc_n d ps c)%N.
Proof.
move=> Hs; rewrite -(pmsc_n_steps N d rs ps c Hs) /pmsc_deg exchange_big /= big_distrr /=.
apply: eq_bigr => e _; rewrite -big_distrl /= big_split /= !pmsc_sum_eq1.
by rewrite mulnC.
Qed.

Lemma pmsc_half_sum (I : finType) (F : I -> nat) : (forall i, ~~ odd (F i)) ->
  ((\sum_(i : I) (F i)./2).*2 = \sum_(i : I) F i)%N.
Proof.
move=> HF; rewrite (big_morph double doubleD double0).
by apply: eq_bigr => i _; rewrite -[RHS](odd_double_half (F i)) (negbTE (HF i)).
Qed.

(* A used color has positive degree at two rows at least. *)
Lemma pmsc_deg_pos2 rs ps c : size ps = size rs -> pmsc_loopfree N rs ->
  (0 < pmsc_n d ps c)%N -> (2 <= \sum_(r : 'I_N) (0 < deg rs ps r c))%N.
Proof.
move=> Hs Hl Hn.
have : has (fun e => 0 < chi e.2 c)%N (pmsc_steps N d rs ps).
  apply/negPn/negP; rewrite -all_predC => /allP H0.
  move: Hn; rewrite -(pmsc_n_steps N d rs ps c Hs) big_seq big1 // => e /H0 /=.
  by rewrite lt0n negbK => /eqP.
case/hasP => e0 He0 Hchi.
have Hloop := pmsc_steps_loopfree N d rs ps e0 Hl He0.
have Hpos (r : 'I_N) : (r == e0.1.1) || (r == e0.1.2) -> (0 < deg rs ps r c)%N.
  move=> Hr; apply: leq_trans (pmsc_sum_ge _ _ (pmsc_f N d r c) _ He0).
  rewrite /pmsc_f muln_gt0 Hchi andbT addn_gt0.
  by case/orP: Hr => /eqP ->; rewrite eqxx ?orbT.
rewrite (bigD1 e0.1.1) //= (bigD1 e0.1.2) /=.
  by rewrite eq_sym.
by rewrite !Hpos ?eqxx ?orbT.
Qed.

(* 1. The direct bound X + 2 C <= 2 K. *)
Theorem pmsc_X_colors_le rs ps : size ps = size rs -> pmsc_loopfree N rs ->
  pmsc_distinct d ps -> pmsc_even N d rs ps ->
  (pmsc_X rs ps + 2 * pmsc_C d ps <= 2 * size rs)%N.
Proof.
move=> Hs Hl Hd He.
have Htot : (\sum_(c : 'I_d) pmsc_n d ps c = 2 * size rs)%N.
  rewrite /pmsc_n exchange_big /= (eq_bigr (fun _ => 2%N)); first by move=> p _; exact: pmsc_chi_sum.
  by rewrite -Hs; elim: ps {Hs Hd He} => [|p ps IH]; rewrite ?big_nil ?big_cons ?IH //= mulnS.
have Hhalf : forall r c, (nat_of_bool (0 < deg rs ps r c) <= (deg rs ps r c)./2)%N.
  move=> r c; have := He r c; case: (deg rs ps r c) => [|[|k]] //= Hev.
have Hsum : forall c, (\sum_(r : 'I_N) pmsc_term rs ps r c + \sum_(r : 'I_N) (0 < deg rs ps r c) =
    pmsc_n d ps c)%N.
  move=> c; rewrite -big_split /=.
  have -> : (\sum_(r : 'I_N) (pmsc_term rs ps r c + (0 < deg rs ps r c)) =
      \sum_(r : 'I_N) (deg rs ps r c)./2)%N.
    by apply: eq_bigr => r _; rewrite /pmsc_term subnK.
  by apply: double_inj; rewrite pmsc_half_sum ?pmsc_deg_sum // -mul2n.
have HC : (2 * pmsc_C d ps = \sum_(c : 'I_d) 2 * (0 < pmsc_n d ps c))%N.
  rewrite /pmsc_C -sum1_card big_mkcond /= big_distrr /=.
  by apply: eq_bigr => c _; rewrite inE pmsc_used_n.
rewrite HC -Htot /pmsc_X exchange_big /= -big_split /=.
apply: leq_sum => c _.
case Hc: (0 < pmsc_n d ps c)%N; rewrite -(Hsum c) leq_add2l //.
exact: pmsc_deg_pos2 Hs Hl Hc.
Qed.

(* 2. Colors and degrees. *)
Lemma pmsc_C_sum ps : pmsc_C d ps = (\sum_(c : 'I_d) (0 < pmsc_n d ps c))%N.
Proof.
rewrite /pmsc_C -sum1_card big_mkcond /=.
by apply: eq_bigr => c _; rewrite inE pmsc_used_n.
Qed.

Lemma pmsc_deg_used rs ps r c : size ps = size rs ->
  (0 < deg rs ps r c)%N -> (0 < pmsc_n d ps c)%N.
Proof.
move=> Hs Hr.
have : (0 < \sum_(r' : 'I_N) deg rs ps r' c)%N by rewrite (bigD1 r) //= addn_gt0 Hr.
by rewrite pmsc_deg_sum // muln_gt0.
Qed.

Lemma pmsc_half_step (D k : nat) (b : bool) : (k <= 1)%N -> ((0 < D)%N -> b) ->
  ((D + k.*2)./2 - (0 < D + k.*2) <= D./2 - (0 < D) + ((0 < k)%N && b))%N.
Proof.
move=> Hk Hb; rewrite halfD odd_double andbF add0n doubleK.
case: k Hk => [|[|//]] _.
  by rewrite double0 !addn0.
case: D Hb => [|D] Hb //.
rewrite (Hb isT) /=.
apply/leP; rewrite -!plusE -!minusE; lia.
Qed.

(* 3. A contraction keeps X. *)
Section ContractX.
Variables (v w u : 'I_N) (M : seq 'I_N) (p0 pl : 'I_d * 'I_d) (Q : seq ('I_d * 'I_d)).
Variable HQ : size Q = (size M).+1.

Lemma pmsc_contract_deg :
  v \notin w :: rcons M u -> pmsc_distinct d (p0 :: rcons Q pl) ->
  pmsc_even N d (v :: w :: rcons M u) (p0 :: rcons Q pl) ->
  forall r c, deg (v :: w :: rcons M u) (p0 :: rcons Q pl) r c =
    (deg (w :: rcons M u) (rcons Q pl) r c + ((v == r) * chi pl c).*2)%N.
Proof.
move=> Hv Hd He.
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
have Hchi : forall c, chi p0 c = chi pl c.
  apply: pmsc_chi_eq => // c; have := He v c.
  rewrite pmsc_deg_f (pmsc_steps_contract_old N d v w u M p0 pl Q HQ) big_cons pmsc_sum_rcons.
  rewrite pmsc_rows_off //.
  by rewrite /pmsc_f /= eqxx (negbTE Hvw) (negbTE Hvu) add0n addn0 !mul1n.
move=> r c.
rewrite !pmsc_deg_f (pmsc_steps_contract_old N d v w u M p0 pl Q HQ).
rewrite (pmsc_steps_contract_new N d w u M pl Q HQ) big_cons !pmsc_sum_rcons /pmsc_f /= Hchi.
set S := \sum_(e <- zip (zip (w :: M) (rcons M u)) Q) _.
set k := chi pl c.
rewrite -addnn !mulnDl -!plusE -!multE; lia.
Qed.

Lemma pmsc_contract_X :
  v \notin w :: rcons M u -> pmsc_distinct d (p0 :: rcons Q pl) ->
  pmsc_even N d (v :: w :: rcons M u) (p0 :: rcons Q pl) ->
  pmsc_X (v :: w :: rcons M u) (p0 :: rcons Q pl) = pmsc_X (w :: rcons M u) (rcons Q pl).
Proof.
move=> Hv Hd He.
have Hpl : pl.1 != pl.2.
  by move: Hd => /= /andP [_ /allP]; apply; rewrite mem_rcons mem_head.
apply: eq_bigr => r _; apply: eq_bigr => c _.
rewrite /pmsc_term (pmsc_contract_deg Hv Hd He).
case: (eqVneq v r) => [<-|_]; last by rewrite mul0n double0 addn0.
rewrite pmsc_deg_notin // add0n mul1n.
by have := pmsc_chi_le1 d pl c Hpl; case: (chi pl c) => [|[|]].
Qed.

End ContractX.

(* 4. An excursion lowers X + C by at most 2. *)
Section ExcursionX.
Variables (v u : 'I_N) (M : seq 'I_N) (p0 p1 pl : 'I_d * 'I_d) (Q : seq ('I_d * 'I_d)).
Variable HQ : size Q = size M.

Lemma pmsc_excursion_chi :
  v \notin u :: rcons M u -> pmsc_distinct d (p0 :: p1 :: rcons Q pl) ->
  pmsc_even N d (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) ->
  forall c, chi p0 c = chi pl c.
Proof.
move=> Hv Hd He.
have Hvu : u != v by apply: contraNneq Hv => ->; rewrite mem_head.
have Hoff : forall e, e \in zip (u :: M) (rcons M u) -> (e.1 != v) && (e.2 != v).
  move=> e He'; apply/andP; split.
    apply: contraNneq Hv => <-.
    have := pmsc_mem_zip1 _ _ _ _ _ He'; rewrite inE => /orP [/eqP ->|H]; first by rewrite mem_head.
    by rewrite inE mem_rcons inE H !orbT.
  apply: contraNneq Hv => <-.
  have := pmsc_mem_zip2 _ _ _ _ _ He' => H.
  by rewrite inE H orbT.
move: (Hd) => /= /and3P [Hp0 Hp1 HdQ].
have Hpl : pl.1 != pl.2 by move: HdQ => /allP; apply; rewrite mem_rcons mem_head.
apply: pmsc_chi_eq => // c; have := He v c.
rewrite pmsc_deg_f (pmsc_steps_excursion_old N d v u M p0 p1 pl Q HQ) big_cons pmsc_sum_rcons.
rewrite pmsc_rows_off //.
by rewrite /pmsc_f /= eqxx (negbTE Hvu) add0n addn0 !mul1n.
Qed.

Lemma pmsc_excursion_deg :
  v \notin u :: rcons M u -> pmsc_distinct d (p0 :: p1 :: rcons Q pl) ->
  pmsc_even N d (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) ->
  forall r c, deg (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) r c =
    (deg (u :: M) (p1 :: Q) r c + (((v == r) + (u == r)) * chi pl c).*2)%N.
Proof.
move=> Hv Hd He r c.
have Hchi := pmsc_excursion_chi Hv Hd He.
rewrite !pmsc_deg_f (pmsc_steps_excursion_old N d v u M p0 p1 pl Q HQ).
rewrite (pmsc_steps_excursion_new N d u M p1 Q) big_cons pmsc_sum_rcons /pmsc_f /= Hchi.
set S := \sum_(e <- zip (zip (u :: M) (rcons M u)) (p1 :: Q)) _.
set k := chi pl c.
rewrite -addnn !mulnDl -!plusE -!multE; lia.
Qed.

Lemma pmsc_excursion_X :
  v \notin u :: rcons M u -> pmsc_distinct d (p0 :: p1 :: rcons Q pl) ->
  pmsc_even N d (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) ->
  (pmsc_X (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) + pmsc_C d (p0 :: p1 :: rcons Q pl) <=
   pmsc_X (u :: M) (p1 :: Q) + pmsc_C d (p1 :: Q) + 2)%N.
Proof.
move=> Hv Hd He.
have Hs : size (p1 :: Q) = size (u :: M) by rewrite /= HQ.
have Hpl : pl.1 != pl.2.
  by move: Hd => /= /and3P [_ _ /allP]; apply; rewrite mem_rcons mem_head.
have Hchi := pmsc_excursion_chi Hv Hd He.
have Hvu : (u == v) = false.
  by apply/negbTE; apply: contraNneq Hv => ->; rewrite mem_head.
have Hvn : v \notin u :: M.
  apply: contra Hv; rewrite !inE mem_rcons !inE.
  by case/orP => ->; rewrite ?orbT.
pose b (c : 'I_d) := ((0 < chi pl c) && (0 < pmsc_n d (p1 :: Q) c))%N.
have Hterm : forall r c, (pmsc_term (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) r c <=
    pmsc_term (u :: M) (p1 :: Q) r c + (u == r) * b c)%N.
  move=> r c; rewrite /pmsc_term (pmsc_excursion_deg Hv Hd He).
  have Hk := pmsc_chi_le1 d pl c Hpl.
  case: (eqVneq v r) => [<-|Hvr].
    rewrite Hvu pmsc_deg_notin // add0n addn0 mul1n.
    by case: (chi pl c) Hk => [|[|]].
  case: (eqVneq u r) => [<-|Hur]; last by rewrite mul0n double0 !addn0.
  rewrite add0n !mul1n /b; apply: pmsc_half_step => // HD.
  exact: pmsc_deg_used Hs HD.
have HX : (pmsc_X (v :: u :: rcons M u) (p0 :: p1 :: rcons Q pl) <=
    pmsc_X (u :: M) (p1 :: Q) + \sum_(c : 'I_d) b c)%N.
  apply: (@leq_trans (\sum_(r : 'I_N) \sum_(c : 'I_d)
      (pmsc_term (u :: M) (p1 :: Q) r c + (u == r) * b c))%N).
    by apply: leq_sum => r _; apply: leq_sum => c _; exact: Hterm.
  rewrite (eq_bigr (fun r : 'I_N => \sum_(c : 'I_d) pmsc_term (u :: M) (p1 :: Q) r c +
      (u == r) * \sum_(c : 'I_d) b c)%N).
    by move=> r _; rewrite big_split /= big_distrr.
  by rewrite big_split /= -big_distrl /= pmsc_sum_eq1 mul1n.
have Hn : forall c, pmsc_n d (p0 :: p1 :: rcons Q pl) c = (pmsc_n d (p1 :: Q) c + (chi pl c).*2)%N.
  move=> c; rewrite /pmsc_n !big_cons pmsc_sum_rcons Hchi -addnn.
  rewrite -!plusE; lia.
rewrite !pmsc_C_sum.
apply: (leq_trans (leq_add HX (leqnn _))).
rewrite -!addnA leq_add2l -big_split /=.
apply: (@leq_trans (\sum_(c : 'I_d) ((0 < pmsc_n d (p1 :: Q) c) + (0 < chi pl c)))%N).
  apply: leq_sum => c _; rewrite /b Hn addn_gt0 double_gt0.
  by case: (0 < chi pl c)%N; case: (0 < pmsc_n d (p1 :: Q) c)%N.
rewrite big_split /= leq_add2l.
apply: (@leq_trans (\sum_(c : 'I_d) chi pl c)); last by rewrite pmsc_chi_sum.
by apply: leq_sum => c _; case: (chi pl c).
Qed.

End ExcursionX.

(* 5. The bound X <= 2 e. *)
Theorem pmsc_X_le rs ps : size ps = size rs -> pmsc_loopfree N rs -> pmsc_distinct d ps ->
  pmsc_even N d rs ps ->
  (pmsc_X rs ps + 2 * (2 * pmsc_R N rs + pmsc_C d ps) <= 2 * (2 * size rs + 2))%N.
Proof.
have [K HK] := ubnP (size rs); elim: K rs ps HK => // K IH rs ps HK Hs Hl Hd He.
have HXC := pmsc_X_colors_le rs ps Hs Hl Hd He.
have HR := pmsc_R_le N rs.
case: (boolP [exists v : 'I_N, (v \in rs) && (count_mem v rs == 1%N)]); last first.
  rewrite negb_exists => /forallP Hall.
  have H2 : (2 * pmsc_R N rs <= size rs)%N.
    apply: pmsc_terminal => r Hr.
    have := Hall r; rewrite Hr /= => Hr1.
    have : (0 < count_mem r rs)%N by rewrite -has_pred1 has_count in Hr.
    by case: (count_mem r rs) Hr1 => [|[|k]].
  apply/leP; move/leP: H2; move/leP: HXC; rewrite -!plusE -!multE; lia.
case/existsP => v /andP [Hvin /eqP Hv1].
have [rest [Hrot Hvr]] := pmsc_rot_head N rs v Hvin Hv1.
set n := index v rs in Hrot.
rewrite -(pmsc_X_rot n rs ps Hs) -(pmsc_R_rot N n rs) -(pmsc_C_rot d n ps) -(size_rot n rs).
have Hs' : size (rot n ps) = size (rot n rs) by rewrite !size_rot.
have Hl' : pmsc_loopfree N (rot n rs) by rewrite pmsc_loopfree_rot.
have Hd' : pmsc_distinct d (rot n ps) by rewrite pmsc_distinct_rot.
have He' : pmsc_even N d (rot n rs) (rot n ps) by apply/(pmsc_even_rot N d n rs ps Hs).
have HK' : (size (rot n rs) < K.+1)%N by rewrite size_rot.
move: (rot n ps) Hs' Hd' He' => ps' Hs' Hd' He'.
rewrite Hrot in HK' Hl' Hs' He' *.
case: rest Hrot Hvr HK' Hl' Hs' He' => [|w rest'] Hrot Hvr HK' Hl' Hs' He'.
  by move: Hl'; rewrite /pmsc_loopfree rot1_cons /= eqxx.
case/lastP: rest' Hrot Hvr HK' Hl' Hs' He' => [|M u] Hrot Hvr HK' Hl' Hs' He'.
  have HR' := pmsc_R_le N [:: v; w].
  have HXC' := pmsc_X_colors_le [:: v; w] ps' Hs' Hl' Hd' He'.
  apply/leP; move/leP: HR'; move/leP: HXC'; rewrite /= -!plusE -!multE; lia.
case: ps' Hs' Hd' He' => [|p0 ps1] Hs' Hd' He' //.
case/lastP: ps1 Hs' Hd' He' => [|Q pl] Hs' Hd' He'.
  by move: Hs'; rewrite /= size_rcons.
have HQ : size Q = (size M).+1 by move: Hs'; rewrite /= !size_rcons => -[].
case: (eqVneq u w) => [Euw | Huw].
- subst w.
  case: Q HQ Hs' Hd' He' => [|p1 Q'] HQ Hs' Hd' He' //.
  have HQ' : size Q' = size M by case: HQ.
  have [Hl2 Hd2 He2 HR2 HC2] := pmsc_excursion N d v u M p0 p1 pl Q' HQ' Hvr Hl' Hd' He'.
  have HX2 := pmsc_excursion_X v u M p0 p1 pl Q' HQ' Hvr Hd' He'.
  have Hs2 : size (p1 :: Q') = size (u :: M) by rewrite /= HQ'.
  have HK2 : (size (u :: M) < K)%N.
    by move: HK'; rewrite /= size_rcons !ltnS => /ltnW.
  have IH2 := IH (u :: M) (p1 :: Q') HK2 Hs2 Hl2 Hd2 He2.
  rewrite HR2 /= size_rcons.
  apply/leP; move/leP: IH2; move/leP: HC2; move/leP: HX2; rewrite /= -!plusE -!multE; lia.
- have [Hl2 Hd2 He2 HR2 HC2] := pmsc_contract N d v w u M p0 pl Q HQ Hvr Huw Hl' Hd' He'.
  have HX2 := pmsc_contract_X v w u M p0 pl Q HQ Hvr Hd' He'.
  have Hs2 : size (rcons Q pl) = size (w :: rcons M u) by rewrite /= !size_rcons HQ.
  have HK2 : (size (w :: rcons M u) < K)%N by move: HK'; rewrite /= !ltnS.
  have IH2 := IH (w :: rcons M u) (rcons Q pl) HK2 Hs2 Hl2 Hd2 He2.
  rewrite HX2 HR2 HC2 /=.
  apply/leP; move/leP: IH2; rewrite /= -!plusE -!multE; lia.
Qed.

(* The deficiency e = 2 K + 2 - 2 R - C bounds the excess: X <= 2 e. *)
Definition pmsc_e rs ps : nat := (2 * size rs + 2 - (2 * pmsc_R N rs + pmsc_C d ps))%N.

Corollary pmsc_X_le_e rs ps : size ps = size rs -> pmsc_loopfree N rs -> pmsc_distinct d ps ->
  pmsc_even N d rs ps -> (pmsc_X rs ps <= 2 * pmsc_e rs ps)%N.
Proof.
move=> Hs Hl Hd He.
have H := pmsc_X_le rs ps Hs Hl Hd He.
rewrite /pmsc_e; apply/leP; move/leP: H; rewrite -!plusE -!multE -!minusE; lia.
Qed.

End Excess.
