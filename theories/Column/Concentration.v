(* Uniform concentration of the square-free column norms under the Gaussian
   law.

   For a sample x of N rows of d coordinates and column indices a, b,
     Q_ab(x) = sum_(i < N) (x_(i d + a) x_(i d + b))^2,
   the same coordinates as pmnb_X for the column (a, b) with a < b, and
   Q_ab - N = S_N(tval x) with S_N of Column.ConcentrationMoments.
   1. paper_main_column_pair_markov: for N > 0, eps > 0 and a < b < d,
      Markov's inequality for S_N^4 (MathComp's markov, the law transport
      pmdf_actual and the exact fourth moment) gives
        P(eps N < |Q_ab - N|) <= (10176 N + 192 N (N - 1)) / (eps N)^4.
   2. paper_main_column_event_bound: the column event is the union over
      a < b < d of these events. It is measurable, and the finite union
      bound over the d^2 index pairs gives
        P(column event) <= d^2 (10176 N + 192 N (N - 1)) / (eps N)^4.
   3. paper_main_column_concentration_limit: if N(d) >= c d^2 eventually
      with c > 0, this is at most (10368 / (eps^4 c^2)) / d, so the column
      event probability tends to 0. By paper_main_column_event_complement,
      outside the event every a < b satisfies |Q_ab - N| <= eps N, hence
      |Q_ab / N - 1| <= eps when N > 0. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import Gaussian.IteratedExpectationDefinitions
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  PaperMainDefinitions Data.FeatureMomentsCoordinates Data.FeatureMoments
  SquareFree.Diagonal Gaussian.Union DiagonalBlock.Moment DiagonalBlock.Limit
  Column.ConcentrationMoments.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. Column norms and events. *)
Definition pmcc_q d a b (n : nat) (xs : list R) : R :=
  (\sum_(i < n) (List.nth (i * d + a) xs 0 * List.nth (i * d + b) xs 0) ^+ 2)%R.

Definition paper_main_column_q N d (x : paper_main_sample N d) (a b : nat) : R :=
  pmcc_q d a b N (tval x).

Lemma pmcc_q_S d a b n xs : pmcc_q d a b n xs - n%:R = pmccm_S d a b n xs.
Proof.
rewrite /pmcc_q /pmccm_S /pmccm_row /pmccm_y.
by rewrite sumrB sumr_const card_ord.
Qed.

Definition paper_main_column_pair_event N d (eps : R) (a b : nat) : set (paper_main_sample N d) :=
  [set x | eps * N%:R < `|paper_main_column_q N d x a b - N%:R|].

Definition paper_main_column_event N d (eps : R) : set (paper_main_sample N d) :=
  [set x | exists a b : 'I_d, (a < b)%N /\ paper_main_column_pair_event N d eps a b x].

Lemma paper_main_column_pair_event_measurable N d eps a b : (a < d)%N -> (b < d)%N ->
  measurable (paper_main_column_pair_event N d eps a b).
Proof.
move=> Ha Hb.
have [HC _] := pmccm_S_reg1 d a b N Ha Hb.
have HA := finite_joint_continuous_abs (N * d) _ HC.
have -> : paper_main_column_pair_event N d eps a b =
    [set x | Rlt (eps * N%:R) (Rabs (pmccm_S d a b N (tval x)))].
  apply/seteqP; split => x /=;
    rewrite /paper_main_column_pair_event /paper_main_column_q /= pmcc_q_S; by move/RltP.
exact: (pmsd_gt_measurable (N * d) _ (eps * N%:R) HA).
Qed.

(* The column event as a finite union over the index pairs k = a d + b. *)
Definition pmcc_index_event N d eps (k : nat) : set (paper_main_sample N d) :=
  if (k %/ d < k %% d)%N then paper_main_column_pair_event N d eps (k %/ d) (k %% d) else set0.

Lemma pmcc_index_range d k : List.In k (List.seq 0 (d * d)%N) ->
  (0 < d)%N /\ (k %/ d < d)%N /\ (k %% d < d)%N.
Proof.
move=> /List.in_seq [_ Hk].
have Hk' : (k < d * d)%N by apply/ssrnat.ltP; lia.
have Hd : (0 < d)%N by case: d Hk Hk'.
split => //; split; first by rewrite ltn_divLR.
by rewrite ltn_pmod.
Qed.

Lemma pmcc_event_union N d eps :
  paper_main_column_event N d eps =
  paper_main_finite_event_union (List.seq 0 (d * d)%N) (pmcc_index_event N d eps).
Proof.
apply/seteqP; split => x.
- move=> [a [b [Hab Hx]]].
  apply/paper_main_finite_event_union_member; exists (a * d + b)%N; split.
    apply/List.in_seq; split; first exact: Nat.le_0_l.
    by apply/ssrnat.ltP; rewrite /=; exact: (pmdm_index_lt d d a b (ltn_ord a) (ltn_ord b)).
  have Hd : (0 < d)%N by apply: leq_ltn_trans (leq0n a) (ltn_ord a).
  rewrite /pmcc_index_event divnMDl // modnMDl divn_small // modn_small // addn0 Hab.
  exact: Hx.
- move/paper_main_finite_event_union_member => [k [Hk Hx]].
  have [Hd [Ha Hb]] := pmcc_index_range d k Hk.
  move: Hx; rewrite /pmcc_index_event; case: ifP => Hlt Hx; last by case: Hx.
  by exists (Ordinal Ha), (Ordinal Hb); split.
Qed.

Theorem paper_main_column_event_measurable N d eps :
  measurable (paper_main_column_event N d eps).
Proof.
rewrite pmcc_event_union; apply: paper_main_gaussian_union_measurable => k Hk.
have [Hd [Ha Hb]] := pmcc_index_range d k Hk.
rewrite /pmcc_index_event; case: ifP => _; last exact: measurable0.
exact: paper_main_column_pair_event_measurable.
Qed.

(* 2. Markov for one pair. *)
Definition pmcc_X N d a b (x : (N * d).-tuple (measurableTypeR R)) : measurableTypeR R :=
  pmccm_S d a b N (tval x) ^+ 4.

Lemma pmcc_X_measurable N d a b : (a < d)%N -> (b < d)%N ->
  measurable_fun [set: (N * d).-tuple (measurableTypeR R)] (pmcc_X N d a b).
Proof.
move=> Ha Hb; have [HC _] := pmccm_S_reg d a b N 4 Ha Hb.
exact: (gpp_joint_measurable (N * d) _ HC).
Qed.

Theorem paper_main_column_pair_markov N d (eps : R) a b : (0 < N)%N -> 0 < eps ->
  (a < b)%N -> (b < d)%N ->
  (paper_main_probability N d (paper_main_column_pair_event N d eps a b) <=
   ((10176 * N%:R + 192 * N%:R * (N%:R - 1)) / (eps * N%:R) ^+ 4)%:E)%E.
Proof.
move=> HN Heps Hab Hbd.
have Had : (a < d)%N := ltn_trans Hab Hbd.
have Hneq : a <> b by move=> E; rewrite E ltnn in Hab.
have HR := pmccm_S_reg d a b N 4 Had Hbd.
have [HC _] := HR.
have [_ HE] := pmdf_actual (N * d) (fun xs => pmccm_S d a b N xs ^+ 4) HR.
have Hge xs : 0 <= pmccm_S d a b N xs ^+ 4.
  by rewrite (_ : 4%N = (2 * 2)%N) // exprM; exact: sqr_ge0.
pose X : {RV gaussian_product_law (N * d) >-> (R : realType)} :=
  @MeasurableFun.Pack _ _ _ (R : realType) (pmcc_X N d a b)
  (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
  (pmcc_X_measurable N d a b Had Hbd))).
set t := (eps * N%:R) ^+ 4.
have HN0 : 0 < N%:R :> R by rewrite ltr0n.
have Ht : 0 < t by rewrite /t exprn_gt0 // mulr_gt0.
have HM := @markov _ _ _ _ X id t Ht (@measurable_id _ _ setT) (fun r Hr => Hr)
  (fun r s _ _ Hrs => Hrs).
have HEX : ('E_(gaussian_product_law (N * d))[(id \o (fun x => `|x|%R)) \o X] =
    (gaussian_iterated_expectation (N * d) (fun xs => pmccm_S d a b N xs ^+ 4))%:E)%E.
  rewrite unlock -HE; apply: eq_integral => x _ /=.
  by rewrite /pmcc_X ger0_norm.
have Hset : [set x | (t%:E <= `|(X x)%:E|)%E] =
    [set x : (N * d).-tuple (measurableTypeR R) | Rle t (pmccm_S d a b N (tval x) ^+ 4)].
  apply/seteqP; split => x /=.
    by rewrite lee_fin /pmcc_X ger0_norm //; move/RleP.
  by rewrite lee_fin /pmcc_X ger0_norm //; move/RleP.
rewrite Hset HEX in HM.
have Hsub : paper_main_column_pair_event N d eps a b `<=`
    [set x : (N * d).-tuple (measurableTypeR R) | Rle t (pmccm_S d a b N (tval x) ^+ 4)].
  move=> x /=; rewrite /paper_main_column_pair_event /paper_main_column_q /= pmcc_q_S => Hx.
  apply/RleP; rewrite /t.
  have H1 : 0 <= eps * N%:R by rewrite mulr_ge0 // ltW.
  have H2 := ltW Hx.
  have H3 : (eps * N%:R) ^+ 4 <= `|pmccm_S d a b N (tval x)| ^+ 4.
    by apply: lerXn2r; rewrite ?nnegrE // (le_trans H1 H2).
  by rewrite -normrX ger0_norm in H3.
have Hmeas := pmsd_ge_measurable (N * d) _ t HC.
have Hmeas2 := paper_main_column_pair_event_measurable N d eps a b Had Hbd.
have HP : (paper_main_probability N d (paper_main_column_pair_event N d eps a b) <=
    gaussian_product_law (N * d)
      [set x : (N * d).-tuple (measurableTypeR R) | Rle t (pmccm_S d a b N (tval x) ^+ 4)%R])%E.
  by rewrite /paper_main_probability; apply: le_measure; rewrite ?inE.
apply: (le_trans HP).
have HM' : (gaussian_product_law (N * d)
      [set x : (N * d).-tuple (measurableTypeR R) | Rle t (pmccm_S d a b N (tval x) ^+ 4)%R] <=
    (t^-1)%:E * (gaussian_iterated_expectation (N * d) (fun xs => pmccm_S d a b N xs ^+ 4)%R)%:E)%E.
  by rewrite lee_pdivlMl.
apply: (le_trans HM'); rewrite -EFinM lee_fin mulrC.
apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
by rewrite (pmccm_S_moment4 d a b N Had Hbd Hneq).
Qed.

(* 3. The union bound. *)
Theorem paper_main_column_event_bound N d (eps : R) : (0 < N)%N -> 0 < eps ->
  (paper_main_probability N d (paper_main_column_event N d eps) <=
   ((d%:R ^+ 2 * (10176 * N%:R + 192 * N%:R * (N%:R - 1))) / (eps * N%:R) ^+ 4)%:E)%E.
Proof.
move=> HN Heps.
set M := 10176 * N%:R + 192 * N%:R * (N%:R - 1).
set t := (eps * N%:R) ^+ 4.
have HN1 : 1 <= N%:R :> R by rewrite ler1n.
have HM0 : 0 <= M by rewrite /M; nra.
have Ht : 0 < t by rewrite /t exprn_gt0 // mulr_gt0 // ltr0n.
have HB0 : 0 <= M / t by rewrite divr_ge0 // ltW.
rewrite pmcc_event_union /paper_main_probability.
apply: le_trans (paper_main_gaussian_union_bound (N * d) (List.seq 0 (d * d)) _ (M / t) _ _) _.
- move=> k Hk; have [Hd [Ha Hb]] := pmcc_index_range d k Hk.
  rewrite /pmcc_index_event; case: ifP => _; last exact: measurable0.
  exact: paper_main_column_pair_event_measurable.
- move=> k Hk; have [Hd [Ha Hb]] := pmcc_index_range d k Hk.
  rewrite /pmcc_index_event; case: ifP => Hlt.
    exact: (paper_main_column_pair_markov N d eps _ _ HN Heps Hlt Hb).
  by rewrite measure0 lee_fin.
- by rewrite lee_fin List.length_seq INRE natrM -expr2 mulrA.
Qed.

(* 4. The rate and the limit. *)
Lemma pmcc_rate (c eps : R) (N d : nat) : 0 < c -> 0 < eps -> (0 < d)%N ->
  c * d%:R ^+ 2 <= N%:R ->
  (d%:R ^+ 2 * (10176 * N%:R + 192 * N%:R * (N%:R - 1))) / (eps * N%:R) ^+ 4 <=
  (10368 / (eps ^+ 4 * c ^+ 2)) / d%:R.
Proof.
move=> Hc Heps Hd HcN.
set n := N%:R in HcN *; set x := d%:R in HcN *.
have Hx1 : 1 <= x by rewrite /x ler1n.
have Hx0 : 0 < x by lra.
have Hcx2 : 0 < c * x ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have Hn0 : 0 < n by lra.
have HN0 : (0 < N)%N by rewrite -(ltr0n R).
have Hn1 : 1 <= n by rewrite /n ler1n.
set M := 10176 * n + 192 * n * (n - 1).
have HM0 : 0 <= M by rewrite /M; nra.
have HM : M <= 10368 * n ^+ 2 by rewrite /M; nra.
have Hcx : c ^+ 2 * x ^+ 3 <= n ^+ 2.
  have H1 : c ^+ 2 * x ^+ 4 <= n ^+ 2.
    have -> : c ^+ 2 * x ^+ 4 = (c * x ^+ 2) ^+ 2 by rewrite exprMn -exprM.
    by apply: lerXn2r; rewrite ?nnegrE // ltW.
  have H2 : x ^+ 3 <= x ^+ 4 by exact: (ler_weXn2l Hx1 (isT : (3 <= 4)%N)).
  apply: le_trans H1; apply: ler_wpM2l => //; exact: exprn_ge0 (ltW Hc).
have Ht : 0 < (eps * n) ^+ 4 by rewrite exprn_gt0 // mulr_gt0.
have He4 : 0 < eps ^+ 4 by rewrite exprn_gt0.
have Hc2 : 0 < c ^+ 2 by rewrite exprn_gt0.
rewrite ler_pdivrMr //.
rewrite [X in _ <= X]mulrAC ler_pdivlMr //.
have Hec : 0 < eps ^+ 4 * c ^+ 2 by rewrite mulr_gt0.
rewrite [X in _ <= X]mulrAC ler_pdivlMr //.
have Hcore : c ^+ 2 * x ^+ 3 * M <= n ^+ 2 * (10368 * n ^+ 2).
  apply: ler_pM => //; apply: mulr_ge0; [exact: exprn_ge0 (ltW Hc) | exact: exprn_ge0 (ltW Hx0)].
have E1 : x ^+ 2 * M * x * (eps ^+ 4 * c ^+ 2) = eps ^+ 4 * (c ^+ 2 * x ^+ 3 * M) by ring.
have E2 : 10368 * (eps * n) ^+ 4 = eps ^+ 4 * (n ^+ 2 * (10368 * n ^+ 2)) by ring.
rewrite E1 E2; apply: ler_wpM2l => //; exact: ltW.
Qed.

Theorem paper_main_column_concentration_limit (N : nat -> nat) (c eps : R) :
  0 < c -> 0 < eps -> paper_main_eventually_ge (paper_main_density N) c ->
  paper_main_tends_to
    (fun d => paper_main_probability (N d) d (paper_main_column_event (N d) d eps)) 0.
Proof.
move=> Hc Heps [D HD].
have Hc2 : 0 < c ^+ 2 by rewrite exprn_gt0.
have He4 : 0 < eps ^+ 4 by rewrite exprn_gt0.
have HA : 0 <= 10368 / (eps ^+ 4 * c ^+ 2).
  by apply: divr_ge0; [exact: ler0n | apply: ltW; rewrite mulr_gt0].
apply: (pmdbl_inv_rate _ _ HA); first by move=> d; exact: measure_ge0.
exists (maxn D 1) => d Hd.
have HdD : (D <= d)%N by exact: leq_trans (leq_maxl _ _) Hd.
have Hd1 : (0 < d)%N by exact: leq_trans (leq_maxr _ _) Hd.
have Hd0 : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0 // ltr0n.
have HcN : c * d%:R ^+ 2 <= (N d)%:R.
  by have := HD d HdD; rewrite /paper_main_density ler_pdivlMr.
have HN0 : (0 < N d)%N.
  by rewrite -(ltr0n R); apply: lt_le_trans HcN; rewrite mulr_gt0.
apply: (le_trans (paper_main_column_event_bound (N d) d eps HN0 Heps)).
by rewrite lee_fin; exact: pmcc_rate.
Qed.

(* Outside the column event every column norm is close to N. *)
Lemma paper_main_column_event_complement N d (eps : R) (x : paper_main_sample N d) (a b : 'I_d) :
  ~ paper_main_column_event N d eps x -> (a < b)%N ->
  `|paper_main_column_q N d x a b - N%:R| <= eps * N%:R /\
  ((0 < N)%N -> `|paper_main_column_q N d x a b / N%:R - 1| <= eps).
Proof.
move=> Hx Hab.
have H1 : `|paper_main_column_q N d x a b - N%:R| <= eps * N%:R.
  rewrite leNgt; apply/negP => Hlt; apply: Hx; exists a, b; split => //.
split => // HN.
have HN0 : 0 < N%:R :> R by rewrite ltr0n.
have HN0' : N%:R != 0 :> R by rewrite gt_eqF.
have -> : paper_main_column_q N d x a b / N%:R - 1 =
    (paper_main_column_q N d x a b - N%:R) / N%:R by rewrite mulrBl divff.
by rewrite normrM normfV (gtr0_norm HN0) ler_pdivrMr.
Qed.
