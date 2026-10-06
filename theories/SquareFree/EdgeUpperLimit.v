(* The upper spectral edge of the square-free block with probability
   tending to one, second part. V is the square-free block and W the
   off-diagonal part of V V^T.
   - The event t^L < tr W^L is measurable. Outside it, -t I <= W <= t I
     for L = 2^(j+1) (paper_main_squarefree_offdiag_event_bound).
   - Markov and the trace moment of SquareFree.EdgeUpper give
     P (t^L < tr W^L) <= N (52 d^2)^L / t^L
     (paper_main_squarefree_offdiag_event_markov).
   - The walk length L(d) = 2^(k+3), with k = trunc_log 2 (trunc_log 2 d),
     satisfies L >= 32, 16 L^2 (2L)^45 <= d and d^3 <= 2^L once
     d >= 2^9600 (pmel_L_facts, from 2^190 l^47 <= 2^l for l >= 48 * 190).
     At t = 104 d^2 the probability is at most 1/d
     (paper_main_squarefree_offdiag_rate), so it tends to 0.
   - With the diagonal event of SquareFree.Diagonal at eps = 1, the
     union paper_main_squarefree_upper_event is measurable, and its
     probability tends to 0 whenever 0 < N(d) <= d^2 eventually
     (paper_main_squarefree_upper_event_tends_to_zero). Outside it,
     V V^T <= 106 d^2 I in the Loewner order
     (paper_main_squarefree_upper_bound). *)
From Stdlib Require Import Reals Lia ArithRing.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions Asymptotics
  Data.FeatureMomentsCoordinates Data.FeatureMoments Feature.GramBlocks
  SquareFree.Diagonal SquareFree.DiagonalLimit SquareFree.WalkMoments
  SquareFree.WalkExpansion SquareFree.WalkBridge Geometry.Psd
  Geometry.Homogeneous Geometry.Separation Geometry.HeadFrobenius
  Geometry.HeadFeature Geometry.HeadCorrection Geometry.HeadCoefficients
  Spectral.SymmetricBilinear Cone.ConditionOperator DiagonalBlock.Trace
  DiagonalBlock.Limit SquareFree.EdgeUpper.
Import GRing.Theory Num.Theory Order.TTheory.

(* 1. The off-diagonal event and Markov. *)
Section Event.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma pmel_W_sym (N d : nat) (xs : seq R) : (pmsw_W N d xs)^T = pmsw_W N d xs.
Proof.
apply/matrixP => i j; rewrite /pmsw_W !mxE eq_sym; case: (i == j) => //.
by apply: eq_bigr => p _; rewrite !pmsw_edge_mono; ring.
Qed.

Definition paper_main_squarefree_offdiag_event (N d L : nat) (t : R) :
    set (paper_main_sample N d) :=
  [set x | t ^+ L < \tr (paper_main_squarefree_offdiag N d x ^+ L)].

Definition pmel_F (N d L : nat) (xs : seq R) : R := \tr (pmsw_W N d xs ^+ L).

Lemma pmel_event_list N d L t :
  paper_main_squarefree_offdiag_event N d L t =
  [set x | Rlt (t ^+ L) (pmel_F N d L (tval x))].
Proof.
apply/seteqP; split => x /=;
  rewrite /paper_main_squarefree_offdiag_event /pmel_F /= paper_main_squarefree_offdiag_list;
  by move/RltP.
Qed.

Theorem paper_main_squarefree_offdiag_event_measurable N d L t : (0 < L)%N ->
  measurable (paper_main_squarefree_offdiag_event N d L t).
Proof.
move=> HL; rewrite pmel_event_list.
have [HC _] := pmsw_offdiag_reg N d L.-1; rewrite prednK in HC => //.
exact: (pmsd_gt_measurable (N * d) (pmel_F N d L) (t ^+ L) HC).
Qed.

Lemma pmel_F_ge0 N d j xs : 0 <= pmel_F N d (2 ^ j.+1) xs.
Proof.
rewrite /pmel_F expnS mul2n -addnn exprD -mulmxE.
have HX := pmeu_trmx_exp _ (pmsw_W N d xs) (2 ^ j) (pmel_W_sym N d xs).
by rewrite -{2}HX; exact: pmdb_trace_gram_ge0.
Qed.

Theorem paper_main_squarefree_offdiag_event_bound N d j (t : R) (x : paper_main_sample N d) :
  0 <= t -> ~ paper_main_squarefree_offdiag_event N d (2 ^ j.+1) t x ->
  paper_main_loewner_le ((- t) *: 1%:M) (paper_main_squarefree_offdiag N d x) /\
  paper_main_loewner_le (paper_main_squarefree_offdiag N d x) (t *: 1%:M).
Proof.
move=> Ht Hx; apply: (pmeu_trace_box _ (paper_main_squarefree_offdiag N d x) t j) => //.
  by rewrite paper_main_squarefree_offdiag_list pmel_W_sym.
by rewrite leNgt; apply/negP.
Qed.

Definition pmel_X N d L (x : (N * d).-tuple (measurableTypeR R)) : measurableTypeR R :=
  pmel_F N d L (tval x).

Lemma pmel_X_measurable N d L : (0 < L)%N ->
  measurable_fun [set: (N * d).-tuple (measurableTypeR R)] (pmel_X N d L).
Proof.
move=> HL; have [HC _] := pmsw_offdiag_reg N d L.-1; rewrite prednK in HC => //.
exact: (gpp_joint_measurable (N * d) (pmel_F N d L) HC).
Qed.

Theorem paper_main_squarefree_offdiag_event_markov N d j (t : R) : (0 < N)%N -> (0 < d)%N ->
  (N <= d ^ 2)%N -> (32 <= 2 ^ j.+1)%N -> (16 * (2 ^ j.+1) ^ 2 * (2 * 2 ^ j.+1) ^ 45 <= d)%N ->
  0 < t ->
  (paper_main_probability N d (paper_main_squarefree_offdiag_event N d (2 ^ j.+1) t) <=
   ((N * (52 * d ^ 2) ^ (2 ^ j.+1))%N%:R / t ^+ (2 ^ j.+1))%:E)%E.
Proof.
move=> HN Hd HNd HL HLd Ht.
have HL0 : (0 < 2 ^ j.+1)%N by rewrite expn_gt0.
have HR := pmsw_offdiag_reg N d (2 ^ j.+1).-1; rewrite prednK in HR => //.
have [HC _] := HR.
have [_ HE] := pmdf_actual (N * d) (pmel_F N d (2 ^ j.+1)) HR.
have Hge xs : 0 <= pmel_F N d (2 ^ j.+1) xs by exact: pmel_F_ge0.
pose X : {RV gaussian_product_law (N * d) >-> (R : realType)} :=
  @MeasurableFun.Pack _ _ _ (R : realType) (pmel_X N d (2 ^ j.+1))
  (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
  (pmel_X_measurable N d (2 ^ j.+1) HL0))).
have Ht' : 0 < t ^+ (2 ^ j.+1) by rewrite exprn_gt0.
have HM := @markov _ _ _ _ X id (t ^+ (2 ^ j.+1)) Ht' (@measurable_id _ _ setT)
  (fun r Hr => Hr) (fun r s _ _ Hrs => Hrs).
have HEX : ('E_(gaussian_product_law (N * d))[(id \o (fun x => `|x|%R)) \o X] =
    (gaussian_iterated_expectation (N * d) (pmel_F N d (2 ^ j.+1)))%:E)%E.
  rewrite unlock -HE; apply: eq_integral => x _ /=.
  by rewrite /pmel_X ger0_norm.
have Hset : [set x | ((t ^+ (2 ^ j.+1))%:E <= `|(X x)%:E|)%E] =
    [set x : (N * d).-tuple (measurableTypeR R) |
      Rle (t ^+ (2 ^ j.+1)) (pmel_F N d (2 ^ j.+1) (tval x))].
  apply/seteqP; split => x /=.
    by rewrite lee_fin /pmel_X ger0_norm //; move/RleP.
  by rewrite lee_fin /pmel_X ger0_norm //; move/RleP.
rewrite Hset HEX in HM.
have Hmeas := pmsd_ge_measurable (N * d) (pmel_F N d (2 ^ j.+1)) (t ^+ (2 ^ j.+1)) HC.
have Hsub : paper_main_squarefree_offdiag_event N d (2 ^ j.+1) t `<=`
    [set x : (N * d).-tuple (measurableTypeR R) |
      Rle (t ^+ (2 ^ j.+1)) (pmel_F N d (2 ^ j.+1) (tval x))].
  rewrite pmel_event_list => x /= Hx; exact: Rlt_le.
have HP : (paper_main_probability N d (paper_main_squarefree_offdiag_event N d (2 ^ j.+1) t) <=
    gaussian_product_law (N * d) [set x : (N * d).-tuple (measurableTypeR R) |
      Rle (t ^+ (2 ^ j.+1))%R (pmel_F N d (2 ^ j.+1) (tval x))])%E.
  rewrite /paper_main_probability; apply: le_measure; rewrite ?inE //.
  exact: paper_main_squarefree_offdiag_event_measurable.
apply: (le_trans HP).
have HM' : (gaussian_product_law (N * d) [set x : (N * d).-tuple (measurableTypeR R) |
      Rle (t ^+ (2 ^ j.+1))%R (pmel_F N d (2 ^ j.+1) (tval x))] <=
    ((t ^+ (2 ^ j.+1))^-1)%:E *
    (gaussian_iterated_expectation (N * d) (pmel_F N d (2 ^ j.+1)))%:E)%E.
  by rewrite lee_pdivlMl.
apply: (le_trans HM'); rewrite -EFinM lee_fin mulrC.
apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
exact: paper_main_squarefree_offdiag_trace_le.
Qed.

End Event.

(* 2. A logarithmic walk length. *)
Lemma pmel_doubling (m : nat) : (10 <= m -> 48 * m.+1 <= 2 ^ m)%N.
Proof.
elim: m => [//|m IH] Hm.
case: (ltngtP m 9) => [H | H | ->].
- by move: Hm; rewrite ltnS leqNgt H.
- have IH' := IH H.
  rewrite expnS; apply: (@leq_trans (2 * (48 * m.+1))); last by rewrite leq_mul2l IH' orbT.
  by apply/ssrnat.leP; rewrite -!multE; lia.
- by [].
Qed.

Lemma pmel_poly_exp (l : nat) : (48 * 190 <= l -> 2 ^ 190 * l ^ 47 <= 2 ^ l)%N.
Proof.
move=> Hl.
set m := (l %/ 48)%N.
have Hm : (190 <= m)%N by rewrite /m leq_divRL // mulnC.
have H48m : (48 * m <= l)%N by rewrite /m mulnC leq_divM.
have Hlt : (l <= 48 * m.+1)%N by rewrite /m mulnC ltnW // ltn_ceil.
have H1 : (l ^ 47 <= (2 ^ m) ^ 47)%N.
  rewrite leq_exp2r //; apply: leq_trans Hlt _; apply: pmel_doubling.
  exact: leq_trans _ Hm.
have H2 : (2 ^ 190 <= 2 ^ m)%N by rewrite leq_exp2l.
apply: (@leq_trans (2 ^ m * (2 ^ m) ^ 47)); first exact: leq_mul.
rewrite -expnM -expnD leq_exp2l //; apply: leq_trans H48m.
by apply/ssrnat.leP; rewrite -!multE -!plusE; lia.
Qed.

Definition pmel_k (d : nat) : nat := trunc_log 2 (trunc_log 2 d).

(* The walk length L(d) = 2^(k+3) with k = log2 (log2 d), so that
   4 (log2 d + 1) <= L(d) <= 8 log2 d. *)
Lemma pmel_L_facts (d : nat) : (2 ^ (48 * 200) <= d)%N ->
  [/\ (32 <= 2 ^ (pmel_k d).+3)%N,
      (16 * (2 ^ (pmel_k d).+3) ^ 2 * (2 * 2 ^ (pmel_k d).+3) ^ 45 <= d)%N &
      (d ^ 3 <= 2 ^ (2 ^ (pmel_k d).+3))%N].
Proof.
move=> Hd.
have HE : forall l : nat, (16 * (8 * l) ^ 2 * (2 * (8 * l)) ^ 45 = 2 ^ 190 * l ^ 47)%N.
  by move=> l; ring.
have Hd0 : (0 < d)%N by apply: leq_trans Hd; rewrite expn_gt0.
set l := trunc_log 2 d.
have Hl1 : (2 ^ l <= d)%N by exact: trunc_logP.
have Hl2 : (d < 2 ^ l.+1)%N by exact: trunc_log_ltn.
have Hl9600 : (48 * 200 <= l)%N.
  rewrite -ltnS -(ltn_exp2l _ _ (isT : (1 < 2)%N)); exact: leq_ltn_trans Hd Hl2.
have Hl0 : (0 < l)%N by exact: leq_trans _ Hl9600.
rewrite /pmel_k -/l; set k := trunc_log 2 l.
have Hk1 : (2 ^ k <= l)%N by exact: trunc_logP.
have Hk2 : (l < 2 ^ k.+1)%N by exact: trunc_log_ltn.
have H4 : (4 <= l)%N by exact: leq_trans _ Hl9600.
have Hk2' : (2 <= k)%N.
  rewrite leqNgt; apply/negP => Hk.
  have H : (2 ^ k.+1 <= 2 ^ 2)%N by rewrite leq_exp2l.
  by move: (leq_trans Hk2 H); rewrite ltnNge H4.
have F1 : (31 < 2 ^ k.+3)%N.
  by apply: (@leq_trans (2 ^ 5)) => //; rewrite leq_exp2l.
have F3 : (d ^ 3 <= 2 ^ 2 ^ k.+3)%N.
  apply: (@leq_trans ((2 ^ l.+1) ^ 3)); first by rewrite leq_exp2r // ltnW.
  rewrite -expnM leq_exp2l //.
  apply: (@leq_trans (2 ^ k.+1 * 4)); first by rewrite leq_mul.
  by rewrite (_ : 4 = 2 ^ 2)%N // -expnD addn2.
have HL8 : (2 ^ k.+3 <= 8 * l)%N.
  by rewrite (expnS 2 k.+2) (expnS 2 k.+1) (expnS 2 k) !mulnA leq_mul2l Hk1 orbT.
have HB : (16 * (2 ^ k.+3) ^ 2 * (2 * 2 ^ k.+3) ^ 45 <=
    16 * (8 * l) ^ 2 * (2 * (8 * l)) ^ 45)%N.
  apply: leq_mul; first by rewrite leq_mul2l leq_exp2r // HL8 orbT.
  by rewrite leq_exp2r // leq_mul2l HL8 orbT.
have Hpe := pmel_poly_exp l (leq_trans (isT : (48 * 190 <= 48 * 200)%N) Hl9600).
by split => //; apply: leq_trans HB _; rewrite HE; apply: leq_trans Hpe Hl1.
Qed.

(* 3. The off-diagonal event at t = 104 d^2 and L = L(d). *)
Section Limit.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition pmel_L (d : nat) : nat := 2 ^ (pmel_k d).+3.
Definition pmel_t (d : nat) : R := 104%:R * d%:R ^+ 2.

Theorem paper_main_squarefree_offdiag_rate (N d : nat) : (0 < N)%N -> (N <= d ^ 2)%N ->
  (2 ^ (48 * 200) <= d)%N ->
  (paper_main_probability N d (paper_main_squarefree_offdiag_event N d (pmel_L d) (pmel_t d)) <=
   (1 / d%:R)%:E)%E.
Proof.
move=> HN HNd Hd.
have [F1 F2 F3] := pmel_L_facts d Hd.
have Hd0 : (0 < d)%N by apply: leq_trans Hd; rewrite expn_gt0.
have Hdr : 0 < d%:R :> R by rewrite ltr0n.
have Ht : 0 < pmel_t d by rewrite /pmel_t mulr_gt0 ?ltr0n // exprn_gt0.
have HM := paper_main_squarefree_offdiag_event_markov N d (pmel_k d).+2 (pmel_t d)
  HN Hd0 HNd F1 F2 Ht.
rewrite /pmel_L; apply: le_trans HM _; rewrite lee_fin.
set L := (2 ^ (pmel_k d).+3)%N.
have HX : 0 < (52 * d ^ 2)%N%:R :> R by rewrite ltr0n muln_gt0 expn_gt0 Hd0.
have Et : pmel_t d = 2%:R * (52 * d ^ 2)%N%:R by rewrite /pmel_t natrM natrX mulrA -natrM.
have H2L : 0 < 2%:R ^+ L :> R by rewrite exprn_gt0 // ltr0n.
(* (52 d^2)^L / (104 d^2)^L = 2^(-L). *)
have E : (N * (52 * d ^ 2) ^ L)%N%:R / pmel_t d ^+ L = N%:R / 2%:R ^+ L :> R.
  rewrite Et exprMn natrM natrX invfM mulrA.
  rewrite [N%:R * _ / _]mulrAC mulfK //.
  by rewrite expf_neq0 // gt_eqF.
(* N 2^(-L) <= d^2 / d^3. *)
rewrite E ler_pdivrMr // div1r ler_pdivlMl //.
rewrite -natrM (_ : 2%:R ^+ L = (2 ^ L)%N%:R :> R); first by rewrite natrX.
rewrite ler_nat; apply: (leq_trans _ F3).
by rewrite (expnS d 2) leq_mul2l HNd orbT.
Qed.

Theorem paper_main_squarefree_offdiag_tends_to_zero (N : nat -> nat) :
  (exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d
    (paper_main_squarefree_offdiag_event (N d) d (pmel_L d) (pmel_t d))) 0.
Proof.
move=> [D HD]; apply: (pmdbl_inv_rate _ 1) => //.
exists (maxn D (2 ^ (48 * 200))) => d Hd.
have [HN HNd] := HD d (leq_trans (leq_maxl _ _) Hd).
by apply: paper_main_squarefree_offdiag_rate => //; exact: leq_trans (leq_maxr _ _) Hd.
Qed.

End Limit.

(* 4. The upper edge of V V^T. *)
Section Upper.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma pmel_tends_to_add (p q : nat -> \bar R) :
  (forall d, (0 <= p d)%E) -> (forall d, (0 <= q d)%E) ->
  paper_main_tends_to p 0 -> paper_main_tends_to q 0 ->
  paper_main_tends_to (fun d => (p d + q d)%E) 0.
Proof.
move=> Hp Hq HP HQ eps Heps.
have He2 : 0 < eps / 2 by rewrite divr_gt0.
have [D1 H1] := HP _ He2; have [D2 H2] := HQ _ He2.
exists (maxn D1 D2) => d Hd.
have := H1 d (leq_trans (leq_maxl _ _) Hd); have := H2 d (leq_trans (leq_maxr _ _) Hd).
rewrite !sube0 !gee0_abs ?adde_ge0 // => Hqd Hpd.
rewrite (_ : eps = eps / 2 + eps / 2); first exact: splitr.
by rewrite EFinD; apply: lteD.
Qed.

Definition paper_main_squarefree_upper_event (N d : nat) : set (paper_main_sample N d) :=
  paper_main_squarefree_offdiag_event N d (pmel_L d) (pmel_t d) `|`
  paper_main_squarefree_diag_event N d 1.

Theorem paper_main_squarefree_upper_event_measurable N d :
  measurable (paper_main_squarefree_upper_event N d).
Proof.
apply: measurableU; last exact: paper_main_squarefree_diag_event_measurable.
by apply: paper_main_squarefree_offdiag_event_measurable; rewrite /pmel_L expn_gt0.
Qed.

Theorem paper_main_squarefree_upper_event_tends_to_zero (N : nat -> nat) :
  (exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d
    (paper_main_squarefree_upper_event (N d) d)) 0.
Proof.
move=> HN.
have HO := paper_main_squarefree_offdiag_tends_to_zero N HN.
have HD : paper_main_tends_to (fun d => paper_main_probability (N d) d
    (paper_main_squarefree_diag_event (N d) d 1)) 0.
  apply: (paper_main_squarefree_diag_tends_to_zero N 1 1); [exact: Rle_0_1 | exact: Rlt_0_1 |].
  have [D HD] := HN; exists D => d /ssrnat.leP Hd.
  have [_ H] := HD d Hd.
  rewrite Rmult_1_l.
  by rewrite !INRE RpowE; apply/RleP; rewrite -natrX ler_nat.
apply: (paper_main_tends_to_zero_squeeze _ (fun d => (paper_main_probability (N d) d
  (paper_main_squarefree_offdiag_event (N d) d (pmel_L d) (pmel_t d)) +
  paper_main_probability (N d) d (paper_main_squarefree_diag_event (N d) d 1))%E)).
- by move=> d; exact: measure_ge0.
- move=> d; rewrite /paper_main_probability /paper_main_squarefree_upper_event.
  apply: measureU2; last exact: paper_main_squarefree_diag_event_measurable.
  by apply: paper_main_squarefree_offdiag_event_measurable; rewrite /pmel_L expn_gt0.
- by apply: pmel_tends_to_add => // d; exact: measure_ge0.
Qed.

(* The diagonal of V V^T outside the diagonal event at eps = 1. *)
Lemma pmel_diag_le N d (x : paper_main_sample N d) (i : 'I_N) : (0 < d)%N ->
  ~ paper_main_squarefree_diag_event N d 1 x ->
  (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) i i <=
  2%:R * d%:R ^+ 2.
Proof.
move=> Hd Hx.
set G := paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T.
have H : ~ Rlt 1 (Rabs (G i i / INR d ^ 2 - 1)) by move=> H; apply: Hx; exists i.
have H' := Rnot_lt_le _ _ H.
move: H'; rewrite RabsE RminusE RdivE RpowE INRE => /RleP.
rewrite (_ : 1%Rcoq = 1 :> R) // ler_norml => /andP [_ H2].
have Hd2 : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0 // ltr0n.
have H3 : G i i / d%:R ^+ 2 <= 2 by move: H2; rewrite lerBlDr (_ : 1 + 1 = 2 :> R) //.
by move: H3; rewrite ler_pdivrMr // mulrC.
Qed.

(* V V^T is its off-diagonal part plus its diagonal. *)
Lemma pmel_form_split N d (x : paper_main_sample N d) (v : 'cV[R]_N) :
  paper_main_quadratic_form
    (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) v =
  paper_main_quadratic_form (paper_main_squarefree_offdiag N d x) v +
  \sum_(i < N) v i 0 ^+ 2 *
    (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) i i.
Proof.
set G := paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T.
have EW i j : paper_main_squarefree_offdiag N d x i j = if i == j then 0 else G i j.
  by rewrite /paper_main_squarefree_offdiag mxE.
rewrite /paper_main_quadratic_form -big_split /=; apply: eq_bigr => i _.
rewrite (bigD1 i) //= [X in _ = X + _](bigD1 i) //= EW eqxx mulr0 mul0r add0r addrC.
congr (_ + _); first by apply: eq_bigr => j Hj; rewrite EW eq_sym (negbTE Hj).
by rewrite expr2 mulrAC.
Qed.

Theorem paper_main_squarefree_upper_bound N d (x : paper_main_sample N d) : (0 < d)%N ->
  ~ paper_main_squarefree_upper_event N d x ->
  paper_main_loewner_le
    (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T)
    ((106%:R * d%:R ^+ 2) *: 1%:M).
Proof.
move=> Hd Hx.
set G := paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T.
have HxO : ~ paper_main_squarefree_offdiag_event N d (pmel_L d) (pmel_t d) x.
  by move=> H; apply: Hx; left.
have HxD : ~ paper_main_squarefree_diag_event N d 1 x by move=> H; apply: Hx; right.
have Ht0 : 0 <= pmel_t d by rewrite /pmel_t mulr_ge0 ?ler0n // exprn_ge0 ?ler0n.
have [_ [_ HW]] := paper_main_squarefree_offdiag_event_bound N d (pmel_k d).+2 (pmel_t d) x
  Ht0 HxO.
have HGs : paper_main_symmetric G.
  by apply/paper_main_symmetricP; rewrite /G trmx_mul trmxK.
split.
  apply: pmh_symmetricB => //; apply: paper_main_symmetric_scale; exact: pmh_symmetric_id.
move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id pmel_form_split.
have HWv := HW v; rewrite pms_formB paper_main_form_scale pmh_form_id in HWv.
(* The diagonal part. *)
have HD : \sum_(i < N) v i 0 ^+ 2 * G i i <= 2%:R * d%:R ^+ 2 * (v^T *m v) 0 0.
  rewrite pmh_vec_dot mulr_sumr; apply: ler_sum => i _.
  rewrite [X in _ <= X]mulrC -expr2; apply: ler_wpM2l; first exact: sqr_ge0.
  exact: (pmel_diag_le N d x i Hd HxD).
rewrite -/G; move: HWv HD; rewrite /pmel_t.
set n := (v^T *m v) 0 0; set q := paper_main_quadratic_form _ v; set S := \sum_(i < N) _.
rewrite (_ : 106%:R = 104%:R + 2%:R :> R); first by rewrite -natrD.
by rewrite RmultE => H1 H2; lra.
Qed.

End Upper.
