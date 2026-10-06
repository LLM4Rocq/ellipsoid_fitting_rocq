(* Good events for the non-backtracking column frame.

   Fix c > 0 and C0 = 2 + 109 / c (paper_main_frame_constant c), which does
   not depend on delta. For delta > 0 the frame event at (N, d, delta)
   (paper_main_column_frame_event) is the union of
   - the column event paper_main_column_event at min(delta, 1)
     (Column.Concentration);
   - the feature upper event paper_main_feature_upper_event
     (Feature.UpperProbability), outside which the Gram matrix
     Q Q^* of the raw features is at most (3 N + 106 d^2) I;
   - the coordinate clipping event at sqrt(sqrt d);
   - the square-free diagonal event at delta / 4.
   1. paper_main_column_frame_event_measurable: it is measurable for every
      N, d and delta. paper_main_column_frame_event_limit: if N(d) has
      eventual density >= c and eventually 0 < N(d) <= d^2, its probability
      tends to 0.
   2. paper_main_column_frame_raw: outside it, for d > 0, 0 < N <= d^2 and
      c d^2 <= N:
      - every column a < b has Q_ab <= 2 N and |Q_ab / N - 1| <= delta;
      - every product of two coordinates of one row has (x_ia x_ib)^2 <= d,
        since every coordinate has x_ia^2 <= sqrt d;
      - the square-free Gram V V^T satisfies u^T V V^T u <= (109 / c) N |u|^2,
        from V V^T <= Q Q^* <= (3 N + 106 d^2) I <= 109 d^2 I and d^2 <= N / c;
      - every row has |(V V^T)_ii / d^2 - 1| <= delta / 4.
   Column.ConcentrationFrame restates these bounds for pmnb_X,
   pmcr_rankone and pmcr_column_norm. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions Asymptotics
  Fixed.Density Geometry.Psd Geometry.Homogeneous Geometry.HeadCoefficients
  Geometry.HeadCorrection Geometry.Separation Feature.GramBlocks
  SquareFree.EdgeUpperLimit Feature.UpperProbability Data.SampleTail
  Clipping.Limits SquareFree.Diagonal SquareFree.DiagonalLimit
  Column.Concentration.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The constant and the event. *)
Definition paper_main_frame_constant (c : R) : R := (2 + 109 / c)%R.

Definition paper_main_column_frame_event N d (delta : R) : set (paper_main_sample N d) :=
  paper_main_column_event N d (Num.min delta 1)%R `|`
  paper_main_feature_upper_event N d `|`
  paper_main_data_coordinate_event N d (sqrt (sqrt (INR d))) `|`
  paper_main_squarefree_diag_event N d (delta / 4)%R.

Lemma paper_main_frame_constant_ge (c : R) : 0 < c ->
  2 <= paper_main_frame_constant c /\ 109 / c <= paper_main_frame_constant c.
Proof.
move=> Hc; rewrite /paper_main_frame_constant.
have H : 0 <= 109 / c by rewrite divr_ge0 // ltW.
by split; lra.
Qed.

Lemma pmccfe_coordinate_measurable N d :
  measurable (paper_main_data_coordinate_event N d (sqrt (sqrt (INR d)))).
Proof.
case: (posnP d) => [->|Hd].
  have -> : paper_main_data_coordinate_event N 0 (sqrt (sqrt (INR 0))) = set0.
    by apply/seteqP; split => x // [i [[a Ha] _]].
  exact: measurable0.
have Hu : (0 < sqrt (sqrt (INR d)))%Rcoq.
  by apply: sqrt_lt_R0; apply: sqrt_lt_R0; apply: lt_0_INR; apply/ssrnat.ltP.
exact: (paper_main_data_coordinate_tail N d _ Hu).1.
Qed.

Theorem paper_main_column_frame_event_measurable N d delta :
  measurable (paper_main_column_frame_event N d delta).
Proof.
rewrite /paper_main_column_frame_event.
apply: measurableU; last exact: paper_main_squarefree_diag_event_measurable.
apply: measurableU; last exact: pmccfe_coordinate_measurable.
apply: measurableU; first exact: paper_main_column_event_measurable.
exact: paper_main_feature_upper_event_measurable.
Qed.

(* 2. The probability tends to 0. *)
Theorem paper_main_column_frame_event_limit (N : nat -> nat) (c delta : R) :
  0 < c -> 0 < delta -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N) ->
  paper_main_tends_to
    (fun d => paper_main_probability (N d) d (paper_main_column_frame_event (N d) d delta)) 0.
Proof.
move=> Hc Hdelta Hlow Hup.
have Hm : 0 < (Num.min delta 1)%R by rewrite lt_min Hdelta ltr01.
have H1 := paper_main_column_concentration_limit N c _ Hc Hm Hlow.
have H2 := paper_main_feature_upper_event_limit N c Hc Hlow Hup.
have Hup' : exists D, forall d, Nat.le D d -> (INR (N d) <= 1 * INR d ^ 2)%Rcoq.
  have [D HD] := Hup; exists D => d Hd.
  have [_ HNd] := HD d (introT ssrnat.leP Hd).
  have H : ((N d)%:R <= d%:R ^+ 2 :> R) by rewrite -natrX ler_nat.
  by rewrite Rmult_1_l; apply/RleP; rewrite RpowE !INRE.
have H3 := paper_main_coordinate_clipping_tends_to_zero N 1 Rle_0_1 Hup'.
have Hd4 : (0 < (delta / 4)%R)%Rcoq by apply/RltP; rewrite divr_gt0.
have H4 := paper_main_squarefree_diag_tends_to_zero N 1 (delta / 4)%R Rle_0_1 Hd4 Hup'.
apply: (paper_main_tends_to_zero_squeeze_eventually _ (fun d =>
  (paper_main_probability (N d) d (paper_main_column_event (N d) d (Num.min delta 1)%R) +
   paper_main_probability (N d) d (paper_main_feature_upper_event (N d) d) +
   paper_main_probability (N d) d (paper_main_data_coordinate_event (N d) d (sqrt (sqrt (INR d)))) +
   paper_main_probability (N d) d (paper_main_squarefree_diag_event (N d) d (delta / 4)%R))%E) 0).
- by move=> d; exact: measure_ge0.
- move=> d _.
  have mA := paper_main_column_event_measurable (N d) d (Num.min delta 1)%R.
  have mB := paper_main_feature_upper_event_measurable (N d) d.
  have mC := pmccfe_coordinate_measurable (N d) d.
  have mD := paper_main_squarefree_diag_event_measurable (N d) d (delta / 4)%R.
  have mAB := measurableU _ _ mA mB.
  have mABC := measurableU _ _ mAB mC.
  rewrite /paper_main_column_frame_event /paper_main_probability.
  apply: le_trans (measureU2 _ mABC mD) _.
  apply: leeD => //.
  apply: le_trans (measureU2 _ mAB mC) _.
  apply: leeD => //.
  exact: measureU2.
- apply: pmel_tends_to_add => //.
    by move=> d; apply: adde_ge0; [apply: adde_ge0|]; exact: measure_ge0.
  apply: pmel_tends_to_add => //.
    by move=> d; apply: adde_ge0; exact: measure_ge0.
  by apply: pmel_tends_to_add.
Qed.

(* 3. The consequences outside the event. *)
Lemma pmccfe_columns N d (delta : R) (x : paper_main_sample N d) :
  0 < delta -> (0 < N)%N -> ~ paper_main_column_event N d (Num.min delta 1)%R x ->
  forall a b : 'I_d, (a < b)%N ->
    paper_main_column_q N d x a b <= 2 * N%:R /\
    `|paper_main_column_q N d x a b / N%:R - 1| <= delta.
Proof.
move=> Hdelta HN Hx a b Hab.
have [H1 H2] := paper_main_column_event_complement N d (Num.min delta 1)%R x a b Hx Hab.
have Hm1 : (Num.min delta 1)%R <= 1 by rewrite ge_min lexx orbT.
have Hmd : (Num.min delta 1)%R <= delta by rewrite ge_min lexx.
have HN0 : 0 < N%:R :> R by rewrite ltr0n.
split; last exact: le_trans (H2 HN) Hmd.
have Hm : (Num.min delta 1)%R * N%:R <= N%:R by rewrite ler_piMl // ltW.
move: H1; rewrite ler_norml => /andP [_ H1].
lra.
Qed.

Lemma pmccfe_coordinates N d (x : paper_main_sample N d) :
  ~ paper_main_data_coordinate_event N d (sqrt (sqrt (INR d))) x ->
  forall (i : 'I_N) (a b : 'I_d),
    (paper_main_point x i a 0 * paper_main_point x i b 0) ^+ 2 <= d%:R.
Proof.
move=> Hx i a b.
have Hb : forall a' : 'I_d, (Rabs (paper_main_point x i a' ord0) < sqrt (sqrt (INR d)))%Rcoq.
  by move=> a'; apply: Rnot_le_lt => H; apply: Hx; exists i, a'.
have Hs0 : (0 <= sqrt (INR d))%Rcoq by apply: sqrt_pos.
have Hsq : forall a' : 'I_d, (paper_main_point x i a' ord0 ^ 2 <= sqrt (INR d))%Rcoq.
  move=> a'; have H := Hb a'.
  have H0 := Rabs_pos (paper_main_point x i a' ord0).
  rewrite -pow2_abs -(sqrt_sqrt (sqrt (INR d)) Hs0).
  have H1 := Rmult_le_compat _ _ _ _ H0 H0 (Rlt_le _ _ H) (Rlt_le _ _ H).
  by rewrite /= Rmult_1_r.
apply/RleP; rewrite -RpowE -INRE -RmultE Rpow_mult_distr.
rewrite -(sqrt_sqrt (INR d) (pos_INR d)).
apply: Rmult_le_compat; [exact: pow2_ge_0 | exact: pow2_ge_0 | exact: Hsq a | exact: Hsq b].
Qed.

Lemma pmccfe_gram N d (c : R) (x : paper_main_sample N d) :
  0 < c -> (0 < d)%N -> (N <= d ^ 2)%N -> c * d%:R ^+ 2 <= N%:R ->
  ~ paper_main_feature_upper_event N d x ->
  forall u : 'cV[R]_N,
    (u^T *m (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) *m u) 0 0 <=
    109 / c * N%:R * (u^T *m u) 0 0.
Proof.
move=> Hc Hd HNd HcN Hx u.
have HG := paper_main_feature_upper_event_bound N d x Hd Hx.
have HV := paper_main_squarefree_gram_le N d x.
have HNR : N%:R <= d%:R ^+ 2 :> R by rewrite -natrX ler_nat.
have H109 : 109 * d%:R ^+ 2 <= 109 / c * N%:R.
  have H109c : 0 <= 109 / c by rewrite divr_ge0 // ltW.
  have := ler_wpM2l H109c HcN.
  by rewrite mulrA divfK ?gt_eqF.
have HK : 3 * N%:R + 106%:R * d%:R ^+ 2 <= 109 / c * N%:R by lra.
have HL : paper_main_loewner_le
    (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T)
    ((109 / c * N%:R) *: 1%:M).
  apply: pmh_loewner_trans HV _; apply: pmh_loewner_trans HG _; exact: pmh_loewner_scalar.
have := HL.2 u.
rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE.
lra.
Qed.

Lemma pmccfe_diagonal N d (delta : R) (x : paper_main_sample N d) :
  ~ paper_main_squarefree_diag_event N d (delta / 4)%R x ->
  forall i : 'I_N,
    `|(paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) i i /
      d%:R ^+ 2 - 1| <= delta / 4.
Proof.
move=> Hx i.
have H : ~ Rlt (delta / 4)%R (Rabs ((paper_main_squarefree_block N d x *m
    (paper_main_squarefree_block N d x)^T)%R i i / INR d ^ 2 - 1)).
  by move=> H; apply: Hx; exists i.
have := Rnot_lt_le _ _ H; move/RleP.
by rewrite RminusE RdivE RpowE INRE.
Qed.

Theorem paper_main_column_frame_raw N d (c delta : R) (x : paper_main_sample N d) :
  0 < c -> 0 < delta -> (0 < d)%N -> (0 < N)%N -> (N <= d ^ 2)%N -> c * d%:R ^+ 2 <= N%:R ->
  ~ paper_main_column_frame_event N d delta x ->
  [/\ forall a b : 'I_d, (a < b)%N ->
        paper_main_column_q N d x a b <= 2 * N%:R /\
        `|paper_main_column_q N d x a b / N%:R - 1| <= delta,
      forall (i : 'I_N) (a b : 'I_d),
        (paper_main_point x i a 0 * paper_main_point x i b 0) ^+ 2 <= d%:R,
      forall u : 'cV[R]_N,
        (u^T *m (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) *m u)
          0 0 <= 109 / c * N%:R * (u^T *m u) 0 0
    & forall i : 'I_N,
        `|(paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T) i i /
          d%:R ^+ 2 - 1| <= delta / 4].
Proof.
move=> Hc Hdelta Hd HN HNd HcN Hx.
have HxA : ~ paper_main_column_event N d (Num.min delta 1)%R x.
  by move=> H; apply: Hx; left; left; left.
have HxB : ~ paper_main_feature_upper_event N d x by move=> H; apply: Hx; left; left; right.
have HxC : ~ paper_main_data_coordinate_event N d (sqrt (sqrt (INR d))) x.
  by move=> H; apply: Hx; left; right.
have HxD : ~ paper_main_squarefree_diag_event N d (delta / 4)%R x by move=> H; apply: Hx; right.
split.
- exact: pmccfe_columns.
- exact: pmccfe_coordinates.
- exact: pmccfe_gram.
- exact: pmccfe_diagonal.
Qed.
