(* Growth of the raw and clipped data-feature scores. Deterministic.

   Let d = S n, N rows, D = N * d and S(xs) = sum_(l < D) (nth l xs 0)^2.
   W f = (f f^T - I) / sqrt d is the data feature of the coordinates f
   (paper_main_data_feature). Let B be a d x d matrix of operator norm at
   most k (matrix_operator_norm of paper_main_matrix_from_public n B; the
   score bounds do not need B symmetric) and y a dual vector with
   euclidean_norm y (seq 0 N) <= 1.
   - pmdcg_trace_bound and pmdcg_pairing_bound: |tr B| <= d k and
     |<W f, B>| <= k (|f|^2 + d) / sqrt d.
   - paper_main_data_raw_score_growth and
     paper_main_data_clipped_score_growth: the raw score
     sum_i y_i <W (row i of xs), B> and the clipped score (U >= 0) are at
     most (k / sqrt d) (S(xs) + D) in absolute value. Both are instances of
     paper_main_data_contraction_score_growth, for a coordinate map phi with
     |phi z| <= |z|.
   - paper_main_data_raw_soft_growth and paper_main_data_clipped_soft_growth:
     for admissible families over nonempty Y and Q, the soft minimax of the
     raw or clipped scores is at most (k / sqrt d) (S(xs) + D) + C in
     absolute value, with C = ln (length Y) / beta + ln (length Q) / gamma
     (paper_main_data_soft_entropy).
   N = 0 is allowed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval boolp.
From mathcomp Require Import classical_sets functions reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums
  MatrixDefinitions OperatorDefinitions PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature
  PaperMainGeometryHeadCoefficients PaperMainGordonLipschitz
  PaperMainGordonProcessCovariance PaperMainGordonGrowth PaperMainGaussianLipschitzClip
  PaperMainSymmetricBilinear PaperMainMatrixTransport PaperMainMatrixDuality
  PaperMainDataFeatureMoments PaperMainDataHeadOperator PaperMainDataClippedScore
  PaperMainDataClipped PaperMainDataClippedSoft.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Open Scope R_scope.

(* 1. Unit vectors, diagonal entries and the trace. *)
Lemma pmdcg_unit_norm n (i : 'I_(S n)) : pmdc_norm (delta_mx i ord0 : 'cV[R]_(S n)) = 1.
Proof.
rewrite /pmdc_norm trmx_delta mul_delta_mx mxE !eqxx /=.
exact: sqrt_1.
Qed.

Lemma pmdcg_diag n (B : 'M[R]_(S n)) (i : 'I_(S n)) :
  (((delta_mx i ord0 : 'cV[R]_(S n))^T *m (B *m (delta_mx i ord0 : 'cV[R]_(S n)))) ord0 ord0)%R =
  B i i.
Proof. by rewrite trmx_delta mulmxA -rowE -colE !mxE. Qed.

Lemma pmdcg_diag_bound n (B : 'M[R]_(S n)) k (i : 'I_(S n)) :
  0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  Rabs (B i i) <= k.
Proof.
move=> Hk HA; rewrite -pmdcg_diag.
apply: Rle_trans (pmdc_dot_bound _ _) _.
have H := pmdc_action_norm n B k (delta_mx i ord0) Hk HA.
rewrite pmdcg_unit_norm in H *.
lra.
Qed.

Lemma pmdcg_trace_bound n (B : 'M[R]_(S n)) k :
  0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  Rabs (paper_main_trace B) <= INR (S n) * k.
Proof.
move=> Hk HA.
have E : paper_main_trace B =
    finite_sum (fun j => B (inord j) (inord j)) (List.seq 0 (S n)).
  rewrite paper_main_finite_sum_public /paper_main_trace.
  by apply: eq_bigr => i _; rewrite inord_val.
rewrite E.
have := finite_sum_bound (fun j => B (inord j) (inord j)) (List.seq 0 (S n)) k.
rewrite List.length_seq; apply => j _; exact: pmdcg_diag_bound.
Qed.

(* 2. The quadratic form and one row. *)
Lemma pmdcg_quad_bound n (B : 'M[R]_(S n)) k (c : 'cV[R]_(S n)) :
  0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  Rabs ((c^T *m B *m c)%R ord0 ord0) <= k * ((c^T *m c)%R ord0 ord0).
Proof.
move=> Hk HA; rewrite -mulmxA.
apply: Rle_trans (pmdc_dot_bound _ _) _.
have H := pmdc_action_norm n B k c Hk HA.
have H0 := pmdc_norm_ge0 c.
have Hc : 0 <= (c^T *m c)%R ord0 ord0 by apply/RleP; exact: pmh_vec_sqr_ge0.
have Hsq : pmdc_norm c * pmdc_norm c = (c^T *m c)%R ord0 ord0 by exact: sqrt_sqrt.
nra.
Qed.

Lemma pmdcg_pairing_eq n (f : nat -> R) (B : 'M[R]_(S n)) :
  paper_main_pairing (paper_main_data_feature n f) B =
  / sqrt (INR (S n)) *
    ((((paper_main_symmetric_column n f)^T *m B *m paper_main_symmetric_column n f)%R
      ord0 ord0) - paper_main_trace B).
Proof.
have Hs : Num.sqrt ((S n)%:R : R) = sqrt (INR (S n)) by rewrite RsqrtE INRE.
rewrite /paper_main_data_feature pmh_pairingZl pmh_pairingBl pmh_pairing_id.
rewrite [paper_main_pairing (_ *m _)%R B]paper_main_pairingC pmsb_pairing_outer.
by rewrite Hs RinvE.
Qed.

Lemma pmdcg_pairing_bound n (f : nat -> R) (B : 'M[R]_(S n)) k :
  0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  Rabs (paper_main_pairing (paper_main_data_feature n f) B) <=
    k / sqrt (INR (S n)) * (paper_main_gordon_dot (S n) f f + INR (S n)).
Proof.
move=> Hk HA.
have Hsp : 0 < sqrt (INR (S n)) by apply: sqrt_lt_R0; apply: lt_0_INR; lia.
have Hi : 0 < / sqrt (INR (S n)) by exact: Rinv_0_lt_compat.
have Hq := pmdcg_quad_bound n B k (paper_main_symmetric_column n f) Hk HA.
rewrite paper_main_symmetric_column_norm in Hq.
have Ht := pmdcg_trace_bound n B k Hk HA.
rewrite pmdcg_pairing_eq Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ Hi)).
set q := ((_ ^T *m B *m _)%R ord0 ord0) in Hq *.
set t := paper_main_trace B in Ht *.
have Htr : Rabs (q - t) <= Rabs q + Rabs t.
  by rewrite /Rminus; apply: Rle_trans (Rabs_triang _ _) _; rewrite Rabs_Ropp; exact: Rle_refl.
apply: Rle_trans (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Hi) Htr) _.
rewrite /Rdiv; set s := / sqrt (INR (S n)) in Hi *.
set G := paper_main_gordon_dot (S n) f f in Hq *.
nra.
Qed.

(* 3. Score growth for coordinate maps with |phi z| <= |z|. *)
Lemma pmdcg_dual_squared N (y : nat -> R) :
  euclidean_norm y (List.seq 0 N) <= 1 -> squared_norm y (List.seq 0 N) <= 1.
Proof.
move=> Hy.
have Hsy : 0 <= squared_norm y (List.seq 0 N).
  by apply: finite_sum_nonneg => j _; exact: pow2_ge_0.
have Hsq := pow2_sqrt _ Hsy.
have Hs0 := sqrt_pos (squared_norm y (List.seq 0 N)).
move: Hy; rewrite /euclidean_norm => Hy; nra.
Qed.

Lemma pmdcg_dual_entry N (y : nat -> R) i :
  euclidean_norm y (List.seq 0 N) <= 1 -> In i (List.seq 0 N) -> Rabs (y i) <= 1.
Proof.
move=> Hy Hi.
have Hy2 := pmdcg_dual_squared N y Hy.
have Hm := finite_sum_member (fun j => y j ^ 2) (List.seq 0 N) i
  (fun j _ => pow2_ge_0 (y j)) Hi.
have H1 : Rabs (y i) ^ 2 <= 1 by rewrite pow2_abs; rewrite /squared_norm in Hy2; lra.
have := Rabs_pos (y i); nra.
Qed.

Lemma pmdcg_row_dot_le phi n i xs :
  (forall z, Rabs (phi z) <= Rabs z) ->
  paper_main_gordon_dot (S n) (pmdc_row phi n i xs) (pmdc_row phi n i xs) <=
  finite_sum (fun j => List.nth (i * S n + j)%N xs 0 ^ 2) (List.seq 0 (S n)).
Proof.
move=> Hphi; rewrite /paper_main_gordon_dot; apply: finite_sum_le => j _.
rewrite /pmdc_row; set z := List.nth _ xs 0.
have := Rsqr_le_abs_1 _ _ (Hphi z); rewrite /Rsqr; nra.
Qed.

Lemma pmdcg_blocks_sum n N xs :
  finite_sum (fun i => finite_sum (fun j => List.nth (i * S n + j)%N xs 0 ^ 2)
    (List.seq 0 (S n)) + INR (S n)) (List.seq 0 N) =
  finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 (N * S n)) + INR (N * S n).
Proof.
rewrite finite_sum_plus finite_sum_const List.length_seq.
rewrite (pmdo_sum_blocks N (S n) (fun l => List.nth l xs 0 ^ 2)).
by rewrite -multE mult_INR.
Qed.

Theorem paper_main_data_contraction_score_growth phi n N (B : 'M[R]_(S n))
    (y : nat -> R) k xs :
  (forall z, Rabs (phi z) <= Rabs z) -> 0 <= k ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  euclidean_norm y (List.seq 0 N) <= 1 ->
  Rabs (pmdc_score phi n N B y xs) <=
    k / sqrt (INR (S n)) *
      (finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 (N * S n)) + INR (N * S n)).
Proof.
move=> Hphi Hk HA Hy.
have Hsp : 0 < sqrt (INR (S n)) by apply: sqrt_lt_R0; apply: lt_0_INR; lia.
have Hks : 0 <= k / sqrt (INR (S n)).
  by apply: Rmult_le_pos => //; apply: Rlt_le; exact: Rinv_0_lt_compat.
rewrite /pmdc_score -pmdcg_blocks_sum -finite_sum_scale.
apply: Rle_trans (finite_sum_abs_le _ _) _.
apply: finite_sum_le => i Hi; rewrite Rabs_mult.
have Hyi := pmdcg_dual_entry N y i Hy Hi.
have Hp := pmdcg_pairing_bound n (pmdc_row phi n i xs) B k Hk HA.
have Hr := pmdcg_row_dot_le phi n i xs Hphi.
have H0 := Rabs_pos (y i).
move: Hp; set p := Rabs _ => Hp.
have H1 : 0 <= p by exact: Rabs_pos.
move: Hr Hp; set G := paper_main_gordon_dot _ _ _; set Rr := finite_sum _ _ => Hr Hp.
set c := k / sqrt (INR (S n)) in Hks Hp *.
nra.
Qed.

(* The raw score of a list, and its growth. *)
Definition paper_main_data_raw_score n N (B : 'M[R]_(S n)) (y : nat -> R)
    (xs : list R) : R :=
  finite_sum (fun i => y i * paper_main_pairing
    (paper_main_data_feature n (fun j => List.nth (i * S n + j)%N xs 0)) B)
    (List.seq 0 N).

Lemma pmdcg_raw_generic n N B y xs :
  paper_main_data_raw_score n N B y xs = pmdc_score (fun z => z) n N B y xs.
Proof. by []. Qed.

Theorem paper_main_data_raw_score_growth n N (B : 'M[R]_(S n)) (y : nat -> R) k xs :
  0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  euclidean_norm y (List.seq 0 N) <= 1 ->
  Rabs (paper_main_data_raw_score n N B y xs) <=
    k / sqrt (INR (S n)) *
      (finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 (N * S n)) + INR (N * S n)).
Proof.
move=> Hk HA Hy; rewrite pmdcg_raw_generic.
by apply: paper_main_data_contraction_score_growth => // z; exact: Rle_refl.
Qed.

Lemma pmdcg_clip_abs_le U z : 0 <= U -> Rabs (paper_main_gaussian_clip U z) <= Rabs z.
Proof.
move=> HU; unfold paper_main_gaussian_clip, Rmax, Rmin.
destruct (Rle_dec U z) as [h1|h1]; destruct (Rle_dec (- U) _) as [h2|h2];
  repeat match goal with H : ~ (_ <= _) |- _ => apply Rnot_le_lt in H end;
  unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.

Theorem paper_main_data_clipped_score_growth U n N (B : 'M[R]_(S n)) (y : nat -> R) k xs :
  0 <= U -> 0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  euclidean_norm y (List.seq 0 N) <= 1 ->
  Rabs (paper_main_data_clipped_score U n N B y xs) <=
    k / sqrt (INR (S n)) *
      (finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 (N * S n)) + INR (N * S n)).
Proof.
move=> HU Hk HA Hy; rewrite pmdcl_score_generic.
by apply: paper_main_data_contraction_score_growth => // z; exact: pmdcg_clip_abs_le.
Qed.

(* 4. Soft minimax of score families. *)
Definition paper_main_data_soft_entropy beta gamma (Y Q : list nat) : R :=
  ln (INR (length Y)) / beta + ln (INR (length Q)) / gamma.

Lemma pmdcg_ln_length_ge0 (I : list nat) : I <> [] -> 0 <= ln (INR (length I)).
Proof.
move=> HI.
have H1 : 1 <= INR (length I).
  case: I HI => [|i I] HI; first by case: (HI erefl).
  change (1 <= INR (S (length I))); rewrite S_INR; have := pos_INR (length I); lra.
case: (Rle_lt_or_eq_dec _ _ H1) => [Hlt | <-]; last by rewrite ln_1; exact: Rle_refl.
by left; rewrite -ln_1; apply: ln_increasing; lra.
Qed.

Lemma paper_main_data_soft_entropy_ge0 beta gamma Y Q :
  0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  0 <= paper_main_data_soft_entropy beta gamma Y Q.
Proof.
move=> Hb Hg HY HQ; rewrite /paper_main_data_soft_entropy.
have H1 := pmdcg_ln_length_ge0 Y HY; have H2 := pmdcg_ln_length_ge0 Q HQ.
apply: Rplus_le_le_0_compat; apply: Rmult_le_pos => //; apply: Rlt_le;
  exact: Rinv_0_lt_compat.
Qed.

Lemma paper_main_data_soft_value_bound beta gamma H Y Q T :
  0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  (forall z q, In z Y -> In q Q -> Rabs (H z q) <= T) ->
  Rabs (soft_minimax beta gamma H Y Q) <= T + paper_main_data_soft_entropy beta gamma Y Q.
Proof.
move=> Hb Hg HY HQ HT.
have H0 := paper_main_gordon_soft_value_bound beta gamma H Y Q T Hb Hg HY HQ HT.
have H1 := pmdcg_ln_length_ge0 Y HY; have H2 := pmdcg_ln_length_ge0 Q HQ.
have H3 : 0 <= ln (INR (length Y)) / beta.
  by apply: Rmult_le_pos => //; apply: Rlt_le; exact: Rinv_0_lt_compat.
have H4 : 0 <= ln (INR (length Q)) / gamma.
  by apply: Rmult_le_pos => //; apply: Rlt_le; exact: Rinv_0_lt_compat.
rewrite (Rabs_pos_eq _ H3) (Rabs_pos_eq _ H4) in H0.
rewrite /paper_main_data_soft_entropy; lra.
Qed.

Definition paper_main_data_raw_family n N (Bf : nat -> nat -> 'M[R]_(S n))
    (yf : nat -> nat -> nat -> R) (xs : list R) : nat -> nat -> R :=
  fun z q => paper_main_data_raw_score n N (Bf z q) (yf z q) xs.

Theorem paper_main_data_raw_soft_growth n N k beta gamma Bf yf Y Q xs :
  0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  Rabs (soft_minimax beta gamma (paper_main_data_raw_family n N Bf yf xs) Y Q) <=
    k / sqrt (INR (S n)) *
      (finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 (N * S n)) + INR (N * S n)) +
    paper_main_data_soft_entropy beta gamma Y Q.
Proof.
move=> Hk Hb Hg HY HQ Had.
apply: paper_main_data_soft_value_bound => // z q Hz Hq.
have [_ [HA Hy]] := Had z q Hz Hq.
exact: paper_main_data_raw_score_growth.
Qed.

Theorem paper_main_data_clipped_soft_growth U n N k beta gamma Bf yf Y Q xs :
  0 <= U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  Rabs (soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf xs) Y Q) <=
    k / sqrt (INR (S n)) *
      (finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 (N * S n)) + INR (N * S n)) +
    paper_main_data_soft_entropy beta gamma Y Q.
Proof.
move=> HU Hk Hb Hg HY HQ Had.
apply: paper_main_data_soft_value_bound => // z q Hz Hq.
have [_ [HA Hy]] := Had z q Hz Hq.
exact: paper_main_data_clipped_score_growth.
Qed.

(* 5. Squares. *)
Lemma paper_main_data_square_bound a T C :
  0 <= T -> 0 <= C -> Rabs a <= T + C -> a * a <= 2 * (T * T) + 2 * (C * C).
Proof.
move=> HT HC Ha.
have E : a * a = Rabs a * Rabs a by have := Rsqr_abs a; rewrite /Rsqr.
have H0 := Rabs_pos a.
have H1 : Rabs a * Rabs a <= (T + C) * (T + C) by apply: Rmult_le_compat.
have H2 := pow2_ge_0 (T - C).
rewrite E; nra.
Qed.
