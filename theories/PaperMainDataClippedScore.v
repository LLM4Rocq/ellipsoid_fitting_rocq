(* Globally Lipschitz scores of clipped quadratic data features, for any
   coordinate map phi with |phi z| <= U and |phi z - phi w| <= |z - w|.

   d = S n, and the sample is a list xs of N rows of length d. Row i of the
   clipped sample is pmdc_row phi n i xs = (phi (nth (i * d + j) xs 0))_j,
   and its feature is paper_main_data_feature n (pmdc_row phi n i xs).
   - Operator bound. matrix_operator_norm n (paper_main_matrix_from_public n B)
     <= k gives |B v|^2 <= k^2 |v|^2 for public v (pmdc_public_action_sqr),
     the converse direction of PaperMainMatrixOperatorTransport.
   - Rows. A clipped row has |row|^2 <= d U^2 (pmdc_row_norm). Clipped row
     differences are at most raw row differences (pmdc_row_dist). The
     squared row distances add up to the full squared list distance
     paper_main_gordon_distance (N * d) (pmdc_dist_blocks).
   - Score (paper_main_data_contraction_score_lipschitz). For symmetric B with
     internal operator norm <= k and a dual vector y with
     euclidean_norm y (seq 0 N) <= 1, the score
       sum_(i < N) y_i <W(row_i xs), B>
     is 2 k U-Lipschitz in paper_main_gordon_distance (N * d). There is no
     sqrt N factor. Proof: <W(f), B> - <W(g), B> =
     ((col f)^T B (col f) - (col g)^T B (col g)) / sqrt d, since the
     centering cancels. Then (c - c')^T B (c + c') <= k |c - c'| (|c| + |c'|)
     <= 2 k U sqrt d |c - c'|, and Cauchy-Schwarz over the rows.
   No length hypothesis is needed: only indices below N * d are read.
   PaperMainDataClipped takes phi to be the checked clip.
   Nothing from the paper is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums MatrixDefinitions
  MatrixCoordinates OperatorDefinitions OperatorBounds PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryGram PaperMainGeometryHomogeneous
  PaperMainGeometrySeparation PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFeature PaperMainMatrixTransport PaperMainMatrixDuality
  PaperMainGordonProcessCovariance PaperMainGordonLipschitz
  PaperMainGaussianFeatureCoordinates PaperMainSymmetricBilinear
  PaperMainConeConditionOperator PaperMainDataFeatureMomentsCoordinates
  PaperMainDataFeatureMoments PaperMainDataHeadOperator PaperMainMatrixOperatorTransport
  PaperMainSymmetricOperatorNet.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

(* 1. From the internal operator norm to public vectors. *)
Lemma pmdc_action_bound n (A : matrix n) (k : R) (x : vector n) :
  matrix_operator_norm n A <= k -> (`|matrix_action n A x|)%R <= k * (`|x|)%R.
Proof.
move=> Hk.
have [Hlin _] := matrix_action_linear n A.
have [Hub _] := matrix_operator_norm_lub n A.
have Hlin0 : matrix_action n A 0%R = 0%R.
  by have := Hlin (-1)%R 0%R 0%R; rewrite scaler0 addr0 scaleN1r addNr.
have HlinZ : forall (c : R) (z : vector n), matrix_action n A (c *: z)%R = (c *: matrix_action n A z)%R.
  by move=> c z; have := Hlin c z 0%R; rewrite !addr0 Hlin0 addr0.
case: (eqVneq x 0%R) => [->|Hx].
  by rewrite Hlin0 !normr0 Rmult_0_r; exact: Rle_refl.
have Hxp : (0 < `|x|)%R by rewrite normr_gt0.
set x' := ((`|x|)^-1 *: x)%R.
have Hx' : (`|x'| = 1)%R.
  by rewrite /x' normrZ ger0_norm ?invr_ge0 ?ltW // mulVf // lt0r_neq0.
have H1 : (`|matrix_action n A x'|)%R <= matrix_operator_norm n A.
  apply: Hub; exists x'; split => //; rewrite Hx'; exact: Rle_refl.
rewrite /x' HlinZ normrZ ger0_norm ?invr_ge0 ?ltW // in H1.
have H2 := Rle_trans _ _ _ H1 Hk.
have Hx0 : 0 <= (`|x|)%R by apply/RleP; exact: normr_ge0.
have := Rmult_le_compat_l _ _ _ Hx0 H2.
by rewrite RmultE mulrA (mulfV (lt0r_neq0 Hxp)) mul1r Rmult_comm.
Qed.

(* The internal vector of a public column. *)
Definition pmdc_internal n (v : 'cV[R]_(S n)) : vector n :=
  tuple_build R^o n (fun i => v (inord i) ord0).

Lemma pmdc_column_internal n (v : 'cV[R]_(S n)) : pmmo_column n (pmdc_internal n v) = v.
Proof.
apply/matrixP => i j; rewrite [j]ord1 !mxE /pmdc_internal /vector_entry.
have Hi : (i <= n)%coq_nat by have /ssrnat.ltP := ltn_ord i; lia.
by rewrite (tuple_entry_build _ _ _ _ Hi) inord_val.
Qed.

Lemma pmdc_public_action_sqr n (B : 'M[R]_(S n)) (k : R) (v : 'cV[R]_(S n)) :
  0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  (((B *m v)^T *m (B *m v)) ord0 ord0)%R <= k ^ 2 * ((v^T *m v) ord0 ord0)%R.
Proof.
move=> Hk HA.
have Hv := pmdc_column_internal n v.
set x := pmdc_internal n v in Hv.
have H := pmdc_action_bound _ _ _ x HA.
have E1 : (((B *m v)^T *m (B *m v)) ord0 ord0)%R =
    (`|matrix_action n (paper_main_matrix_from_public n B) x| ^+ 2)%R.
  by rewrite -Hv -pmmo_column_action pmmo_column_norm.
have E2 : ((v^T *m v) ord0 ord0)%R = (`|x| ^+ 2)%R by rewrite -Hv pmmo_column_norm.
rewrite E1 E2.
have H0 : 0 <= (`|matrix_action n (paper_main_matrix_from_public n B) x|)%R.
  by apply/RleP; exact: normr_ge0.
have Hx0 : 0 <= (`|x|)%R by apply/RleP; exact: normr_ge0.
rewrite -!RpowE; nra.
Qed.

(* 2. Public norms with the Stdlib square root. *)
Definition pmdc_norm {d : nat} (v : 'cV[R]_d) : R := sqrt ((v^T *m v)%R ord0 ord0).

Lemma pmdc_norm_ge0 {d : nat} (v : 'cV[R]_d) : 0 <= pmdc_norm v.
Proof. exact: sqrt_pos. Qed.

Lemma pmdc_dot_bound {d : nat} (u w : 'cV[R]_d) :
  Rabs ((u^T *m w)%R ord0 ord0) <= pmdc_norm u * pmdc_norm w.
Proof.
have CS := pmco_vec_cauchy_schwarz _ u w.
have Hu : 0 <= (u^T *m u)%R ord0 ord0 by apply/RleP; exact: pmh_vec_sqr_ge0.
have Hw : 0 <= (w^T *m w)%R ord0 ord0 by apply/RleP; exact: pmh_vec_sqr_ge0.
rewrite /pmdc_norm -sqrt_mult // -(sqrt_Rsqr_abs ((u^T *m w)%R ord0 ord0)).
by apply: sqrt_le_1_alt; rewrite /Rsqr; apply/RleP; rewrite !RmultE -expr2.
Qed.

Lemma pmdc_action_norm n (B : 'M[R]_(S n)) (k : R) (w : 'cV[R]_(S n)) :
  0 <= k -> matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  pmdc_norm (B *m w)%R <= k * pmdc_norm w.
Proof.
move=> Hk HA; have H := pmdc_public_action_sqr n B k w Hk HA.
have Hw : 0 <= (w^T *m w)%R ord0 ord0 by apply/RleP; exact: pmh_vec_sqr_ge0.
rewrite /pmdc_norm -(sqrt_pow2 k Hk) -(sqrt_mult _ _ (pow2_ge_0 k) Hw).
exact: (sqrt_le_1_alt _ _ H).
Qed.

(* 3. A quadratic difference for symmetric B. *)
Lemma pmdc_quad_diff n (B : 'M[R]_(S n)) (k : R) (c c' : 'cV[R]_(S n)) :
  paper_main_symmetric B -> 0 <= k ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  Rabs ((c^T *m B *m c)%R ord0 ord0 - (c'^T *m B *m c')%R ord0 ord0) <=
    k * pmdc_norm (c - c')%R * (pmdc_norm c + pmdc_norm c').
Proof.
move=> HB Hk HA; have HBt : (B^T)%R = B by exact/paper_main_symmetricP.
have E : ((c^T *m B *m c) 0 0 - (c'^T *m B *m c') 0 0 =
    ((c - c')^T *m (B *m c)) 0 0 + ((c - c')^T *m (B *m c')) 0 0)%R.
  rewrite !mulmxA pmon_bilinear_sub_l pmon_bilinear_sub_l.
  by rewrite (paper_main_cross_sym _ B c c' HBt) addrA subrK.
have -> : (c^T *m B *m c)%R ord0 ord0 - (c'^T *m B *m c')%R ord0 ord0 =
    ((c - c')^T *m (B *m c))%R ord0 ord0 + ((c - c')^T *m (B *m c'))%R ord0 ord0.
  exact: E.
apply: Rle_trans (Rabs_triang _ _) _.
have H1 := pmdc_dot_bound (c - c')%R (B *m c)%R.
have H2 := pmdc_dot_bound (c - c')%R (B *m c')%R.
have H3 := pmdc_action_norm n B k c Hk HA.
have H4 := pmdc_action_norm n B k c' Hk HA.
have H0 := pmdc_norm_ge0 (c - c')%R.
have Hc0 := pmdc_norm_ge0 c; have Hc0' := pmdc_norm_ge0 c'.
apply: Rle_trans (Rplus_le_compat _ _ _ _ H1 H2) _.
nra.
Qed.

(* 4. Clipped rows. *)
Definition pmdc_row (phi : R -> R) n (i : nat) (xs : list R) : nat -> R :=
  fun j => phi (List.nth (i * S n + j)%N xs 0).

Definition pmdc_col (phi : R -> R) n (i : nat) (xs : list R) : 'cV[R]_(S n) :=
  paper_main_symmetric_column n (pmdc_row phi n i xs).

Lemma pmdc_row_norm phi U n i xs :
  (forall z, Rabs (phi z) <= U) -> pmdc_norm (pmdc_col phi n i xs) <= U * sqrt (INR (S n)).
Proof.
move=> Hphi.
have HU : 0 <= U by apply: Rle_trans (Rabs_pos (phi 0)) (Hphi 0).
rewrite /pmdc_norm /pmdc_col paper_main_symmetric_column_norm.
rewrite -(sqrt_pow2 U HU) -(sqrt_mult _ _ (pow2_ge_0 U) (pos_INR (S n))).
apply: sqrt_le_1_alt; rewrite /paper_main_gordon_dot.
apply: Rle_trans (finite_sum_le _ (fun _ => U ^ 2) _ _) _.
  move=> j _; have H := Hphi (List.nth (i * S n + j)%N xs 0).
  have := Rabs_pos (phi (List.nth (i * S n + j)%N xs 0)).
  rewrite /pmdc_row; move: H; set z := phi _ => H H0.
  have := Rsqr_le_abs_1 z U; rewrite (Rabs_pos_eq U HU) /Rsqr => Hz.
  by have := Hz H; nra.
by rewrite finite_sum_const List.length_seq; right; ring.
Qed.

Lemma pmdc_row_dist phi n i xs ys :
  (forall z w, Rabs (phi z - phi w) <= Rabs (z - w)) ->
  pmdc_norm (pmdc_col phi n i xs - pmdc_col phi n i ys)%R <=
  sqrt (finite_sum (fun j => (List.nth (i * S n + j)%N xs 0 -
    List.nth (i * S n + j)%N ys 0) ^ 2) (List.seq 0 (S n))).
Proof.
move=> Hl.
rewrite /pmdc_norm /pmdc_col -pmon_column_sub paper_main_symmetric_column_norm.
apply: sqrt_le_1_alt; rewrite /paper_main_gordon_dot.
apply: finite_sum_le => j _; rewrite /pmdc_row.
set a := List.nth (i * S n + j)%N xs 0; set b := List.nth (i * S n + j)%N ys 0.
have := Rsqr_le_abs_1 _ _ (Hl a b); rewrite /Rsqr; nra.
Qed.

Lemma pmdc_dist_blocks N d (xs ys : list R) :
  finite_sum (fun i => finite_sum (fun j => (List.nth (i * d + j)%N xs 0 -
    List.nth (i * d + j)%N ys 0) ^ 2) (List.seq 0 d)) (List.seq 0 N) =
  paper_main_gordon_distance (N * d) xs ys ^ 2.
Proof.
have H0 : 0 <= finite_sum (fun l => (List.nth l xs 0 - List.nth l ys 0) ^ 2)
    (List.seq 0 (N * d)).
  by apply: finite_sum_nonneg => l _; exact: pow2_ge_0.
rewrite /paper_main_gordon_distance (pow2_sqrt _ H0).
by rewrite (pmdo_sum_blocks N d (fun l => (List.nth l xs 0 - List.nth l ys 0) ^ 2)).
Qed.

(* The pairing of two features differs by the quadratic difference over sqrt d. *)
Lemma pmdc_pairing_diff n (f g : nat -> R) (B : 'M[R]_(S n)) :
  (paper_main_pairing (paper_main_data_feature n f) B -
   paper_main_pairing (paper_main_data_feature n g) B =
   (Num.sqrt (S n)%:R)^-1 *
   (((paper_main_symmetric_column n f)^T *m B *m paper_main_symmetric_column n f) 0 0 -
    ((paper_main_symmetric_column n g)^T *m B *m paper_main_symmetric_column n g) 0 0))%R.
Proof.
rewrite /paper_main_data_feature !pmh_pairingZl !pmh_pairingBl.
rewrite ![paper_main_pairing (_ *m _)%R B]paper_main_pairingC !pmsb_pairing_outer.
by rewrite -mulrBr opprB addrA subrK.
Qed.

(* 5. The score and its Lipschitz bound. *)
Definition pmdc_score (phi : R -> R) n N (B : 'M[R]_(S n)) (y : nat -> R)
    (xs : list R) : R :=
  finite_sum (fun i => y i * paper_main_pairing
    (paper_main_data_feature n (pmdc_row phi n i xs)) B) (List.seq 0 N).

Lemma pmdc_row_arith k U q e r1 r2 D s :
  0 <= k -> 0 < s -> 0 <= e -> e <= D -> 0 <= r1 -> 0 <= r2 ->
  r1 <= U * s -> r2 <= U * s -> q <= k * e * (r1 + r2) -> / s * q <= 2 * k * U * D.
Proof.
move=> Hk Hs He HeD Hr1 Hr2 H1 H2 Hq.
have Hi : 0 < / s by apply: Rinv_0_lt_compat.
have Hb : q <= k * D * (2 * U * s).
  apply: Rle_trans Hq _.
  apply: Rmult_le_compat.
  - exact: Rmult_le_pos.
  - lra.
  - exact: Rmult_le_compat_l.
  - lra.
apply: Rle_trans (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Hi) Hb) _.
right.
have -> : / s * (k * D * (2 * U * s)) = 2 * k * U * D * (/ s * s) by ring.
by rewrite (Rinv_l _ (Rgt_not_eq _ _ Hs)) Rmult_1_r.
Qed.

(* The full score is 2kU-Lipschitz in the Euclidean distance of all N * d
   coordinates, for every dual vector y of norm at most 1. *)
Theorem paper_main_data_contraction_score_lipschitz phi U n N (B : 'M[R]_(S n))
    (y : nat -> R) k xs ys :
  (forall z, Rabs (phi z) <= U) ->
  (forall z w, Rabs (phi z - phi w) <= Rabs (z - w)) ->
  paper_main_symmetric B -> 0 <= k ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  euclidean_norm y (List.seq 0 N) <= 1 ->
  Rabs (pmdc_score phi n N B y xs - pmdc_score phi n N B y ys) <=
    2 * k * U * paper_main_gordon_distance (N * S n) xs ys.
Proof.
move=> Hb Hl HB Hk HA Hy.
have HU : 0 <= U by apply: Rle_trans (Rabs_pos (phi 0)) (Hb 0).
pose D := fun i => sqrt (finite_sum (fun j => (List.nth (i * S n + j)%N xs 0 -
  List.nth (i * S n + j)%N ys 0) ^ 2) (List.seq 0 (S n))).
have HD0 : forall i, 0 <= D i by move=> i; exact: sqrt_pos.
have Hs : Num.sqrt ((S n)%:R : R) = sqrt (INR (S n)) by rewrite RsqrtE INRE.
have Hsp : 0 < sqrt (INR (S n)) by apply: sqrt_lt_R0; apply: lt_0_INR; lia.
have Hrow : forall i, Rabs (paper_main_pairing (paper_main_data_feature n (pmdc_row phi n i xs)) B -
    paper_main_pairing (paper_main_data_feature n (pmdc_row phi n i ys)) B) <=
    2 * k * U * D i.
  move=> i.
  have -> : paper_main_pairing (paper_main_data_feature n (pmdc_row phi n i xs)) B -
      paper_main_pairing (paper_main_data_feature n (pmdc_row phi n i ys)) B =
    / sqrt (INR (S n)) *
      ((((pmdc_col phi n i xs)^T *m B *m pmdc_col phi n i xs)%R ord0 ord0) -
       (((pmdc_col phi n i ys)^T *m B *m pmdc_col phi n i ys)%R ord0 ord0)).
    by rewrite -Hs; exact: pmdc_pairing_diff.
  rewrite Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ (Rinv_0_lt_compat _ Hsp))).
  have Hq := pmdc_quad_diff n B k (pmdc_col phi n i xs) (pmdc_col phi n i ys) HB Hk HA.
  have Hn1 := pmdc_row_norm phi U n i xs Hb.
  have Hn2 := pmdc_row_norm phi U n i ys Hb.
  have Hd : pmdc_norm (pmdc_col phi n i xs - pmdc_col phi n i ys)%R <= D i.
    exact: pmdc_row_dist phi n i xs ys Hl.
  have H0 := pmdc_norm_ge0 (pmdc_col phi n i xs - pmdc_col phi n i ys)%R.
  have Hc1 := pmdc_norm_ge0 (pmdc_col phi n i xs).
  have Hc2 := pmdc_norm_ge0 (pmdc_col phi n i ys).
  exact: pmdc_row_arith Hk Hsp H0 Hd Hc1 Hc2 Hn1 Hn2 Hq.
rewrite /pmdc_score -finite_sum_minus.
apply: Rle_trans (finite_sum_abs_le _ _) _.
apply: Rle_trans (finite_sum_le _ (fun i => Rabs (y i) * (2 * k * U * D i)) _ _) _.
  move=> i _; rewrite -Rmult_minus_distr_l Rabs_mult.
  by apply: Rmult_le_compat_l; [exact: Rabs_pos | exact: Hrow].
have E1 : finite_sum (fun i => Rabs (y i) * (2 * k * U * D i)) (List.seq 0 N) =
    2 * k * U * finite_sum (fun i => Rabs (y i) * D i) (List.seq 0 N).
  by rewrite -finite_sum_scale; apply: finite_sum_ext => i _; ring.
rewrite E1.
have Hkk : 0 <= 2 * k * U by nra.
apply: Rmult_le_compat_l => //.
have CS := paper_main_gordon_sum_cauchy (fun i => Rabs (y i)) D (List.seq 0 N).
have Ey : finite_sum (fun i => Rabs (y i) ^ 2) (List.seq 0 N) = squared_norm y (List.seq 0 N).
  by apply: finite_sum_ext => i _; rewrite -Rsqr_pow2 -Rsqr_abs Rsqr_pow2.
have ED : finite_sum (fun i => D i ^ 2) (List.seq 0 N) =
    paper_main_gordon_distance (N * S n) xs ys ^ 2.
  rewrite -pmdc_dist_blocks; apply: finite_sum_ext => i _.
  by rewrite /D pow2_sqrt //; apply: finite_sum_nonneg => j _; exact: pow2_ge_0.
rewrite Ey ED in CS.
have Hsy : 0 <= squared_norm y (List.seq 0 N).
  by apply: finite_sum_nonneg => i _; exact: pow2_ge_0.
have Hdist : 0 <= paper_main_gordon_distance (N * S n) xs ys by exact: sqrt_pos.
have HS0 : 0 <= finite_sum (fun i => Rabs (y i) * D i) (List.seq 0 N).
  by apply: finite_sum_nonneg => i _; apply: Rmult_le_pos; [exact: Rabs_pos | exact: HD0].
have Hy2 : squared_norm y (List.seq 0 N) <= 1.
  have Hsq := pow2_sqrt _ Hsy.
  have Hs0 := sqrt_pos (squared_norm y (List.seq 0 N)).
  move: Hy; rewrite /euclidean_norm => Hy.
  nra.
move: CS HS0 Hdist Hsy Hy2.
set S := finite_sum _ _; set G := paper_main_gordon_distance _ _ _; set q := squared_norm _ _.
move=> CS HS0 Hdist Hsy Hy2.
nra.
Qed.
