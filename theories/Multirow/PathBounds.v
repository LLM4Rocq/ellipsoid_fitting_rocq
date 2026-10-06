(* Uniform bounds and continuity along the simultaneous path of all rows.

   Z(t) = gaussian_row_array n m t xs is the block array of the
   Z_i(t) = sqrt t W_i + sqrt (1-t) G_i of the m + 1 rows read from the
   list xs, and Phi = lower_block_phi is the soft minimax on block arrays.
   This module proves:
   - a Lipschitz bound |Phi A - Phi A'| <= K |A - A'| on block arrays, by the
     mean value theorem along a segment and the bound of the first
     derivative (mexp_phi_lipschitz), and the continuity of Phi
     (mexp_phi_continuous);
   - bounds on |Z(t)|, |Z(t) - Z(s)| and on the block velocity, by the
     product weight of degree 2 of the coordinates (mexp_row_array_bound,
     mexp_row_array_difference, mexp_velocity_array_bound);
   - for the value Phi (Z(t)): continuity in the coordinates for every t, a
     polynomial bound uniform in t in [0,1], and a bound of the difference
     of two times by L (|sqrt t - sqrt s| + |sqrt (1-t) - sqrt (1-s)|)
     (mexp_value_continuous, mexp_value_polynomial, mexp_value_difference);
   - a polynomial bound of degree 4 of the sum of the row accelerations of
     Multirow.RowVelocityDerivatives, uniform for t in [tau, 1 - tau]
     (mexp_acceleration_sum_bound).

   The constants come from the uniform score bound
   Multirow.ObservableBounds.multirow_block_score_bound_uniform, so the
   hypotheses are 0 < beta, 0 < gamma, Y <> [] and S <> []; there is no
   hypothesis on the norms of y or B. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Soft.Definitions Soft.MinimaxDerivativeDefinitions
  Goe.Definitions Joint.Definitions Joint.TimeVelocity Row.ArrayDefinitions
  Matrix.BlockInjection Row.ObservableDefinitions Multirow.ArrayTimeDefinitions
  Matrix.EuclideanProduct Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Multirow.RowVelocityDerivatives
  Analysis.CoordinateTopology.
From EllipsoidFitting Require Analysis.CalculusBridge Joint.PathTimeDerivative
  Joint.PathIncrements Joint.ObservableGrowth Goe.MatrixBasis
  Matrix.OperatorNormProperties Matrix.EntryNormBounds Soft.MinimaxFrechet
  Soft.LowerDerivativeBounds Multirow.ObservableBounds Row.DecoderRegularity
  Analysis.CoordinateTopology Gaussian.Coordinate.Weights Matrix.BlockBasis.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

Local Ltac mexp_norm_nonneg := apply/RleP; apply normr_ge0.

(* Tuples. *)

Lemma mexp_tuple_build_ext (V : normedModType R) k (f g : nat -> V) :
  (forall i, (i <= k)%coq_nat -> f i = g i) -> tuple_build V k f = tuple_build V k g.
Proof.
  elim: k f g => [|k IH] f g H /=; first by apply: H; lia.
  rewrite (H 0%nat ltac:(lia)) (IH (fun i => f i.+1) (fun i => g i.+1)) //.
  move=> i Hi; apply: H; lia.
Qed.

Lemma mexp_tuple_build_sub (V : normedModType R) k (f g : nat -> V) :
  (tuple_build V k f - tuple_build V k g)%R = tuple_build V k (fun i => (f i - g i)%R).
Proof.
  elim: k f g => [|k IH] f g //=.
  rewrite -(IH (fun i => f i.+1) (fun i => g i.+1)); reflexivity.
Qed.

(* The constant of the pair growth of one row. *)

Definition mexp_KZ n : R :=
  INR (Datatypes.S n)^2 * Rabs (/sqrt (INR (Datatypes.S n))) +
  goe_scale n * INR (Datatypes.S (goe_vector_index n)).

Lemma mexp_KZ_nonneg n : 0 <= mexp_KZ n.
Proof.
  unfold mexp_KZ; apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos].
  - apply Rmult_le_pos; [pose proof (Goe.MatrixBasis.goe_scale_positive n); lra|apply pos_INR].
Qed.

Lemma mexp_quadratic_input_growth n
    (q : euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))) :
  (`|joint_quadratic_input n (fst q)|)%R <= mexp_KZ n * (1+(`|q|)%R)^2.
Proof.
  have Hq : 0 <= (`|q|)%R by mexp_norm_nonneg.
  have Hx : 0 <= (`|fst q|)%R by mexp_norm_nonneg.
  have Hxq : (`|fst q|)%R <= (`|q|)%R by apply/RleP; apply euclidean_product_norm_fst.
  have HG : 0 <= goe_scale n * INR (Datatypes.S (goe_vector_index n)).
  { apply Rmult_le_pos; [pose proof (Goe.MatrixBasis.goe_scale_positive n); lra|apply pos_INR]. }
  eapply Rle_trans; [apply Joint.ObservableGrowth.joint_quadratic_input_norm|].
  unfold mexp_KZ; apply Rmult_le_compat.
  - apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos].
  - apply pow2_ge_0.
  - lra.
  - nra.
Qed.

Lemma mexp_goe_growth n
    (q : euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))) :
  (`|goe_matrix n (snd q)|)%R <= mexp_KZ n * (1+(`|q|)%R)^2.
Proof.
  have Hq : 0 <= (`|q|)%R by mexp_norm_nonneg.
  have Hz : 0 <= (`|snd q|)%R by mexp_norm_nonneg.
  have Hzq : (`|snd q|)%R <= (`|q|)%R by apply/RleP; apply euclidean_product_norm_snd.
  have HW : 0 <= INR (Datatypes.S n)^2 * Rabs (/sqrt (INR (Datatypes.S n))).
  { apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos]. }
  have HG : 0 <= goe_scale n * INR (Datatypes.S (goe_vector_index n)).
  { apply Rmult_le_pos; [pose proof (Goe.MatrixBasis.goe_scale_positive n); lra|apply pos_INR]. }
  eapply Rle_trans; [apply Goe.MatrixBasis.goe_matrix_norm_bound|].
  unfold mexp_KZ; apply Rmult_le_compat; [exact HG|exact Hz|lra|nra].
Qed.

Lemma mexp_scale_norm_le n (c : R) (M : matrix n) (K : R) :
  Rabs c <= 1 -> (`|M|)%R <= K -> (`|matrix_scale n c M|)%R <= K.
Proof.
  move=> Hc HM; unfold matrix_scale; rewrite Matrix.OperatorNormProperties.real_norm_scal_exact.
  have HN : 0 <= (`|M|)%R by mexp_norm_nonneg.
  have HA : 0 <= Rabs c by apply Rabs_pos.
  nra.
Qed.

Lemma mexp_joint_matrix_bound n t
    (q : euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))) :
  0 <= t <= 1 ->
  (`|joint_matrix n (matrix_zero n) t (fst q) (snd q)|)%R <=
    2 * (mexp_KZ n * (1+(`|q|)%R)^2).
Proof.
  move=> Ht.
  rewrite (Joint.PathTimeDerivative.joint_matrix_normalized_path n (matrix_zero n) t (fst q) (snd q)
    (proj1 Ht)).
  unfold matrix_add, matrix_zero; rewrite add0r.
  eapply Rle_trans; [apply/RleP; apply ler_normD|].
  have Hs : Rabs (sqrt t) <= 1.
  { rewrite (Rabs_pos_eq _ (sqrt_pos t)).
    apply (Rle_trans _ (sqrt 1)); [apply sqrt_le_1_alt; lra|rewrite sqrt_1; lra]. }
  have Hs' : Rabs (sqrt (1-t)) <= 1.
  { rewrite (Rabs_pos_eq _ (sqrt_pos (1-t))).
    apply (Rle_trans _ (sqrt 1)); [apply sqrt_le_1_alt; lra|rewrite sqrt_1; lra]. }
  have H1 := mexp_scale_norm_le n (sqrt t) _ _ Hs (mexp_quadratic_input_growth n q).
  have H2 := mexp_scale_norm_le n (sqrt (1-t)) _ _ Hs' (mexp_goe_growth n q).
  change ((`|matrix_scale n (sqrt t) (joint_quadratic_input n (fst q))|)%R +
    (`|matrix_scale n (sqrt (1-t)) (goe_matrix n (snd q))|)%R <=
    2 * (mexp_KZ n * (1+(`|q|)%R)^2)).
  lra.
Qed.

Lemma mexp_pair_weight n m i xs :
  (i <= m)%coq_nat ->
  length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
  (1+(`|gaussian_row_pair n i xs|)%R)^2 <= gaussian_coordinate_product_weight 2 xs.
Proof. exact: Row.DecoderRegularity.gaussian_row_pair_squared_weight. Qed.

Theorem mexp_row_array_bound n m t xs :
  0 <= t <= 1 ->
  length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
  (`|gaussian_row_array n m t xs|)%R <=
    INR (Datatypes.S m) * (2 * mexp_KZ n) * gaussian_coordinate_product_weight 2 xs.
Proof.
  move=> Ht HL; rewrite Rmult_assoc.
  apply: Matrix.EntryNormBounds.tuple_build_norm_bound.
  - apply Rmult_le_pos; [have := mexp_KZ_nonneg n; lra|].
    apply Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_nonnegative.
  - move=> i Hi; unfold gaussian_row_matrix.
    eapply Rle_trans; [apply mexp_joint_matrix_bound; exact Ht|].
    have := mexp_pair_weight n m i xs Hi HL; have := mexp_KZ_nonneg n; nra.
Qed.

Theorem mexp_row_array_difference n m s t xs :
  0 <= s -> 0 <= t ->
  length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
  (`|(gaussian_row_array n m t xs - gaussian_row_array n m s xs)%R|)%R <=
    INR (Datatypes.S m) * mexp_KZ n *
      (Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) *
      gaussian_coordinate_product_weight 2 xs.
Proof.
  move=> Hs Ht HL; unfold gaussian_row_array; rewrite mexp_tuple_build_sub.
  have HM : 0 <= Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s)).
  { apply Rplus_le_le_0_compat; apply Rabs_pos. }
  have HW := Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_nonnegative 2 xs.
  have HK := mexp_KZ_nonneg n.
  rewrite !Rmult_assoc.
  apply: Matrix.EntryNormBounds.tuple_build_norm_bound.
  - apply Rmult_le_pos; [exact HK|apply Rmult_le_pos; assumption].
  - move=> i Hi; unfold gaussian_row_matrix.
    have HD := Joint.PathIncrements.joint_matrix_path_difference_bound n (matrix_zero n) s t
      (gaussian_row_pair n i xs) Hs Ht.
    unfold matrix_add, matrix_scale in HD; rewrite scaleN1r in HD.
    eapply Rle_trans; [exact HD|].
    have HP := mexp_pair_weight n m i xs Hi HL.
    have HKM : 0 <= mexp_KZ n *
      (Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) by apply Rmult_le_pos.
    change (mexp_KZ n * (Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) *
      (1+(`|gaussian_row_pair n i xs|)%R)^2 <= mexp_KZ n *
      ((Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) *
        gaussian_coordinate_product_weight 2 xs)).
    rewrite -Rmult_assoc; apply Rmult_le_compat_l; [exact HKM|exact HP].
Qed.

Theorem mexp_velocity_array_bound n m t xs :
  length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
  (`|gaussian_array_velocity n m t xs|)%R <=
    INR (Datatypes.S m) *
      ((Rabs (/(2*sqrt t)) + Rabs (/(2*sqrt (1-t)))) * mexp_KZ n) *
      gaussian_coordinate_product_weight 2 xs.
Proof.
  move=> HL; rewrite Rmult_assoc.
  have HK := mexp_KZ_nonneg n.
  have HW := Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_nonnegative 2 xs.
  have Ha := Rabs_pos (/(2*sqrt t)); have Hb := Rabs_pos (/(2*sqrt (1-t))).
  apply: Matrix.EntryNormBounds.tuple_build_norm_bound.
  - apply Rmult_le_pos; [apply Rmult_le_pos; lra|exact HW].
  - move=> i Hi; unfold joint_time_velocity, matrix_add, matrix_scale.
    set q := gaussian_row_pair n i xs.
    eapply Rle_trans; [apply/RleP; apply ler_normD|].
    rewrite (Matrix.OperatorNormProperties.real_norm_scal_exact (/(2*sqrt t)))
      (Matrix.OperatorNormProperties.real_norm_scal_exact (-/(2*sqrt (1-t)))) Rabs_Ropp.
    have H1 := mexp_quadratic_input_growth n q.
    have H2 := mexp_goe_growth n q.
    have H3 := mexp_pair_weight n m i xs Hi HL; fold q in H3.
    have HN1 : 0 <= (`|joint_quadratic_input n (fst q)|)%R by mexp_norm_nonneg.
    have HN2 : 0 <= (`|goe_matrix n (snd q)|)%R by mexp_norm_nonneg.
    have HP : 0 <= (1+(`|q|)%R)^2 by apply pow2_ge_0.
    have H1' : (`|joint_quadratic_input n (fst q)|)%R <=
      mexp_KZ n * gaussian_coordinate_product_weight 2 xs by nra.
    have H2' : (`|goe_matrix n (snd q)|)%R <=
      mexp_KZ n * gaussian_coordinate_product_weight 2 xs by nra.
    apply (Rle_trans _
      (Rabs (/(2*sqrt t)) * (mexp_KZ n * gaussian_coordinate_product_weight 2 xs) +
       Rabs (/(2*sqrt (1-t))) * (mexp_KZ n * gaussian_coordinate_product_weight 2 xs))).
    + apply Rplus_le_compat; apply Rmult_le_compat_l; assumption.
    + right; ring.
Qed.

(* The soft minimax on block arrays: Lipschitz bound and continuity. *)

Lemma mexp_block_line_derivative n m (A H : block_array n m) (u : R) :
  @is_derive R R^o (block_NormedModule n m) u 1
    (fun v : R => (A + v *: H)%R : block_NormedModule n m) H.
Proof.
  have HB : @is_derive R R^o (block_NormedModule n m) u 1
      (fun v : R => (v *: H)%R : block_NormedModule n m) H.
  { have HD := @Joint.PathTimeDerivative.joint_time_derive_scale (block_NormedModule n m)
      (fun v => v) u 1 H (Analysis.CalculusBridge.is_derive_id_R u).
    rewrite -[X in is_derive _ _ _ X](scale1r H); exact HD. }
  have HD := is_deriveD (is_derive_cst (A : block_NormedModule n m) (u : R^o) 1) HB.
  rewrite -[X in is_derive _ _ _ X](add0r H); exact HD.
Qed.

Lemma mexp_phi_line_derivative n m beta gamma y B Y S (A H : block_array n m) (u : R) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  @is_derive R R^o R^o u 1
    (fun v : R => lower_block_phi n m beta gamma y B Y S (A + v *: H)%R)
    (lower_block_first n m beta gamma y B Y S (A + u *: H)%R H).
Proof.
  move=> Hb Hg HY HS.
  have HP := Joint.PathTimeDerivative.joint_time_is_diff_of_derive
    (fun v : R => (A + v *: H)%R : block_NormedModule n m) u H
    (mexp_block_line_derivative n m A H u).
  have HF := proj1 (Soft.MinimaxFrechet.lower_block_derivatives n m beta gamma y B Y S Hb Hg HY HS
    (A + u *: H)%R).
  have HC := is_diff_comp HP HF.
  apply: DeriveDef.
    exact/diff_derivable/ex_diff.
  rewrite deriveE ?diff_val //= scale1r; reflexivity.
Qed.

Theorem mexp_phi_lipschitz n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists K : R, 0 <= K /\ forall A A' : block_array n m,
    Rabs (lower_block_phi n m beta gamma y B Y S A -
      lower_block_phi n m beta gamma y B Y S A') <= K * (`|(A - A')%R|)%R.
Proof.
  move=> Hb Hg HY HS.
  destruct (Multirow.ObservableBounds.multirow_block_score_bound_uniform n m y B Y S)
    as [K [HK HKs]].
  exists K; split; [exact HK|]; move=> A A'.
  set H := (A - A')%R.
  destruct (MVT_cor2
    (fun v : R => lower_block_phi n m beta gamma y B Y S (A' + v *: H)%R)
    (fun v : R => lower_block_first n m beta gamma y B Y S (A' + v *: H)%R H) 0 1 ltac:(lra))
    as [c [HE HC]].
  { move=> v Hv; apply Analysis.CalculusBridge.is_derive_Reals, mexp_phi_line_derivative; assumption. }
  have H1 : (A' + 1 *: H)%R = A by rewrite scale1r /H addrC subrK.
  have H0 : (A' + 0 *: H)%R = A' by rewrite scale0r addr0.
  rewrite H1 H0 Rminus_0_r Rmult_1_r in HE.
  rewrite HE.
  exact: Multirow.ObservableBounds.multirow_lower_block_first_bound_general.
Qed.

Theorem mexp_phi_continuous n m beta gamma y B Y S (A : block_array n m) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  {for A, continuous (lower_block_phi n m beta gamma y B Y S : block_array n m -> R^o)}.
Proof.
  move=> Hb Hg HY HS.
  have HF := proj1 (Soft.MinimaxFrechet.lower_block_derivatives n m beta gamma y B Y S Hb Hg HY HS A).
  apply: differentiable_continuous; exact: ex_diff.
Qed.

(* The value Phi (Z(t)) as a function of the coordinates. *)

Theorem mexp_value_continuous n m beta gamma y B Y S t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  finite_joint_continuous
    (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_array_value n m beta gamma y B Y S t).
Proof.
  move=> Hb Hg HY HS.
  apply/Analysis.CoordinateTopology.finite_joint_continuous_filter => q.
  unfold gaussian_array_value.
  have HA := Row.DecoderRegularity.gaussian_row_array_continuous n m t q.
  have HC := mexp_phi_continuous n m beta gamma y B Y S
    (gaussian_row_array n m t (coordinates_to_list _ q)) Hb Hg HY HS.
  exact: (continuous_comp HA HC).
Qed.

Theorem mexp_value_polynomial n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists C : R, 0 <= C /\ forall t, 0 <= t <= 1 ->
    finite_polynomial_bound
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat C 2
      (gaussian_array_value n m beta gamma y B Y S t).
Proof.
  move=> Hb Hg HY HS.
  destruct (mexp_phi_lipschitz n m beta gamma y B Y S Hb Hg HY HS) as [K [HK HL]].
  set P0 := Rabs (lower_block_phi n m beta gamma y B Y S 0%R).
  set c := INR (Datatypes.S m) * (2 * mexp_KZ n).
  have Hc : 0 <= c.
  { apply Rmult_le_pos; [apply pos_INR|have := mexp_KZ_nonneg n; lra]. }
  have HP0 : 0 <= P0 by apply Rabs_pos.
  exists (P0 + K * c); split; [have := Rmult_le_pos _ _ HK Hc; lra|].
  move=> t Ht; split; [have := Rmult_le_pos _ _ HK Hc; lra|]; move=> xs Hxs.
  unfold gaussian_array_value.
  set A := gaussian_row_array n m t xs.
  have H1 := HL A 0%R; rewrite subr0 in H1.
  have H2 := mexp_row_array_bound n m t xs Ht Hxs; fold A c in H2.
  have Hw := Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_at_least_one 2 xs.
  have H3 := Rabs_triang_inv (lower_block_phi n m beta gamma y B Y S A)
    (lower_block_phi n m beta gamma y B Y S 0%R).
  fold P0 in H3.
  have H5 : P0 <= P0 * gaussian_coordinate_product_weight 2 xs.
  { rewrite -{1}(Rmult_1_r P0); apply Rmult_le_compat_l; [exact HP0|exact Hw]. }
  have H6 : (P0 + K * c) * gaussian_coordinate_product_weight 2 xs =
    P0 * gaussian_coordinate_product_weight 2 xs +
    K * (c * gaussian_coordinate_product_weight 2 xs) by ring.
  have H7 : Rabs (lower_block_phi n m beta gamma y B Y S A) <=
    Rabs (lower_block_phi n m beta gamma y B Y S A -
      lower_block_phi n m beta gamma y B Y S 0%R) + P0 by lra.
  rewrite H6; eapply Rle_trans; [exact H7|].
  rewrite Rplus_comm; apply Rplus_le_compat; [exact H5|].
  eapply Rle_trans; [exact H1|].
  apply Rmult_le_compat_l; [exact HK|exact H2].
Qed.

Theorem mexp_value_difference n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists L : R, 0 <= L /\ forall s t xs, 0 <= s -> 0 <= t ->
    length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
    Rabs (gaussian_array_value n m beta gamma y B Y S t xs -
      gaussian_array_value n m beta gamma y B Y S s xs) <=
    L * (Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) *
      gaussian_coordinate_product_weight 2 xs.
Proof.
  move=> Hb Hg HY HS.
  destruct (mexp_phi_lipschitz n m beta gamma y B Y S Hb Hg HY HS) as [K [HK HL]].
  exists (K * (INR (Datatypes.S m) * mexp_KZ n)); split.
  { apply Rmult_le_pos; [exact HK|apply Rmult_le_pos; [apply pos_INR|apply mexp_KZ_nonneg]]. }
  move=> s t xs Hs Ht Hxs; unfold gaussian_array_value.
  eapply Rle_trans; [apply HL|].
  have HD := mexp_row_array_difference n m s t xs Hs Ht Hxs.
  eapply Rle_trans; [apply Rmult_le_compat_l; [exact HK|exact HD]|].
  right; ring.
Qed.

(* Coefficients of the time derivatives, for t in [tau, 1 - tau]. *)

Lemma mexp_coefficient_bound u tau :
  0 < tau <= u ->
  Rabs (/(2*sqrt u)) <= /(2*sqrt tau) /\ Rabs (-/(4*u*sqrt u)) <= /(4*tau*sqrt tau).
Proof.
  move=> [Htau Hu].
  have Hst : 0 < sqrt tau by apply sqrt_lt_R0.
  have Hsu : sqrt tau <= sqrt u by apply sqrt_le_1_alt.
  have Hsu' : 0 < sqrt u by lra.
  have P1 : 0 <= /(2*sqrt u) by apply Rlt_le, Rinv_0_lt_compat; lra.
  have P2 : 0 <= /(4*u*sqrt u).
  { apply Rlt_le, Rinv_0_lt_compat; apply Rmult_lt_0_compat; [lra|exact Hsu']. }
  split.
  - rewrite (Rabs_pos_eq _ P1).
    apply Rinv_le_contravar; lra.
  - rewrite Rabs_Ropp (Rabs_pos_eq _ P2).
    apply Rinv_le_contravar; [apply Rmult_lt_0_compat; [lra|exact Hst]|].
    apply Rmult_le_compat; [lra|lra|lra|exact Hsu].
Qed.

Lemma mexp_abs_mult_le a b A B :
  Rabs a <= A -> Rabs b <= B -> Rabs (a * b) <= A * B.
Proof.
  move=> Ha Hb; rewrite Rabs_mult.
  apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Ha|exact Hb].
Qed.

Lemma mexp_four_term_bound x1 x2 x3 x4 a b c e X1 X2 X3 X4 A1 B1 :
  Rabs x1 <= X1 -> Rabs x2 <= X2 -> Rabs x3 <= X3 -> Rabs x4 <= X4 ->
  Rabs a <= A1 -> Rabs b <= B1 -> Rabs c <= A1 -> Rabs e <= B1 ->
  Rabs (x1*a + x2*b + (x3*c + x4*e)) <= X1*A1 + X2*B1 + (X3*A1 + X4*B1).
Proof.
  move=> H1 H2 H3 H4 Ha Hb Hc He.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat.
  - eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat; apply mexp_abs_mult_le; assumption.
  - eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat; apply mexp_abs_mult_le; assumption.
Qed.

Lemma mexp_finite_sum_abs_le (f : nat -> R) (c : R) (I : list nat) :
  (forall i, In i I -> Rabs (f i) <= c) -> Rabs (finite_sum f I) <= INR (length I) * c.
Proof.
  induction I as [|i I IH]; intro H.
  - simpl finite_sum; simpl length; rewrite Rabs_R0; simpl INR; lra.
  - have Hi := H i (or_introl erefl).
    have HI := IH (fun j Hj => H j (or_intror Hj)).
    simpl finite_sum; simpl length.
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite S_INR; lra.
Qed.

Lemma mexp_block_inject_norm n m i (M : matrix n) :
  (`|block_inject n m i M|)%R <= INR (Datatypes.S m) * (`|M|)%R.
Proof.
  unfold block_inject.
  apply: Matrix.EntryNormBounds.tuple_build_norm_bound; [mexp_norm_nonneg|].
  move=> j Hj; case: (Nat.eqb j i); [apply Rle_refl|rewrite normr0; mexp_norm_nonneg].
Qed.

Theorem mexp_row_acceleration_bound n m beta gamma y B Y S tau :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 < tau ->
  exists C : R, 0 <= C /\ forall t i xs, tau <= t <= 1 - tau -> (i <= m)%coq_nat ->
    length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
    Rabs (mexp_row_acceleration n m beta gamma y B Y S t i xs) <=
      C * gaussian_coordinate_product_weight 4 xs.
Proof.
  move=> Hb Hg HY HS Htau.
  destruct (Multirow.ObservableBounds.multirow_block_score_bound_uniform n m y B Y S)
    as [K [HK HKs]].
  have HKs' : forall z s, In z Y -> In s S -> forall W : block_array n m,
      Rabs (lower_block_scores n m y B z s W) <= K * (`|W|)%R.
  { move=> z s Hz Hs W; exact: HKs. }
  set L2 := 2 * K ^ 2 * (beta + gamma).
  set IM := INR (Datatypes.S m).
  set KZ := mexp_KZ n.
  set c2 := /(2*sqrt tau).
  set c4 := /(4*tau*sqrt tau).
  set VB := IM * ((c2 + c2) * KZ).
  set UB := IM * KZ.
  have Hst : 0 < sqrt tau by apply sqrt_lt_R0.
  have HL2 : 0 <= L2.
  { apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|lra]. }
  have HIM : 0 <= IM by apply pos_INR.
  have HKZ : 0 <= KZ by apply mexp_KZ_nonneg.
  have Hc2 : 0 <= c2 by apply Rlt_le, Rinv_0_lt_compat; lra.
  have Hc4 : 0 <= c4.
  { apply Rlt_le, Rinv_0_lt_compat; apply Rmult_lt_0_compat; [lra|exact Hst]. }
  have HVB : 0 <= VB by apply Rmult_le_pos; [exact HIM|apply Rmult_le_pos; lra].
  have HUB : 0 <= UB by apply Rmult_le_pos.
  exists (2 * (L2 * UB * VB * c2 + K * UB * c4)); split.
  { have := Rmult_le_pos _ _ (Rmult_le_pos _ _ (Rmult_le_pos _ _ HL2 HUB) HVB) Hc2.
    have := Rmult_le_pos _ _ (Rmult_le_pos _ _ HK HUB) Hc4. lra. }
  move=> t i xs Ht Hi HL.
  have Ht0 : 0 < tau <= t by lra.
  have Ht1 : 0 < tau <= 1 - t by lra.
  destruct (mexp_coefficient_bound t tau Ht0) as [Ha Hb'].
  destruct (mexp_coefficient_bound (1-t) tau Ht1) as [Hc He].
  fold c2 c4 in Ha, Hb', Hc, He.
  have Hc' : Rabs (-/(2*sqrt (1-t))) <= c2 by rewrite Rabs_Ropp.
  set w2 := gaussian_coordinate_product_weight 2 xs.
  set w4 := gaussian_coordinate_product_weight 4 xs.
  have Hw2 : 1 <= w2
    by apply Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_at_least_one.
  have Hw24 : w2 * w2 = w4.
  { rewrite /w2 /w4 -Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_degree_add.
    reflexivity. }
  have Hw2le : w2 <= w4.
  { apply Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_degree_monotone; lia. }
  unfold mexp_row_acceleration; cbv zeta.
  set A := gaussian_row_array n m t xs.
  set V := gaussian_array_velocity n m t xs.
  set q := gaussian_row_pair n i xs.
  set Wi := block_inject n m i (joint_quadratic_input n (fst q)).
  set Gi := block_inject n m i (goe_matrix n (snd q)).
  have Hq := mexp_pair_weight n m i xs Hi HL; fold q w2 in Hq.
  have HV : (`|V|)%R <= VB * w2.
  { eapply Rle_trans; [apply mexp_velocity_array_bound; exact HL|].
    fold IM KZ w2; rewrite /VB.
    apply Rmult_le_compat_r; [lra|].
    apply Rmult_le_compat_l; [exact HIM|].
    apply Rmult_le_compat_r; [exact HKZ|].
    have := Rabs_Ropp (/(2*sqrt (1-t))); lra. }
  have HWi : (`|Wi|)%R <= UB * w2.
  { eapply Rle_trans; [apply mexp_block_inject_norm|]; fold IM.
    have H := mexp_quadratic_input_growth n q; fold KZ in H.
    rewrite /UB Rmult_assoc; apply Rmult_le_compat_l; [exact HIM|].
    eapply Rle_trans; [exact H|]; apply Rmult_le_compat_l; [exact HKZ|exact Hq]. }
  have HGi : (`|Gi|)%R <= UB * w2.
  { eapply Rle_trans; [apply mexp_block_inject_norm|]; fold IM.
    have H := mexp_goe_growth n q; fold KZ in H.
    rewrite /UB Rmult_assoc; apply Rmult_le_compat_l; [exact HIM|].
    eapply Rle_trans; [exact H|]; apply Rmult_le_compat_l; [exact HKZ|exact Hq]. }
  have HNV : 0 <= (`|V|)%R by mexp_norm_nonneg.
  have HNW : 0 <= (`|Wi|)%R by mexp_norm_nonneg.
  have HNG : 0 <= (`|Gi|)%R by mexp_norm_nonneg.
  have Hsec : forall U : block_array n m, (`|U|)%R <= UB * w2 ->
      Rabs (lower_block_second n m beta gamma y B Y S A U V) <= L2 * (UB * w2) * (VB * w2).
  { move=> U HU.
    have HNU : 0 <= (`|U|)%R by mexp_norm_nonneg.
    eapply Rle_trans.
    - exact: (Soft.LowerDerivativeBounds.lower_second_uniform_bound beta gamma
        (lower_block_scores n m y B) Y S A U V K Hb Hg HY HS HK HKs').
    - fold L2; apply Rmult_le_compat; [|exact HNV|apply Rmult_le_compat_l; [exact HL2|exact HU]|exact HV].
      apply Rmult_le_pos; [exact HL2|exact HNU]. }
  have Hfir : forall U : block_array n m, (`|U|)%R <= UB * w2 ->
      Rabs (lower_block_first n m beta gamma y B Y S A U) <= K * (UB * w2).
  { move=> U HU.
    eapply Rle_trans.
    - exact: (Multirow.ObservableBounds.multirow_lower_block_first_bound_general
        n m beta gamma y B Y S K A U HY HS HKs).
    - apply Rmult_le_compat_l; [exact HK|exact HU]. }
  eapply Rle_trans.
  - apply (mexp_four_term_bound _ _ _ _ _ _ _ _
      (L2 * (UB * w2) * (VB * w2)) (K * (UB * w2))
      (L2 * (UB * w2) * (VB * w2)) (K * (UB * w2)) c2 c4).
    + exact: Hsec.
    + exact: Hfir.
    + exact: Hsec.
    + exact: Hfir.
    + exact Ha.
    + exact Hb'.
    + exact Hc'.
    + exact He.
  - have E : L2 * (UB * w2) * (VB * w2) * c2 + K * (UB * w2) * c4 +
        (L2 * (UB * w2) * (VB * w2) * c2 + K * (UB * w2) * c4) =
      2 * (L2 * UB * VB * c2) * (w2 * w2) + 2 * (K * UB * c4) * w2 by ring.
    rewrite E Hw24.
    have HK4 : 2 * (K * UB * c4) * w2 <= 2 * (K * UB * c4) * w4.
    { apply Rmult_le_compat_l; [|exact Hw2le].
      have := Rmult_le_pos _ _ (Rmult_le_pos _ _ HK HUB) Hc4; lra. }
    have E2 : 2 * (L2 * UB * VB * c2 + K * UB * c4) * w4 =
      2 * (L2 * UB * VB * c2) * w4 + 2 * (K * UB * c4) * w4 by ring.
    rewrite E2; lra.
Qed.

Theorem mexp_acceleration_sum_bound n m beta gamma y B Y S tau :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 < tau ->
  exists C : R, forall t, tau <= t <= 1 - tau ->
    finite_polynomial_bound
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat C 4
      (fun xs => finite_sum (fun i => mexp_row_acceleration n m beta gamma y B Y S t i xs)
        (List.seq 0 (Datatypes.S m))).
Proof.
  move=> Hb Hg HY HS Htau.
  destruct (mexp_row_acceleration_bound n m beta gamma y B Y S tau Hb Hg HY HS Htau)
    as [C [HC HB]].
  exists (INR (Datatypes.S m) * C); move=> t Ht; split.
  { apply Rmult_le_pos; [apply pos_INR|exact HC]. }
  move=> xs HL.
  have Hw := Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_nonnegative 4 xs.
  eapply Rle_trans.
  - apply (mexp_finite_sum_abs_le _ (C * gaussian_coordinate_product_weight 4 xs)).
    move=> i Hi; apply HB; [exact Ht| |exact HL].
    apply in_seq in Hi; lia.
  - rewrite length_seq; right; ring.
Qed.
