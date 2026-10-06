From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Weights
  Chaos.CubicMassBounds Matrix.Definitions Matrix.EntriesAndLinearMaps
  Matrix.Trace Matrix.OperatorDefinitions Matrix.OperatorNorm
  Matrix.OperatorNormProperties Matrix.FrobeniusNorm Soft.MatrixDefinitions
  Soft.MinimaxDerivativeDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Norm bounds for the scores of the soft minimax of block arrays
   (Soft.MinimaxDerivativeDefinitions). Rabs (trace_pair n B U) is at most
   sqrt (INR (S n)) * matrix_operator_norm n B * `|U|, with the Frobenius
   norm of U (trace_pair_operator_frobenius_bound). With the Cauchy-Schwarz
   inequality for a unit vector y (lower_block_unit_cauchy), this bounds
   the score lower_block_scores n m y B z s U by
   sqrt (INR (S n)) * k * `|U| when every B t has operator norm at most k
   (lower_block_score_bound). *)

Lemma lower_tuple_entry_norm_bound (V : normedModType R) n i (x : tuple_NormedModule V n) :
  (`|tuple_entry V n i x|)%R <= (`|x|)%R.
Proof.
  revert i x; induction n as [|n IH]; intros [|i] x; simpl.
  - apply Rle_refl.
  - rewrite normr0; apply/RleP; apply normr_ge0.
  - apply/RleP; exact (@euclidean_product_norm_fst V (tuple_NormedModule V n) x).
  - eapply Rle_trans; [apply IH|].
    apply/RleP; exact (@euclidean_product_norm_snd V (tuple_NormedModule V n) x).
Qed.

Lemma lower_coordinate_sum_abs n f :
  Rabs (coordinate_sum n f) <= coordinate_sum n (fun i => Rabs (f i)).
Proof.
  revert f; induction n; intros f; simpl; [apply Rle_refl|].
  eapply Rle_trans; [apply Rabs_triang|apply Rplus_le_compat_l, IHn].
Qed.

Lemma lower_column_norm_sum n (U : matrix n) :
  coordinate_sum n (fun j => (`|matrix_action n U (operator_basis_vector n j)|)%R) <=
    sqrt (INR (S n)) * (`|U|)%R.
Proof.
  pose proof (coordinate_cauchy_schwarz_squared n (fun _ => 1)
    (fun j => (`|matrix_action n U (operator_basis_vector n j)|)%R)) as H.
  assert (Hone : coordinate_sum n (fun _ => 1 ^ 2) = INR (S n)).
  { rewrite normeq_coordinate_sum_const; simpl; ring. }
  assert (Hsum : coordinate_sum n
      (fun i => 1 * (`|matrix_action n U (operator_basis_vector n i)|)%R) =
    coordinate_sum n (fun i => (`|matrix_action n U (operator_basis_vector n i)|)%R)).
  { apply coordinate_sum_ext; intros; ring. }
  cbn beta in H; rewrite Hone Hsum -matrix_frobenius_column_identity in H.
  assert (Hd : 0 <= INR (S n)) by apply pos_INR.
  assert (HE : (sqrt (INR (S n)) * (`|U|)%R) ^ 2 = INR (S n) * (`|U|)%R ^ 2).
  { rewrite Rpow_mult_distr (pow2_sqrt _ Hd); reflexivity. }
  rewrite -HE in H.
  assert (Hp : 0 <= sqrt (INR (S n)) * (`|U|)%R).
  { apply Rmult_le_pos; [apply sqrt_pos|apply/RleP; apply normr_ge0]. }
  nra.
Qed.

Theorem trace_pair_operator_frobenius_bound n (B U : matrix n) :
  Rabs (trace_pair n B U) <= sqrt (INR (S n)) * matrix_operator_norm n B * (`|U|)%R.
Proof.
  unfold trace_pair; eapply Rle_trans; [apply lower_coordinate_sum_abs|].
  eapply Rle_trans with (coordinate_sum n (fun i => matrix_operator_norm n B *
    (`|matrix_action n U (operator_basis_vector n i)|)%R)).
  - apply normeq_coordinate_sum_le; intros i Hi.
    assert (HE : coordinate_sum n (fun j => matrix_entry n B i j * matrix_entry n U j i) =
      vector_entry n (matrix_action n B (matrix_action n U (operator_basis_vector n i))) i).
    { rewrite (matrix_action_entry n B _ i Hi); apply coordinate_sum_ext; intros j Hj.
      rewrite (matrix_action_basis_entry n U j i Hj Hi); reflexivity. }
    rewrite HE RabsE.
    eapply Rle_trans; [exact (lower_tuple_entry_norm_bound R^o n i _)|].
    apply matrix_action_norm_bound.
  - rewrite normeq_coordinate_sum_scale.
    eapply Rle_trans with (matrix_operator_norm n B * (sqrt (INR (S n)) * (`|U|)%R)).
    + apply Rmult_le_compat_l; [apply matrix_operator_norm_nonnegative|apply lower_column_norm_sum].
    + right; ring.
Qed.

Lemma lower_finite_sum_abs f I : Rabs (finite_sum f I) <= finite_sum (fun i => Rabs (f i)) I.
Proof.
  induction I; simpl; [rewrite Rabs_R0; lra|].
  eapply Rle_trans; [apply Rabs_triang|lra].
Qed.

Lemma lower_finite_sum_seq_shift f a k :
  finite_sum f (List.seq (S a) k) = finite_sum (fun i => f (S i)) (List.seq a k).
Proof. revert a; induction k; intros a; simpl; [reflexivity|rewrite IHk; reflexivity]. Qed.

Lemma lower_coordinate_sum_finite n f : coordinate_sum n f = finite_sum f (List.seq 0 (S n)).
Proof.
  revert f; induction n; intros f.
  - cbn [coordinate_sum List.seq finite_sum]; ring.
  - change (f O + coordinate_sum n (fun i => f (S i)) = f O + finite_sum f (List.seq 1 (S n))).
    rewrite (lower_finite_sum_seq_shift f O) -IHn; reflexivity.
Qed.

Theorem lower_block_unit_cauchy n m (y : nat -> R) (U : block_array n m) :
  euclidean_norm y (List.seq 0 (S m)) = 1 ->
  finite_sum (fun i => Rabs (y i) * (`|block_entry n m U i|)%R) (List.seq 0 (S m)) <=
    (`|U|)%R.
Proof.
  intros Hunit.
  pose proof (coordinate_cauchy_schwarz_squared m (fun i => Rabs (y i))
    (fun i => (`|block_entry n m U i|)%R)) as H.
  assert (Hy : coordinate_sum m (fun i => Rabs (y i) ^ 2) = 1).
  { transitivity (coordinate_sum m (fun i => y i ^ 2)).
    - apply coordinate_sum_ext; intros; apply vector_abs_square.
    - rewrite lower_coordinate_sum_finite; apply cubic_unit_squared_norm; exact Hunit. }
  assert (HU : coordinate_sum m (fun i => (`|block_entry n m U i|)%R ^ 2) = (`|U|)%R ^ 2).
  { symmetry; exact (tuple_norm_squared (matrix_NormedModule n) m U). }
  cbn beta in H; rewrite Hy HU lower_coordinate_sum_finite in H.
  assert (H0 : 0 <= (`|U|)%R) by (apply/RleP; apply normr_ge0).
  nra.
Qed.

Theorem lower_block_score_bound n m y B S k z s (U : block_array n m) :
  0 <= k -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1 -> In s S ->
  (forall t, In t S -> matrix_operator_norm n (B t) <= k) ->
  Rabs (lower_block_scores n m y B z s U) <= sqrt (INR (Datatypes.S n)) * k * (`|U|)%R.
Proof.
  intros Hk Hunit Hs HB.
  unfold lower_block_scores, soft_matrix_scores.
  eapply Rle_trans; [apply lower_finite_sum_abs|].
  eapply Rle_trans with (finite_sum (fun i => (sqrt (INR (Datatypes.S n)) * k) *
    (Rabs (y z i) * (`|block_entry n m U i|)%R)) (List.seq 0 (Datatypes.S m))).
  - apply cubic_sum_le; intros i Hi; rewrite Rabs_mult.
    pose proof (trace_pair_operator_frobenius_bound n (B s) (block_entry n m U i)) as HT.
    assert (HK : sqrt (INR (Datatypes.S n)) * matrix_operator_norm n (B s) *
      (`|block_entry n m U i|)%R <=
        sqrt (INR (Datatypes.S n)) * k * (`|block_entry n m U i|)%R).
    { apply Rmult_le_compat_r; [apply/RleP; apply normr_ge0|].
      apply Rmult_le_compat_l; [apply sqrt_pos|apply HB; exact Hs]. }
    replace ((sqrt (INR (Datatypes.S n)) * k) * (Rabs (y z i) * (`|block_entry n m U i|)%R))
      with (Rabs (y z i) * (sqrt (INR (Datatypes.S n)) * k * (`|block_entry n m U i|)%R))
      by ring.
    apply Rmult_le_compat_l; [apply Rabs_pos|lra].
  - rewrite cubic_sum_scale; apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [apply sqrt_pos|exact Hk].
    + apply lower_block_unit_cauchy; exact Hunit.
Qed.
