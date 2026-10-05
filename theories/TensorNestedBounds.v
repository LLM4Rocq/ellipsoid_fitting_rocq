From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights MomentDefinitions FiniteMoments
  MatrixDefinitions MatrixGibbsDefinitions OperatorDefinitions OperatorBounds OperatorProperties
  TensorDefinitions TensorBounds TensorGibbsDefinitions TensorGibbs
  TensorCombinationsDefinitions TensorCombinations TensorNestedDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/TensorNestedBounds.v from Coquelicot to MathComp-Analysis.

   The original imported Coquelicot but used nothing from it directly. Its
   only Coquelicot content came through matrix n of MatrixDefinitions,
   through matrix_operator_norm of OperatorDefinitions, through the record
   trace_atom and tensor_cost of TensorDefinitions, through the definitions
   of MatrixGibbsDefinitions, TensorGibbsDefinitions,
   TensorCombinationsDefinitions and TensorNestedDefinitions, and through
   the lemmas of OperatorBounds, OperatorProperties, TensorBounds,
   TensorGibbs and TensorCombinations that it cites. The ports of these
   modules keep the same names, arguments, fields and values, and the cited
   lemmas keep their statements. So the import of Coquelicot is dropped and
   the text below is the original's, statements and proofs.

   MathComp is not imported here. So In, the lists and ++ are Stdlib's, the
   tactics are Stdlib's (rewrite A, B keeps its meaning), and the
   arithmetic, Rabs, the powers and the order are Stdlib's, as before.
   weighted_average, finite_probability and gibbs_average come from
   MomentDefinitions and GibbsDefinitions, which never used Coquelicot and
   are unchanged. The meaning of every statement is unchanged. *)

Lemma matrix_probability_mean_operator_envelope n q B I r :
  finite_probability q I ->
  (forall i, In i I -> matrix_operator_norm n (B i) <= r i) ->
  matrix_operator_norm n (matrix_weighted_sum n q B I) <= weighted_average q I r.
Proof.
  intros Hq HB; eapply Rle_trans; [apply matrix_weighted_sum_operator_bound|].
  assert (HE : weighted_average (fun i => Rabs (q i)) I
    (fun i => matrix_operator_norm n (B i)) =
    weighted_average q I (fun i => matrix_operator_norm n (B i))).
  { unfold weighted_average; apply gibbs_sum_ext; intros i Hi.
    rewrite Rabs_pos_eq by (apply (proj1 Hq); exact Hi); reflexivity. }
  rewrite HE; apply weighted_average_monotone; assumption.
Qed.

Lemma matrix_centered_operator_envelope n q B I r i :
  finite_probability q I ->
  (forall j, In j I -> matrix_operator_norm n (B j) <= r j) -> In i I ->
  matrix_operator_norm n (matrix_centered n q B I i) <= r i + weighted_average q I r.
Proof.
  intros Hq HB Hi; unfold matrix_centered.
  pose proof (matrix_probability_mean_operator_envelope n q B I r Hq HB) as HM.
  eapply Rle_trans; [apply matrix_operator_norm_triangle|].
  rewrite matrix_operator_norm_scale.
  replace (Rabs (-1)) with 1 by (rewrite Rabs_left; lra).
  specialize (HB i Hi); lra.
Qed.

Theorem centered_trace_atoms_moment_cost n q B I r :
  finite_probability q I -> (forall i, In i I -> 0 <= r i) ->
  (forall i, In i I -> matrix_operator_norm n (B i) <= r i) ->
  tensor_cost (centered_trace_atoms n q B I) <=
    8 * weighted_average q I (fun i => r i ^ 3).
Proof.
  intros Hq Hr HB; unfold centered_trace_atoms; rewrite diagonal_trace_atoms_cost.
  assert (HE : weighted_average (fun i => Rabs (q i)) I
    (fun i => matrix_operator_norm n (matrix_centered n q B I i) ^ 3) =
    weighted_average q I (fun i => matrix_operator_norm n (matrix_centered n q B I i) ^ 3)).
  { unfold weighted_average; apply gibbs_sum_ext; intros i Hi.
    rewrite Rabs_pos_eq by (apply (proj1 Hq); exact Hi); reflexivity. }
  rewrite HE; apply weighted_cubic_envelope; try assumption.
  - intros; apply matrix_operator_norm_nonnegative.
  - intros; apply matrix_centered_operator_envelope; assumption.
Qed.

Lemma weighted_scaled_cube q I k r :
  weighted_average q I (fun i => (k * r i) ^ 3) =
    k ^ 3 * weighted_average q I (fun i => r i ^ 3).
Proof.
  rewrite <- weighted_average_scale; apply weighted_average_ext; intros; ring.
Qed.

Lemma nested_inner_probability n gamma offset coeff S (A : matrix n) y :
  S <> [] -> finite_probability (nested_inner_weights n gamma offset coeff S A y) S.
Proof. intros HS; apply tensor_gibbs_finite_probability; exact HS. Qed.

Lemma nested_outer_probability n beta gamma offset coeff Y S (A : matrix n) :
  Y <> [] -> finite_probability (nested_outer_weights n beta gamma offset coeff Y S A) Y.
Proof. intros HY; apply tensor_gibbs_finite_probability; exact HY. Qed.

Lemma nested_mean_operator_bound n gamma offset coeff S (A : matrix n) k r y :
  S <> [] ->
  (forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  matrix_operator_norm n (nested_mean_matrix n gamma offset coeff S A y) <= k * r y.
Proof. intros HS HB; apply matrix_gibbs_mean_operator_bound; assumption. Qed.

Lemma nested_inner_center_operator_bound n gamma offset coeff S (A : matrix n) k r y s :
  S <> [] ->
  (forall t, In t S -> matrix_operator_norm n (coeff y t) <= k * r y) -> In s S ->
  matrix_operator_norm n (nested_inner_center n gamma offset coeff S A y s) <= 2 * k * r y.
Proof.
  intros HS HB Hs; replace (2 * k * r y) with (2 * (k * r y)) by ring.
  apply matrix_centered_operator_bound; try assumption.
  apply nested_inner_probability; exact HS.
Qed.

Lemma nested_outer_center_operator_bound n beta gamma offset coeff Y S (A : matrix n) k r y :
  Y <> [] -> S <> [] ->
  (forall z, In z Y -> forall s, In s S -> matrix_operator_norm n (coeff z s) <= k * r z) ->
  In y Y ->
  matrix_operator_norm n (nested_outer_center n beta gamma offset coeff Y S A y) <=
    k * (r y + weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y r).
Proof.
  intros HY HS HB Hy.
  pose proof (matrix_centered_operator_envelope n
    (nested_outer_weights n beta gamma offset coeff Y S A)
    (nested_mean_matrix n gamma offset coeff S A) Y (fun z => k * r z) y) as H.
  rewrite weighted_average_scale in H.
  replace (k * (r y + weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y r))
    with (k * r y + k * weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y r) by ring.
  apply H; try assumption.
  - apply nested_outer_probability; exact HY.
  - intros z Hz; apply nested_mean_operator_bound; [exact HS|apply HB; exact Hz].
Qed.

Theorem nested_inner_atoms_cost_bound n beta gamma offset coeff Y S (A : matrix n) k r :
  Y <> [] -> S <> [] ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  tensor_cost (nested_inner_atoms n beta gamma offset coeff Y S A) <=
    8 * k ^ 3 * weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (fun y => r y ^ 3).
Proof.
  intros HY HS HB; unfold nested_inner_atoms.
  assert (Hq := nested_outer_probability n beta gamma offset coeff Y S A HY).
  rewrite tensor_weighted_join_probability_cost by exact Hq.
  eapply Rle_trans with (weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
    (fun y => 8 * (k * r y) ^ 3)).
  - apply weighted_average_monotone; [exact Hq|]; intros y Hy.
    apply centered_trace_atoms_cost_bound.
    + apply nested_inner_probability; exact HS.
    + apply HB; exact Hy.
  - rewrite weighted_average_scale, weighted_scaled_cube; right; ring.
Qed.

Theorem nested_outer_atoms_cost_bound n beta gamma offset coeff Y S (A : matrix n) k r :
  Y <> [] -> S <> [] -> 0 <= k -> (forall y, In y Y -> 0 <= r y) ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  tensor_cost (nested_outer_atoms n beta gamma offset coeff Y S A) <=
    8 * k ^ 3 * weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (fun y => r y ^ 3).
Proof.
  intros HY HS Hk Hr HB; unfold nested_outer_atoms.
  eapply Rle_trans with (8 * weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
    (fun y => (k * r y) ^ 3)).
  - apply centered_trace_atoms_moment_cost.
    + apply nested_outer_probability; exact HY.
    + intros y Hy; apply Rmult_le_pos; [exact Hk|apply Hr; exact Hy].
    + intros y Hy; apply nested_mean_operator_bound; [exact HS|apply HB; exact Hy].
  - rewrite weighted_scaled_cube; right; ring.
Qed.

Theorem nested_covariance_atoms_cost_bound n beta gamma offset coeff Y S (A : matrix n) k r :
  Y <> [] -> S <> [] -> 0 <= k -> (forall y, In y Y -> 0 <= r y) ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  tensor_cost (nested_covariance_atoms n beta gamma offset coeff Y S A) <=
    8 * k ^ 3 * weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (fun y => r y ^ 3).
Proof.
  intros HY HS Hk Hr HB.
  set (q := nested_outer_weights n beta gamma offset coeff Y S A).
  assert (Hq : finite_probability q Y) by (apply nested_outer_probability; exact HY).
  set (m := weighted_average q Y r).
  assert (Hm : 0 <= m) by (apply weighted_average_nonnegative; assumption).
  unfold nested_covariance_atoms; fold q.
  rewrite tensor_weighted_join_probability_cost by exact Hq.
  eapply Rle_trans with (weighted_average q Y (fun y => 4 * k ^ 3 * (r y ^ 3 + m * r y ^ 2))).
  - apply weighted_average_monotone; [exact Hq|]; intros y Hy.
    replace (4 * k ^ 3 * (r y ^ 3 + m * r y ^ 2))
      with ((2 * k * r y) * (2 * k * r y) * (k * (r y + m))) by ring.
    apply mixed_trace_atoms_cost_bound.
    + apply nested_inner_probability; exact HS.
    + apply Rmult_le_pos; [lra|apply Hr; exact Hy].
    + apply Rmult_le_pos; [lra|apply Hr; exact Hy].
    + apply Rmult_le_pos; [exact Hk|specialize (Hr y Hy); lra].
    + intros s Hs; apply nested_inner_center_operator_bound; try assumption; apply HB; exact Hy.
    + intros s Hs; apply nested_inner_center_operator_bound; try assumption; apply HB; exact Hy.
    + intros s Hs; apply nested_outer_center_operator_bound; assumption.
  - rewrite weighted_average_scale, weighted_average_add, weighted_average_scale.
    pose proof (weighted_moment_product q Y r Hq Hr) as HP; fold m in HP.
    assert (Hk3 : 0 <= k ^ 3) by (apply pow_le; exact Hk).
    nra.
Qed.

Theorem nested_third_atoms_cost_bound n beta gamma offset coeff Y S (A : matrix n) k r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall y, In y Y -> 0 <= r y) ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  tensor_cost (nested_third_atoms n beta gamma offset coeff Y S A) <=
    10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y (fun y => r y ^ 3).
Proof.
  intros Hbeta Hgamma HY HS Hk Hr HB.
  pose proof (nested_inner_atoms_cost_bound n beta gamma offset coeff Y S A k r HY HS HB) as HI.
  pose proof (nested_covariance_atoms_cost_bound n beta gamma offset coeff Y S A k r HY HS Hk Hr HB) as HC.
  pose proof (nested_outer_atoms_cost_bound n beta gamma offset coeff Y S A k r HY HS Hk Hr HB) as HO.
  set (e := weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y (fun y => r y ^ 3)) in *.
  assert (He : 0 <= e).
  { unfold e; apply weighted_average_nonnegative.
    - apply nested_outer_probability; exact HY.
    - intros y Hy; apply pow_le; apply Hr; exact Hy. }
  assert (Hk3 : 0 <= k ^ 3) by (apply pow_le; exact Hk).
  unfold nested_third_atoms.
  rewrite !tensor_cost_append, !tensor_scale_atoms_cost, !tensor_cost_append,
    tensor_swap23_atoms_cost, tensor_rotate_atoms_cost.
  rewrite (Rabs_pos_eq (gamma ^ 2)) by nra.
  rewrite (Rabs_pos_eq (beta ^ 2)) by nra.
  rewrite (Rabs_left (- beta * gamma)) by nra.
  change (gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y (fun y => r y ^ 3)) with e.
  assert (HA : gamma ^ 2 * tensor_cost (nested_inner_atoms n beta gamma offset coeff Y S A) <=
    gamma ^ 2 * (8 * k ^ 3 * e)) by (apply Rmult_le_compat_l; [nra|exact HI]).
  assert (HBc : (- (- beta * gamma)) *
    (tensor_cost (nested_covariance_atoms n beta gamma offset coeff Y S A) +
      (tensor_cost (nested_covariance_atoms n beta gamma offset coeff Y S A) +
       tensor_cost (nested_covariance_atoms n beta gamma offset coeff Y S A))) <=
    (beta * gamma) * (3 * (8 * k ^ 3 * e))).
  { replace (- (- beta * gamma)) with (beta * gamma) by ring.
    apply Rmult_le_compat_l; [nra|lra]. }
  assert (HZ : beta ^ 2 * tensor_cost (nested_outer_atoms n beta gamma offset coeff Y S A) <=
    beta ^ 2 * (8 * k ^ 3 * e)) by (apply Rmult_le_compat_l; [nra|exact HO]).
  assert (HD : 0 <= k ^ 3 * e * (beta - gamma) ^ 2).
  { apply Rmult_le_pos; [apply Rmult_le_pos; assumption|apply pow2_ge_0]. }
  nra.
Qed.
