From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Matrix.OperatorDefinitions
  Matrix.OperatorNormProperties Tensor.Definitions Matrix.SymmetricBasis
  Soft.Definitions Gibbs.MatrixDefinitions Gibbs.MatrixFrechet
  Gibbs.NestedGradientDefinitions Gibbs.MatrixNestedGradient Goe.Definitions
  Goe.MatrixBasis Joint.Definitions Joint.UniformBounds Joint.ObservableGrowth
  Joint.TimeVelocity Joint.PathTimeDerivative.
Import ListNotations.
Open Scope R_scope.

(* Time increments of the interpolation path joint_matrix n C t x z, which
   is C + sqrt t * joint_quadratic_input n x + sqrt (1-t) * goe_matrix n z
   for t >= 0.
   - joint_matrix_path_difference: for s, t >= 0, the path at t minus the
     path at s is (sqrt t - sqrt s) * joint_quadratic_input n x plus
     (sqrt (1-t) - sqrt (1-s)) * goe_matrix n z.
   - joint_matrix_path_difference_bound: the Frobenius norm of this
     difference is at most an explicit constant times
     (|sqrt t - sqrt s| + |sqrt (1-t) - sqrt (1-s)|) * (1 + `|q|) ^ 2,
     where q = (x, z) is the joint vector, with the Euclidean norm of all
     its coordinates. *)

(* A norm is nonnegative, stated with Stdlib's order. *)
Local Ltac joint_norm_nonneg := apply/RleP; apply normr_ge0.

Lemma joint_matrix_path_difference n C s t x z : 0 <= s -> 0 <= t ->
  matrix_add n (joint_matrix n C t x z) (matrix_scale n (-1) (joint_matrix n C s x z)) =
  matrix_add n
    (matrix_scale n (sqrt t - sqrt s) (joint_quadratic_input n x))
    (matrix_scale n (sqrt (1-t) - sqrt (1-s)) (goe_matrix n z)).
Proof.
  intros Hs Ht.
  rewrite (joint_matrix_normalized_path n C t x z Ht)
    (joint_matrix_normalized_path n C s x z Hs).
  apply matrix_ext; intros i j Hi Hj;
    repeat first [rewrite matrix_entry_add | rewrite matrix_entry_scale]; ring.
Qed.

Lemma joint_matrix_path_difference_bound n C s t
  (q : euclidean_product (vector_NormedModule n)
    (vector_NormedModule (goe_vector_index n))) : 0 <= s -> 0 <= t ->
  (`|matrix_add n (joint_matrix n C t (fst q) (snd q))
    (matrix_scale n (-1) (joint_matrix n C s (fst q) (snd q)))|)%R <=
  (INR (S n)^2 * Rabs (/sqrt (INR (S n))) +
    goe_scale n * INR (S (goe_vector_index n))) *
  (Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) * (1+(`|q|)%R)^2.
Proof.
  intros Hs Ht.
  set (CW := INR (S n)^2 * Rabs (/sqrt (INR (S n)))).
  set (CZ := goe_scale n * INR (S (goe_vector_index n))).
  assert (HW : 0 <= CW) by (unfold CW; apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos]).
  assert (HZ : 0 <= CZ).
  { unfold CZ; apply Rmult_le_pos; [pose proof (goe_scale_positive n); lra|apply pos_INR]. }
  assert (Hq : 0 <= (`|q|)%R) by joint_norm_nonneg.
  assert (Hx : 0 <= (`|fst q|)%R) by joint_norm_nonneg.
  assert (Hz : 0 <= (`|snd q|)%R) by joint_norm_nonneg.
  assert (Hxq : (`|fst q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_fst).
  assert (Hzq : (`|snd q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_snd).
  assert (HWB : (`|joint_quadratic_input n (fst q)|)%R <= (CW+CZ)*(1+(`|q|)%R)^2).
  { eapply Rle_trans; [apply joint_quadratic_input_norm|].
    fold CW; apply Rmult_le_compat; [exact HW|apply pow2_ge_0|lra|nra]. }
  assert (HZB : (`|goe_matrix n (snd q)|)%R <= (CW+CZ)*(1+(`|q|)%R)^2).
  { eapply Rle_trans; [apply goe_matrix_norm_bound|].
    fold CZ; apply Rmult_le_compat; [exact HZ|exact Hz|lra|nra]. }
  rewrite (joint_matrix_path_difference n C s t (fst q) (snd q) Hs Ht).
  unfold matrix_add, matrix_scale.
  eapply Rle_trans; [apply/RleP; apply ler_normD|].
  rewrite (real_norm_scal_exact (sqrt t - sqrt s))
    (real_norm_scal_exact (sqrt (1-t) - sqrt (1-s))).
  eapply Rle_trans.
  - apply Rplus_le_compat; apply Rmult_le_compat_l; try apply Rabs_pos; eassumption.
  - right; ring.
Qed.
