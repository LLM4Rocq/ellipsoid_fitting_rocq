From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights Cubic
  MatrixDefinitions MatrixTrace MatrixGibbsDefinitions MatrixThirdDefinitions
  OperatorDefinitions TensorDefinitions TensorNested.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Sums over coordinates of the projective norms of the third derivatives
   of nested soft minimax functions. A projective norm N is an extended
   real; N = EFin (fine N) says that N is finite, and fine N is its value.
   - matrix_nested_projective_real_bound: if the matrices coeff y s are
     symmetric with operator norm at most k * r y, the projective norm of
     matrix_nested_third_derivative is finite, nonnegative and at most
     10 k^3 (beta+gamma)^2 times the outer Gibbs average of r^3.
   - matrix_nested_shared_score_sum_bound and matrix_nested_zero_sum_bound:
     for a family of coordinates i whose inner soft values induce the same
     outer Gibbs law, the sum of these norms is at most
     10 k^3 (beta+gamma)^2 times the Gibbs average of sum_i (r i)^3.
   - matrix_nested_projective_sum_low_influence: when r i z = |y z i| for
     unit vectors y z with entries at most theta / sqrt d, the sum is at
     most 10 k^3 (beta+gamma)^2 theta / sqrt d. *)

Lemma tensor_sum_gibbs_scores_ext c f g Y u :
  (forall y, In y Y -> f y = g y) ->
  gibbs_average c f Y u = gibbs_average c g Y u.
Proof.
  intros H.
  assert (HP : partition c f Y = partition c g Y).
  { unfold partition; apply gibbs_sum_ext; intros y Hy; rewrite (H y Hy); reflexivity. }
  unfold gibbs_average; apply gibbs_sum_ext; intros y Hy.
  unfold gibbs_weight; rewrite HP (H y Hy); reflexivity.
Qed.

Lemma tensor_sum_gibbs_interchange c f I Y u :
  finite_sum (fun i => gibbs_average c f Y (u i)) I =
    gibbs_average c f Y (fun y => finite_sum (fun i => u i y) I).
Proof.
  unfold gibbs_average; rewrite cubic_sum_swap; apply cubic_sum_ext; intros y Hy.
  apply cubic_sum_scale.
Qed.

Lemma matrix_affine_scores_at_zero n H coeff :
  matrix_affine_scores n H coeff (matrix_zero n) = H.
Proof.
  apply functional_extensionality; intros y.
  apply functional_extensionality; intros s; unfold matrix_affine_scores.
  assert (HZ : trace_pair n (coeff y s) (matrix_zero n) = 0).
  { unfold matrix_zero; exact (linear0 (trace_pair n (coeff y s))). }
  rewrite HZ; ring.
Qed.

Lemma matrix_inner_values_at_zero n gamma H coeff S :
  matrix_inner_values n gamma H coeff S (matrix_zero n) =
    (fun y => soft_max gamma (H y) S).
Proof. unfold matrix_inner_values; rewrite matrix_affine_scores_at_zero; reflexivity. Qed.

(* The real projection fine is used only after producing a finite,
   nonnegative witness for the projective norm. *)
Theorem matrix_nested_projective_real_bound n beta gamma H coeff Y S (A : matrix n) k r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall y, In y Y -> 0 <= r y) ->
  (forall y, In y Y -> forall s, In s S -> symmetric_matrix n (coeff y s)) ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  let N := projective_operator_norm (matrix_nested_third_derivative n beta gamma H coeff Y S A) in
  N = EFin (fine N) /\ 0 <= fine N /\
  fine N <= 10 * k ^ 3 * (beta + gamma) ^ 2 *
    gibbs_average (- beta) (matrix_inner_values n gamma H coeff S A) Y (fun y => r y ^ 3).
Proof.
  intros Hb Hg HY HS Hk Hr Hsym Hcap; cbn zeta.
  destruct (matrix_nested_third_projective_finite_bound n beta gamma H coeff Y S A k r
    Hb Hg HY HS Hk Hr Hsym Hcap) as [z [HE [Hz Hbound]]].
  rewrite HE; simpl; auto.
Qed.

(* Every coordinate may have its own matrix coefficients and offsets, but
   the inner soft values at A must induce the same outer Gibbs law. *)
Theorem matrix_nested_shared_score_sum_bound n beta gamma offset coeff I Y S
    (A : matrix n) h k r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall i y, In i I -> In y Y -> 0 <= r i y) ->
  (forall i y s, In i I -> In y Y -> In s S -> symmetric_matrix n (coeff i y s)) ->
  (forall i y s, In i I -> In y Y -> In s S ->
    matrix_operator_norm n (coeff i y s) <= k * r i y) ->
  (forall i y, In i I -> In y Y -> matrix_inner_values n gamma (offset i) (coeff i) S A y = h y) ->
  (forall i, In i I ->
    let N := projective_operator_norm
      (matrix_nested_third_derivative n beta gamma (offset i) (coeff i) Y S A) in
    N = EFin (fine N) /\ 0 <= fine N) /\
  finite_sum (fun i => fine (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma (offset i) (coeff i) Y S A))) I <=
    10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) h Y (fun y => finite_sum (fun i => r i y ^ 3) I).
Proof.
  intros Hb Hg HY HS Hk Hr Hsym Hcap Hshared.
  assert (HP : forall i, In i I ->
    let N := projective_operator_norm
      (matrix_nested_third_derivative n beta gamma (offset i) (coeff i) Y S A) in
    N = EFin (fine N) /\ 0 <= fine N /\
    fine N <= 10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) h Y (fun y => r i y ^ 3)).
  { intros i Hi.
    pose proof (matrix_nested_projective_real_bound n beta gamma (offset i) (coeff i) Y S A k (r i)
      Hb Hg HY HS Hk (fun y Hy => Hr i y Hi Hy)
      (fun y Hy s Hs => Hsym i y s Hi Hy Hs)
      (fun y Hy s Hs => Hcap i y s Hi Hy Hs)) as Hpoint.
    rewrite (tensor_sum_gibbs_scores_ext (- beta)
      (matrix_inner_values n gamma (offset i) (coeff i) S A) h Y
      (fun y => r i y ^ 3) (fun y Hy => Hshared i y Hi Hy)) in Hpoint.
    exact Hpoint. }
  split.
  - intros i Hi; destruct (HP i Hi) as [HE [Hz Hbound]]; split; assumption.
  - eapply Rle_trans with (finite_sum (fun i => 10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) h Y (fun y => r i y ^ 3)) I).
    + apply cubic_sum_le; intros i Hi; exact (proj2 (proj2 (HP i Hi))).
    + rewrite cubic_sum_scale tensor_sum_gibbs_interchange; apply Rle_refl.
Qed.

Theorem matrix_nested_zero_sum_bound n beta gamma H coeff I Y S k r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall i y, In i I -> In y Y -> 0 <= r i y) ->
  (forall i y s, In i I -> In y Y -> In s S -> symmetric_matrix n (coeff i y s)) ->
  (forall i y s, In i I -> In y Y -> In s S ->
    matrix_operator_norm n (coeff i y s) <= k * r i y) ->
  (forall i, In i I ->
    let N := projective_operator_norm
      (matrix_nested_third_derivative n beta gamma H (coeff i) Y S (matrix_zero n)) in
    N = EFin (fine N) /\ 0 <= fine N) /\
  finite_sum (fun i => fine (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma H (coeff i) Y S (matrix_zero n)))) I <=
    10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) (fun y => soft_max gamma (H y) S) Y
        (fun y => finite_sum (fun i => r i y ^ 3) I).
Proof.
  intros Hb Hg HY HS Hk Hr Hsym Hcap.
  apply (matrix_nested_shared_score_sum_bound n beta gamma (fun _ => H) coeff I Y S
    (matrix_zero n) (fun y => soft_max gamma (H y) S) k r); try assumption.
  intros i y Hi Hy; rewrite matrix_inner_values_at_zero; reflexivity.
Qed.

Theorem matrix_nested_projective_sum_low_influence n beta gamma H coeff y I Y S d theta k :
  0 < beta -> 0 < gamma -> 0 <= k -> (1 <= d)%coq_nat -> 0 < theta -> Y <> [] -> S <> [] ->
  (forall z, In z Y -> euclidean_norm (y z) I = 1) ->
  (forall z i, In z Y -> In i I -> Rabs (y z i) <= theta / sqrt (INR d)) ->
  (forall i z s, In i I -> In z Y -> In s S -> symmetric_matrix n (coeff i z s)) ->
  (forall i z s, In i I -> In z Y -> In s S ->
    matrix_operator_norm n (coeff i z s) <= k * Rabs (y z i)) ->
  (forall i, In i I ->
    let N := projective_operator_norm
      (matrix_nested_third_derivative n beta gamma H (coeff i) Y S (matrix_zero n)) in
    N = EFin (fine N) /\ 0 <= fine N) /\
  finite_sum (fun i => fine (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma H (coeff i) Y S (matrix_zero n)))) I <=
    10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR d).
Proof.
  intros Hb Hg Hk Hd Htheta HY HS Hunit Hcap Hsym Hcoeff.
  destruct (matrix_nested_zero_sum_bound n beta gamma H coeff I Y S k (fun i z => Rabs (y z i))
    Hb Hg HY HS Hk (fun _ _ _ _ => Rabs_pos _) Hsym Hcoeff) as [Hfinite Hsum].
  split; [exact Hfinite|].
  eapply Rle_trans; [exact Hsum|].
  replace (10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR d)) with
    ((10 * k ^ 3 * (beta + gamma) ^ 2) * (theta / sqrt (INR d))) by (unfold Rdiv; ring).
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow_le; exact Hk]|apply pow2_ge_0].
  - unfold gibbs_average.
    change (finite_sum (fun z => gibbs_weight (- beta) (fun z => soft_max gamma (H z) S) Y z *
      cubic_mass (y z) I) Y <= theta / sqrt (INR d)).
    apply weighted_cubic_mass_low_influence; try assumption.
    + intros; apply gibbs_weight_nonnegative; exact HY.
    + apply gibbs_weights_normalized; exact HY.
Qed.
