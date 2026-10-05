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

(* Port of theories/TensorSum.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. No lemma is added. The first four lemmas keep the text
   of the original: they mention only definitions of the ported modules,
   Stdlib's arithmetic, lists and In, whose meaning the ports keep.

   The four theorems use Coquelicot's extended reals. As in the ports of
   TensorDefinitions and TensorNested, and in the restatement of the
   challenge ellipsoid_tensor_sum in analysis/challenges, Rbar becomes
   MathComp's \bar R, Finite becomes EFin and real becomes fine. real and
   fine both return the real value of a finite argument and 0 on the two
   infinite values. So N = EFin (fine N) says that N is finite, as
   N = Finite (real N) did, and fine N is the same real as real N was. The
   prefix forms EFin and fine are used, not the notation x%:E, so that the
   bounds keep Stdlib's arithmetic.

   One change of notation: with ssreflect loaded, (1 <= d)%nat would mean
   ssrnat's boolean leq. The original means Stdlib's Peano order le, so
   matrix_nested_projective_sum_low_influence writes (1 <= d)%coq_nat,
   ssrnat's notation for Stdlib's le, as the restated challenge does. The
   meaning is unchanged.

   The proofs follow the original. matrix_affine_scores_at_zero used
   Coquelicot's linear_zero on is_linear; here trace_pair n B is a linear map
   of MathComp by the instance of the port of MatrixTrace, and linear0 gives
   the same identity. Stdlib's "rewrite A, B" and "rewrite ... by tac" are
   written in the forms that ssreflect accepts. *)

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

(* The real projection is used only after producing a finite, nonnegative
   witness for the projective norm.  Finite and real of the original become
   EFin and fine; see the comment at the top of the file. *)
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

(* (1 <= d)%nat of the original is written (1 <= d)%coq_nat, Stdlib's le;
   see the comment at the top of the file. *)
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
