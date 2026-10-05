From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum classical_sets.
From mathcomp Require Import Rstruct topology normedtype derive Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions SoftDefinitions OperatorDefinitions
  TensorDefinitions GaussianProductDefinitions JointDefinitions GoeDefinitions
  RowTimeDefinitions MultirowEndpointDefinitions MaximumRadiusDefinitions
  RowCoordinateDefinitions RowMarginalDefinitions RowArrayDefinitions RowObservableDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianProduct GaussianLastIntegration GaussianFiniteSums
  MaximumRadiusResults InterleavedMaximumRadiusResults
  RowObservableRegularity RowRemainderSum WeightedComparison MultirowIntegratedArithmetic.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Helper for the challenge multirow_integrated_bound: the parts of the
   target that do not depend on the unfinished challenge
   multirow_expectation_derivative, and the assembly of the target from that
   challenge's four clauses, taken as hypotheses. Written by the solving
   session on 30 September 2026. Nothing is assumed: every lemma is proved
   from accepted or checkpoint results of the port, and the clauses of the
   unfinished challenge appear only as hypotheses of the assembly theorems.

   1. multirow_integrated_radius_facts: the domain of the maximum squared
      radius of N rows of d coordinates, its expectation is nonnegative and
      at most d + 2 sqrt (d ln N) + 2 ln N (gaussian_expected_maximum_radius
      of the accepted maximum_radius, and a nonnegativity argument).
   2. multirow_integrated_remainder_sum_bound: under the low-influence
      hypotheses, the sum over the rows of the expectations of the row
      remainders is at most 4 M3 radius in absolute value, with
      M3 = 10 k^3 (beta+gamma)^2 theta / sqrt d: the row remainders are
      regular (RowObservableRegularity), so the expectation of the sum is the
      sum of the expectations (GaussianFiniteSums); the sum is bounded
      pointwise by 4 M3 times the interleaved maximum radius
      (RowRemainderSum); the expectation of the interleaved maximum radius
      is that of the consecutive one (interleaved_maximum_radius).
   3. The assembly: with the derivative identity, the continuity within
      [0, 1] and the endpoint identities as hypotheses, the derivative bound
      of clause 2 and the integrated bounds of clause 3 follow from the
      scalar lemma sqrt_weighted_endpoint_bound (WeightedComparison) and the
      arithmetic of MultirowIntegratedArithmetic. *)

Local Notation Dfull n m :=
  (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat.

Lemma multirow_integrated_sum_squares_ge0 (xs : list R) : 0 <= gaussian_sum_squares xs.
Proof.
  induction xs as [|x xs IH]; simpl; [lra|].
  pose proof (Rle_0_sqr x); unfold Rsqr in *; lra.
Qed.

Lemma multirow_integrated_maximum_radius_ge0 N d (xs : list R) :
  0 <= gaussian_maximum_radius N d xs.
Proof.
  revert xs; induction N as [|k IH]; intros xs; simpl; [lra|].
  apply Rle_trans with (gaussian_maximum_radius k d (skipn d xs)); [apply IH|apply Rmax_r].
Qed.

(* 1. The expected maximum radius over N rows of d consecutive coordinates. *)
Theorem multirow_integrated_radius_facts n m :
  gaussian_list_domain (Datatypes.S m * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)) /\
  0 <= gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)) /\
  gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)) <=
    INR (Datatypes.S n) + 2 * sqrt (INR (Datatypes.S n) * Rpower.ln (INR (Datatypes.S m))) +
      2 * Rpower.ln (INR (Datatypes.S m)).
Proof.
  destruct (gaussian_expected_maximum_radius (Datatypes.S m) (Datatypes.S n)
    ltac:(apply Nat.lt_0_succ) ltac:(apply Nat.lt_0_succ)) as [HI [HA [HE [HEA [_ Hb]]]]].
  split; [split; [exact HI|split; [exact HA|split; [exact HE|exact HEA]]]|].
  split; [|exact Hb].
  apply Rle_trans with (Rabs (gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)))); [apply Rabs_pos|].
  apply (gaussian_iterated_majorant_bound _ _ _ HI HI).
  intros xs _.
  rewrite (Rabs_right _ (Rle_ge _ _ (multirow_integrated_maximum_radius_ge0 _ _ xs))).
  apply Rle_refl.
Qed.

(* 2. The summed remainder expectations are bounded by 4 M3 radius. *)
Theorem multirow_integrated_remainder_sum_bound n m beta gamma theta k y B Y S t :
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k -> Y <> [] -> S <> [] ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  Rabs (finite_sum (fun i => gaussian_iterated_expectation (Dfull n m)
      (gaussian_row_remainder n m beta gamma y B Y S t i)) (List.seq 0 (Datatypes.S m))) <=
    4 * (10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n))) *
      gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
        (gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)).
Proof.
  intros Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB.
  set (c := 40 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n))).
  set (rad := fun xs => gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)
    (row_prefixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) xs)).
  (* regularity of every row remainder *)
  assert (Hreg : forall i, In i (List.seq 0 (Datatypes.S m)) -> exists C,
    finite_joint_continuous (Dfull n m) (gaussian_row_remainder n m beta gamma y B Y S t i) /\
    finite_polynomial_bound (Dfull n m) C 2 (gaussian_row_remainder n m beta gamma y B Y S t i)).
  { intros i Hi; destruct (proj1 (List.in_seq _ _ _) Hi) as [_ Hi'].
    destruct (gaussian_row_observables_regular n m beta gamma y B Y S k t i Hb Hg HY HS Hk
      ltac:(lia) Hunit HB) as [_ [HCR [CV [CR [_ HBR]]]]].
    exists CR; split; assumption. }
  destruct (gaussian_finite_polynomial_sum (Dfull n m) (List.seq 0 (Datatypes.S m))
    (fun i => gaussian_row_remainder n m beta gamma y B Y S t i) 2 Hreg)
    as [_ [_ [_ [[HIsum _] Hsum]]]].
  rewrite -Hsum.
  (* the interleaved maximum radius: domain and expectation *)
  destruct (gaussian_interleaved_expected_maximum_radius (Datatypes.S m) (Datatypes.S n)
    (Datatypes.S (goe_vector_index n)) ltac:(apply Nat.lt_0_succ) ltac:(apply Nat.lt_0_succ))
    as [HIrad [_ [_ [_ [Hradeq _]]]]].
  destruct (gaussian_iterated_scale (Dfull n m) rad c HIrad) as [HIc HEc].
  eapply Rle_trans; [apply (gaussian_iterated_majorant_bound _ _ _ HIsum HIc)|].
  - intros xs HL.
    unfold c, rad.
    apply (gaussian_row_remainder_absolute_sum n m beta gamma y B Y S t theta k xs);
      try assumption.
  - rewrite HEc. unfold rad. rewrite Hradeq. unfold c. right; field.
    apply Rgt_not_eq, sqrt_lt_R0, lt_0_INR, Nat.lt_0_succ.
Qed.

(* 3. The assembly from the four clauses of the expectation-derivative
   challenge, taken as hypotheses. *)
Section assembly.
Variables (n m : nat) (beta gamma theta k : R) (y : nat -> nat -> R) (B : nat -> matrix n) (Y S : list nat).
Hypotheses (Hb : 0 < beta) (Hg : 0 < gamma) (Hth : 0 < theta) (Hk : 0 <= k) (HY : Y <> []) (HS : S <> []).
Hypothesis Hunit : forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1.
Hypothesis Hlow : forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
  Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n)).
Hypothesis Hsym : forall s, In s S -> symmetric_matrix n (B s).
Hypothesis HB : forall s, In s S -> matrix_operator_norm n (B s) <= k.

Let d := INR (Datatypes.S n).
Let radius := gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
  (gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)).
Let M3 := 10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt d.
Let f := fun t => gaussian_iterated_expectation (Dfull n m) (gaussian_array_value n m beta gamma y B Y S t).
Let dg := fun t => (sqrt t / (2 * INR (Datatypes.S n) * sqrt (INR (Datatypes.S n)))) *
  finite_sum (fun i => gaussian_iterated_expectation (Dfull n m)
    (gaussian_row_remainder n m beta gamma y B Y S t i)) (List.seq 0 (Datatypes.S m)).

Let d_pos : 0 < d. Proof. apply lt_0_INR, Nat.lt_0_succ. Qed.
Let radius_nonneg : 0 <= radius.
Proof. exact (proj1 (proj2 (multirow_integrated_radius_facts n m))). Qed.
Let M3_nonneg : 0 <= M3.
Proof.
  unfold M3; apply Rmult_le_pos; [|left; apply Rinv_0_lt_compat, sqrt_lt_R0, d_pos].
  apply Rmult_le_pos; [|lra]. apply Rmult_le_pos; [|apply pow2_ge_0].
  apply Rmult_le_pos; [lra|apply pow_le; exact Hk].
Qed.

(* The derivative value is bounded by (2 sqrt t / (d sqrt d)) radius M3. *)
Lemma multirow_integrated_dg_bound t : 0 <= t ->
  Rabs (dg t) <= (2 * sqrt t / (d * sqrt d)) * radius * M3.
Proof.
  intros Ht; unfold dg.
  apply (multirow_integrated_derivative_bound d t radius M3 _ d_pos Ht radius_nonneg M3_nonneg).
  unfold M3, d.
  exact (multirow_integrated_remainder_sum_bound n m beta gamma theta k y B Y S t
    Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB).
Qed.

Lemma multirow_integrated_dg_bound_K t : 0 <= t ->
  Rabs (dg t) <= (2 * radius * M3 / (d * sqrt d)) * sqrt t.
Proof.
  intros Ht; unfold dg.
  apply (multirow_integrated_derivative_bound_K d t radius M3 _ d_pos Ht radius_nonneg M3_nonneg).
  unfold M3, d.
  exact (multirow_integrated_remainder_sum_bound n m beta gamma theta k y B Y S t
    Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB).
Qed.

(* Clause 2 of the target, given the derivative identity of the
   expectation-derivative challenge. *)
Theorem multirow_integrated_clause2_of_derivative :
  (forall a, 0 < a < 1 -> @is_derive R R^o R^o a 1 f (dg a)) ->
  forall t, 0 < t < 1 -> exists l : R,
    @is_derive R R^o R^o t 1 f l /\ Rabs l <= (2 * sqrt t / (d * sqrt d)) * radius * M3.
Proof.
  intros Hder t Ht; exists (dg t); split; [apply Hder; exact Ht|].
  apply multirow_integrated_dg_bound; lra.
Qed.

(* Clause 3 of the target, given the endpoint clause and the continuity
   clause of the expectation-derivative challenge. *)
Theorem multirow_integrated_clause3_of_endpoints (g w : R) :
  (forall a, 0 < a < 1 -> @is_derive R R^o R^o a 1 f (dg a)) ->
  (f @ within (fun t : R => 0 <= t <= 1) (nbhs (0 : R)) --> f 0)%classic ->
  (f @ within (fun t : R => 0 <= t <= 1) (nbhs (1 : R)) --> f 1)%classic ->
  f 0 = g -> f 1 = w ->
  Rabs (w - g) <= (4 * radius / (3 * d * sqrt d)) * M3 /\
  Rabs (w - g) <= (40 / 3) * k ^ 3 * (beta + gamma) ^ 2 * theta *
    (d + 2 * sqrt (d * Rpower.ln (INR (Datatypes.S m))) + 2 * Rpower.ln (INR (Datatypes.S m))) / d ^ 2.
Proof.
  intros Hder H0 H1 Hf0 Hf1.
  assert (Hmain : Rabs (w - g) <= (4 * radius / (3 * d * sqrt d)) * M3).
  { rewrite -Hf0 -Hf1 -(multirow_integrated_two_thirds d radius M3 d_pos).
    apply (sqrt_weighted_endpoint_bound f dg (2 * radius * M3 / (d * sqrt d))); try assumption.
    - apply multirow_integrated_K_nonneg; [exact d_pos|exact radius_nonneg|exact M3_nonneg].
    - intros t Ht; apply multirow_integrated_dg_bound_K; lra. }
  split; [exact Hmain|].
  eapply Rle_trans; [exact Hmain|].
  unfold M3; apply multirow_integrated_explicit_constant; try assumption.
  exact (proj2 (proj2 (multirow_integrated_radius_facts n m))).
Qed.
End assembly.
