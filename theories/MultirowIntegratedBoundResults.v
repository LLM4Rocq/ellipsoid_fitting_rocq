(* Results module of the draft challenge multirow_integrated_bound, over the
   MathComp-Analysis port in analysis/. Nothing here is reviewed, solved or
   accepted: the challenge is a draft of the port, and this module is a
   pre-submission proof written on 30 September 2026 by a session that did
   not write the statement.

   The imports before the proof modules are those of
   analysis/challenges/multirow_integrated_bound/Challenge.v, in the same
   order, and the statement below is the text of that file, copied unchanged
   (SHA-256 of Challenge.v:
   0c7e86e61e03c24b51cb1017f2de854a935110f642849c7aca39362ec8fcce5f).

   The proof composes three sources. The radius facts of clause 1 and the
   bound 4 M3 radius on the summed remainder expectations are
   MultirowIntegratedBounds (from the accepted maximum_radius and
   interleaved_maximum_radius and the checkpoint remainder sum). The domain
   of the array value on [0, 1], the derivative of its expectation on (0, 1)
   with the value sqrt t / (2 d sqrt d) times the summed remainder
   expectations, its continuity within [0, 1], and the endpoint identities
   with their domains are the per-clause theorems of
   MultirowExpectationAssembly, the assembly module of the proved challenge
   multirow_expectation_derivative. The integration in time is the scalar
   lemma sqrt_weighted_endpoint_bound of WeightedComparison, applied inside
   MultirowIntegratedBounds with K = 2 radius M3 / (d sqrt d), and the
   explicit constant 40/3 is MultirowIntegratedArithmetic. *)
From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum classical_sets.
From mathcomp Require Import Rstruct topology normedtype derive Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions SoftDefinitions OperatorDefinitions
  TensorDefinitions GaussianProductDefinitions JointDefinitions GoeDefinitions
  RowTimeDefinitions MultirowEndpointDefinitions MaximumRadiusDefinitions.
From Stdlib Require Import Lra.
From EllipsoidFitting Require Import MultirowIntegratedArithmetic MultirowIntegratedBounds.
From EllipsoidFitting Require MultirowExpectationAssembly.
Import ListNotations.
Open Scope R_scope.

Theorem paper_multirow_integrated_bound_results :
(forall (n m : nat) (beta gamma theta k : R) (y : nat -> nat -> R)
    (B : nat -> matrix n) (Y S : list nat),
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k -> Y <> [] -> S <> [] ->
  (forall z, In z Y ->
    euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  let D := (N * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat in
  let radius := gaussian_iterated_expectation (N * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius N (Datatypes.S n)) in
  let radius_bound := d + 2 * sqrt (d * Rpower.ln (INR N)) + 2 * Rpower.ln (INR N) in
  let M3 := 10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt d in
  let f := fun t => gaussian_iterated_expectation D
    (gaussian_array_value n m beta gamma y B Y S t) in
  gaussian_list_domain (N * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius N (Datatypes.S n)) /\
  0 <= radius /\ radius <= radius_bound /\
  (forall t, 0 <= t <= 1 ->
    gaussian_list_domain D (gaussian_array_value n m beta gamma y B Y S t))) /\
(forall (n m : nat) (beta gamma theta k : R) (y : nat -> nat -> R)
    (B : nat -> matrix n) (Y S : list nat),
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k -> Y <> [] -> S <> [] ->
  (forall z, In z Y ->
    euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  let D := (N * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat in
  let radius := gaussian_iterated_expectation (N * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius N (Datatypes.S n)) in
  let radius_bound := d + 2 * sqrt (d * Rpower.ln (INR N)) + 2 * Rpower.ln (INR N) in
  let M3 := 10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt d in
  let f := fun t => gaussian_iterated_expectation D
    (gaussian_array_value n m beta gamma y B Y S t) in
  forall t, 0 < t < 1 -> exists l : R,
  @is_derive R R^o R^o t 1 f l /\
  Rabs l <= (2 * sqrt t / (d * sqrt d)) * radius * M3) /\
(forall (n m : nat) (beta gamma theta k : R) (y : nat -> nat -> R)
    (B : nat -> matrix n) (Y S : list nat),
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k -> Y <> [] -> S <> [] ->
  (forall z, In z Y ->
    euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  let D := (N * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat in
  let radius := gaussian_iterated_expectation (N * Datatypes.S n)%coq_nat
    (gaussian_maximum_radius N (Datatypes.S n)) in
  let radius_bound := d + 2 * sqrt (d * Rpower.ln (INR N)) + 2 * Rpower.ln (INR N) in
  let M3 := 10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt d in
  let f := fun t => gaussian_iterated_expectation D
    (gaussian_array_value n m beta gamma y B Y S t) in
  let DG := (N * Datatypes.S (goe_vector_index n))%coq_nat in
  let DW := (N * Datatypes.S n)%coq_nat in
  let g := gaussian_iterated_expectation DG
    (multirow_goe_value n m beta gamma y B Y S) in
  let w := gaussian_iterated_expectation DW
    (multirow_quadratic_value n m beta gamma y B Y S) in
  gaussian_list_domain DG (multirow_goe_value n m beta gamma y B Y S) /\
  gaussian_list_domain DW (multirow_quadratic_value n m beta gamma y B Y S) /\
  Rabs (w - g) <= (4 * radius / (3 * d * sqrt d)) * M3 /\
  Rabs (w - g) <= (40 / 3) * k ^ 3 * (beta + gamma) ^ 2 * theta *
    radius_bound / d ^ 2).
Proof.
  split; [|split].
  - intros n m beta gamma theta k y B Y S Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB.
    intros d N D radius radius_bound M3 f.
    destruct (multirow_integrated_radius_facts n m) as [Hdom [Hr0 Hrb]].
    split; [exact Hdom|]. split; [exact Hr0|]. split; [exact Hrb|].
    intros t Ht.
    exact (MultirowExpectationAssembly.mexp_clause_domain n m beta gamma y B Y S t Hb Hg HY HS Ht).
  - intros n m beta gamma theta k y B Y S Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB.
    intros d N D radius radius_bound M3 f t Ht.
    refine (multirow_integrated_clause2_of_derivative n m beta gamma theta k y B Y S
      Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB _ t Ht).
    intros a Ha.
    exact (proj2 (proj2 (proj2 (proj2
      (MultirowExpectationAssembly.mexp_clause_derivative n m beta gamma y B Y S a Hb Hg HY HS Hsym Ha))))).
  - intros n m beta gamma theta k y B Y S Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB.
    intros d N D radius radius_bound M3 f DG DW g w.
    destruct (MultirowExpectationAssembly.mexp_clause_endpoints n m beta gamma y B Y S Hb Hg HY HS)
      as [HdomG [HdomW [Hf0 [Hf1 _]]]].
    split; [exact HdomG|]. split; [exact HdomW|].
    refine (multirow_integrated_clause3_of_endpoints n m beta gamma theta k y B Y S
      Hb Hg Hth Hk HY HS Hunit Hlow Hsym HB g w _ _ _ Hf0 Hf1).
    + intros a Ha.
      exact (proj2 (proj2 (proj2 (proj2
        (MultirowExpectationAssembly.mexp_clause_derivative n m beta gamma y B Y S a Hb Hg HY HS Hsym Ha))))).
    + exact (MultirowExpectationAssembly.mexp_value_expectation_continuous n m beta gamma y B Y S 0
        Hb Hg HY HS ltac:(lra)).
    + exact (MultirowExpectationAssembly.mexp_value_expectation_continuous n m beta gamma y B Y S 1
        Hb Hg HY HS ltac:(lra)).
Qed.
