From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  TensorDefinitions QuadraticDefinitions GradientDefinitions MatrixThirdDefinitions
  SecondChaosDefinitions SymmetricDefinitions GaussianVectorDefinitions GoeDefinitions
  JointDefinitions QuadraticGaussianTime GoeGibbs.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Gaussian integration by parts in each of the two independent inputs of
   joint_matrix n C t x z = C + sqrt (t / (n + 1)) (x x^T - I)
   + sqrt (1 - t) goe_matrix n z (JointDefinitions). For fixed z, the
   joint matrix is quadratic_matrix in x (joint_matrix_quadratic_section),
   and joint_quadratic_section_stein expresses the expectation in x of
   joint_quadratic_trace through those of joint_divergence and
   joint_remainder. For fixed x, joint_goe_section_stein: the expectation
   in z of joint_goe_trace is 2 sqrt (1 - t) / (n + 1) times that of
   joint_divergence. Both theorems also show that the functions they
   integrate satisfy gaussian_vector_domain. *)

Lemma joint_matrix_quadratic_section n C t x z :
  joint_matrix n C t x z =
    quadratic_matrix n (sqrt (t / INR (S n)))
      (matrix_add n C (matrix_scale n (sqrt (1-t)) (goe_matrix n z))) x.
Proof.
  unfold joint_matrix, quadratic_matrix; apply matrix_ext; intros i j Hi Hj.
  rewrite !matrix_entry_add.
  rewrite (matrix_entry_build n _ i j Hi Hj) (matrix_entry_build n _ i j Hi Hj).
  rewrite !matrix_entry_add.
  ring.
Qed.

Theorem joint_quadratic_section_stein n beta gamma offset coeff Y S C t z :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= t ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  List.Forall (gaussian_vector_domain n)
    [(fun x => joint_quadratic_trace n beta gamma offset coeff Y S C t x z);
     (fun x => joint_divergence n beta gamma offset coeff Y S C t x z);
     (fun x => joint_remainder n beta gamma offset coeff Y S C t x z)] /\
  gaussian_vector_expectation n (fun x => joint_quadratic_trace n beta gamma offset coeff Y S C t x z) =
    (2 * sqrt t / INR (Datatypes.S n)) *
      gaussian_vector_expectation n (fun x => joint_divergence n beta gamma offset coeff Y S C t x z) +
    (t / (INR (Datatypes.S n) * sqrt (INR (Datatypes.S n)))) *
      gaussian_vector_expectation n (fun x => joint_remainder n beta gamma offset coeff Y S C t x z).
Proof.
  intros Hb Hg HY HS Ht HC.
  assert (HP : (fun x => joint_quadratic_trace n beta gamma offset coeff Y S C t x z) =
    (fun x => trace_pair n (joint_quadratic_input n x)
      (quadratic_gradient n beta gamma offset coeff Y S (sqrt (t / INR (Datatypes.S n)))
        (matrix_add n C (matrix_scale n (sqrt (1-t)) (goe_matrix n z))) x))).
  { apply functional_extensionality; intro x.
    unfold joint_quadratic_trace, quadratic_gradient; rewrite joint_matrix_quadratic_section; reflexivity. }
  assert (HD : (fun x => joint_divergence n beta gamma offset coeff Y S C t x z) =
    (fun x => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n)))
        (matrix_add n C (matrix_scale n (sqrt (1-t)) (goe_matrix n z))) x)))).
  { apply functional_extensionality; intro x.
    unfold joint_divergence; rewrite joint_matrix_quadratic_section; reflexivity. }
  assert (HR : (fun x => joint_remainder n beta gamma offset coeff Y S C t x z) =
    (fun x => chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n)))
        (matrix_add n C (matrix_scale n (sqrt (1-t)) (goe_matrix n z))) x)) x)).
  { apply functional_extensionality; intro x.
    unfold joint_remainder; rewrite joint_matrix_quadratic_section; reflexivity. }
  rewrite HP HD HR.
  exact (quadratic_gaussian_time_stein n beta gamma offset coeff Y S t
    (matrix_add n C (matrix_scale n (sqrt (1-t)) (goe_matrix n z))) Hb Hg HY HS Ht HC).
Qed.

Theorem joint_goe_section_stein n beta gamma offset coeff Y S C t x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  List.Forall (gaussian_vector_domain (goe_vector_index n))
    [(fun z => joint_goe_trace n beta gamma offset coeff Y S C t x z);
     (fun z => joint_divergence n beta gamma offset coeff Y S C t x z)] /\
  gaussian_vector_expectation (goe_vector_index n)
    (fun z => joint_goe_trace n beta gamma offset coeff Y S C t x z) =
    (2 * sqrt (1-t) / INR (Datatypes.S n)) *
      gaussian_vector_expectation (goe_vector_index n)
        (fun z => joint_divergence n beta gamma offset coeff Y S C t x z).
Proof.
  intros Hb Hg HY HS.
  unfold joint_goe_trace, joint_divergence, joint_matrix.
  exact (goe_gibbs_matrix_stein n beta gamma offset coeff Y S
    (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x)
    (sqrt (1-t)) Hb Hg HY HS).
Qed.
