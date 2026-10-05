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

(* Port of the inner module JointSections of theories/InterpolationProofs.v
   (also copied in theories/JointProofs.v), extracted to
   build/agent2/unbundled/JointSections.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundles QuadraticGaussianProofs and GoeProofs
   and named their inner modules QuadraticGaussianTime and GoeGibbs through
   them. The port imports these two standalone ported modules directly.

   The three statements keep their names, their arguments in the same order,
   their hypotheses and their text. No item is added.
   joint_matrix_quadratic_section is an identity between matrices and means
   the same as before. joint_quadratic_section_stein and
   joint_goe_section_stein change meaning only through the ported
   definitions they mention: gaussian_vector_domain and
   gaussian_vector_expectation follow the ported GaussianVectorDefinitions
   (difference 4 of analysis/README.md), that is Borel measurability and
   Lebesgue integrability against the Gaussian kernel at each level of the
   iterated expectation, and Lebesgue integrals. The sections are continuous
   and bounded by a polynomial, as the ported QuadraticGaussianTime and
   GoeGibbs use, so both readings of the domain hold and the values agree.
   Their text is that of the two clauses of the group "Fixed-section
   quadratic and GOE identities with full domains" of the restated challenge
   analysis/challenges/ellipsoid_joint/Challenge.v.

   The proofs are the original ones. Stdlib's "rewrite A, B" and
   "rewrite ... by tac" are written in the form that ssreflect accepts. *)

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
