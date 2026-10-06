From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  NormEquivalence TensorDefinitions GradientDefinitions MatrixGradient
  MatrixThirdDefinitions MatrixThird HessianDefinitions MatrixHessian
  SecondChaosDefinitions SecondChaosAlgebra SymmetricDefinitions SymmetricDivergence
  QuadraticDefinitions QuadraticCalculus QuadraticGradient QuadraticSymmetry.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* The second derivative in x of the nested gradient at
   quadratic_matrix n lambda C x = C + lambda (x x^T - I), summed over the
   coordinate directions. When every coefficient matrix coeff y s is
   symmetric, quadratic_gradient_second_sum states that the sum over a and
   b of the entries (a, b) of quadratic_gradient_second along the basis
   vectors chaos_basis n a and chaos_basis n b is
   2 * lambda * symmetric_divergence of the derivative of the gradient plus
   lambda ^ 2 * chaos_contraction of the third derivative with x, both at
   quadratic_matrix n lambda C x. quadratic_gradient_second_contraction
   identifies the second part. The proof uses symmetric_divergence_identity,
   with the linearity of the derivative of matrix_nested_gradient from
   matrix_third_is_diff_linear of MatrixThird. *)

Lemma quadratic_double_sum_scale n c f :
  coordinate_sum n (fun a => coordinate_sum n (fun b => c * f a b)) =
  c * coordinate_sum n (fun a => coordinate_sum n (f a)).
Proof.
  transitivity (coordinate_sum n (fun a => c * coordinate_sum n (f a))).
  - apply coordinate_sum_ext; intros; apply normeq_coordinate_sum_scale.
  - apply normeq_coordinate_sum_scale.
Qed.

Theorem quadratic_gradient_second_contraction n beta gamma offset coeff Y S (A : matrix n) (x : vector n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    matrix_entry n
      (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A
        (chaos_first n x a) (chaos_first n x b)) a b)) =
  chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S A) x.
Proof.
  intros Hb Hg HY HS HC; unfold chaos_contraction; rewrite <- quadratic_double_sum_scale.
  apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hbnd.
  pose proof (matrix_nested_gradient_second_trace n beta gamma offset coeff Y S A
    (chaos_first n x a) (chaos_first n x b) (chaos_second n a b) Hb Hg HY HS) as HT.
  rewrite (trace_pair_chaos_second n _ a b
    (quadratic_nested_gradient_second_symmetric n beta gamma offset coeff Y S A
      (chaos_first n x a) (chaos_first n x b) Hb Hg HY HS HC) Ha Hbnd) in HT.
  rewrite (matrix_nested_third_swap_left n beta gamma offset coeff Y S A
    (chaos_second n a b) (chaos_first n x a) (chaos_first n x b)) in HT.
  rewrite (matrix_nested_third_swap_right n beta gamma offset coeff Y S A
    (chaos_first n x a) (chaos_second n a b) (chaos_first n x b)) in HT.
  lra.
Qed.

(* This is the deterministic identity used before Gaussian integration by
   parts.  No expectation or integration identity is assumed here. *)
Theorem quadratic_gradient_second_sum n beta gamma offset coeff Y S lambda C (x : vector n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    matrix_entry n
      (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x
        (chaos_basis n a) (chaos_basis n b)) a b)) =
  2 * lambda * symmetric_divergence n
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)) +
  lambda ^ 2 * chaos_contraction n
    (matrix_nested_third_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)) x.
Proof.
  intros Hb Hg HY HS HC.
  transitivity (coordinate_sum n (fun a => coordinate_sum n (fun b =>
    lambda * matrix_entry n
      (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)
        (chaos_second n a b)) a b +
    lambda ^ 2 * matrix_entry n
      (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)
        (chaos_first n x a) (chaos_first n x b)) a b))).
  - apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hbnd.
    rewrite (quadratic_gradient_second_basis n beta gamma offset coeff Y S lambda C x a b
      Hb Hg HY HS).
    rewrite matrix_entry_add !matrix_entry_scale; reflexivity.
  - rewrite symmetric_double_sum_add !quadratic_double_sum_scale.
    rewrite (symmetric_divergence_identity n
      (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x))
      (matrix_third_is_diff_linear _ _ _
        (matrix_nested_gradient_frechet n beta gamma offset coeff Y S Hb Hg HY HS
          (quadratic_matrix n lambda C x)))).
    rewrite (quadratic_gradient_second_contraction n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) x Hb Hg HY HS HC); ring.
Qed.
