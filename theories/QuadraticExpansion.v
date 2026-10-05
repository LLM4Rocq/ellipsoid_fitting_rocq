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

(* Port of theories/QuadraticExpansion.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. No lemma is added. One statement changes form, in the way of
   the ports of QuadraticGradient and MatrixCoordinates, which this module
   imports, and of the restated challenge ellipsoid_quadratic in
   analysis/challenges (its conjunct 2c).

   1. Frechet derivatives. In quadratic_entry_second_frechet, Coquelicot's
      filterdiff f (locally x) l becomes is_diff x f l of MathComp-Analysis:
      f is differentiable at x and its differential 'd f x is l. Both say
      that l is linear and continuous and that f (x + h) = f x + l h + o(h)
      as h tends to 0. The space vector n is the one of the port of
      OperatorDefinitions, which keeps Coquelicot's Euclidean norm, so the
      neighbourhoods are those of the original. The map is real-valued, and
      is typed into R^o, the normed module view of R, whose norm is the
      absolute value like the norm of Coquelicot's R_NormedModule. R^o is R
      by definition, so the map is the same.

   quadratic_double_sum_scale, quadratic_gradient_second_contraction,
   quadratic_gradient_second_sum and quadratic_gradient_time_sum mention no
   normed notion, and their text is the original's.

   In the proofs, filterdiff_comp' with filterdiff_linear of
   matrix_entry_linear becomes is_diff_comp with matrix_entry_frechet of
   MatrixCoordinates. The linearity and the bound of the derivative of
   matrix_nested_gradient, which the original takes from proj1 of
   Coquelicot's filterdiff to feed symmetric_divergence_identity, come from
   matrix_third_is_diff_linear of MatrixThird. Stdlib's "rewrite A, B" and
   "rewrite ... by tac" are written in the forms that ssreflect accepts. *)

Theorem quadratic_entry_second_frechet n beta gamma offset coeff Y S lambda C
    (x : vector n) a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff x
    ((fun z => matrix_entry n
      (quadratic_gradient_first n beta gamma offset coeff Y S lambda C z (chaos_basis n a)) a b)
      : vector n -> R^o)
    (fun v => matrix_entry n
      (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x (chaos_basis n a) v) a b).
Proof.
  intros Hb Hg HY HS.
  exact (is_diff_comp
    (quadratic_gradient_first_frechet n beta gamma offset coeff Y S lambda C x
      (chaos_basis n a) Hb Hg HY HS)
    (matrix_entry_frechet n
      (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x (chaos_basis n a))
      a b)).
Qed.

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

Theorem quadratic_gradient_time_sum n beta gamma offset coeff Y S t C (x : vector n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= t ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  / sqrt (INR (Datatypes.S n)) *
    coordinate_sum n (fun a => coordinate_sum n (fun b =>
      matrix_entry n
        (quadratic_gradient_second n beta gamma offset coeff Y S
          (sqrt (t / INR (Datatypes.S n))) C x (chaos_basis n a) (chaos_basis n b)) a b)) =
  (2 * sqrt t / INR (Datatypes.S n)) * symmetric_divergence n
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x)) +
  (t / (INR (Datatypes.S n) * sqrt (INR (Datatypes.S n)))) * chaos_contraction n
    (matrix_nested_third_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x)) x.
Proof.
  intros Hb Hg HY HS Ht HC.
  rewrite (quadratic_gradient_second_sum n beta gamma offset coeff Y S
    (sqrt (t / INR (Datatypes.S n))) C x Hb Hg HY HS HC).
  set (D := symmetric_divergence n
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x))).
  set (Rc := chaos_contraction n
    (matrix_nested_third_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x)) x).
  assert (Hd : 0 < INR (Datatypes.S n)) by (apply lt_0_INR; lia).
  assert (Hds : 0 < sqrt (INR (Datatypes.S n))) by (apply sqrt_lt_R0; exact Hd).
  rewrite (sqrt_div t (INR (Datatypes.S n)) Ht Hd).
  pose proof (sqrt_def t Ht) as Htsq.
  pose proof (sqrt_def (INR (Datatypes.S n)) (Rlt_le _ _ Hd)) as Hdsq.
  field_simplify.
  - rewrite (pow2_sqrt t Ht).
    replace (sqrt (INR (Datatypes.S n)) ^ 3) with
      (sqrt (INR (Datatypes.S n)) * (sqrt (INR (Datatypes.S n)) * sqrt (INR (Datatypes.S n)))) by ring.
    rewrite Hdsq; f_equal; ring.
  - split; lra.
  - lra.
Qed.
