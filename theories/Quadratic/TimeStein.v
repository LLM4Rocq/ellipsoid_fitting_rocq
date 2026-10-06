From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions Tensor.Definitions
  Gibbs.NestedGradientDefinitions Gibbs.MatrixThirdDerivativeDefinitions
  Chaos.SecondOrderDefinitions Matrix.SymmetricBasisDefinitions
  Quadratic.Definitions Quadratic.GradientSecondContraction
  Gaussian.Vector.Definitions Gaussian.Vector.Domain Gaussian.Vector.Linearity
  Gaussian.Vector.FiniteSums Quadratic.GaussianMatrixStein.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* The Gaussian integration by parts identity of Quadratic.GaussianMatrixStein at
   time t. Let x be a standard Gaussian vector of dimension d = n + 1, and
   M x = quadratic_matrix n (sqrt (t / d)) C x = C + sqrt (t / d) (x x^T - I).
   If 0 < beta, 0 < gamma, Y and S are nonempty, the coefficient matrices
   are symmetric and 0 <= t, then the expectation of the trace pairing of
   (x x^T - I) / sqrt d with the gradient of the nested Gibbs function at
   M x is 2 sqrt t / d times that of symmetric_divergence of its derivative
   at M x, plus t / (d sqrt d) times that of chaos_contraction of its third
   derivative at M x, and the three functions are in the Gaussian domain
   (quadratic_gaussian_time_stein). The proof rescales
   quadratic_gaussian_matrix_stein, the case lambda = sqrt (t / d)
   (quadratic_centered_trace_scale, quadratic_gaussian_time_coefficients). *)

Lemma quadratic_centered_trace_scale n c (A : matrix n) (x : vector n) :
  trace_pair n (quadratic_matrix n c (matrix_zero n) x) A =
    c * trace_pair n (quadratic_matrix n 1 (matrix_zero n) x) A.
Proof.
  unfold trace_pair; rewrite <- quadratic_double_sum_scale.
  apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hb.
  unfold quadratic_matrix.
  rewrite (matrix_entry_build n _ a b Ha Hb) (matrix_entry_build n _ a b Ha Hb).
  rewrite matrix_entry_zero; ring.
Qed.

Lemma quadratic_gaussian_time_coefficients n t D R :
  0 <= t ->
  / sqrt (INR (S n)) * (2 * sqrt (t / INR (S n)) * D +
    sqrt (t / INR (S n)) ^ 2 * R) =
  (2 * sqrt t / INR (S n)) * D +
    (t / (INR (S n) * sqrt (INR (S n)))) * R.
Proof.
  intro Ht.
  assert (Hd : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (Hds : 0 < sqrt (INR (S n))) by (apply sqrt_lt_R0; exact Hd).
  rewrite (sqrt_div t (INR (S n)) Ht Hd).
  pose proof (sqrt_def t Ht) as Htsq.
  pose proof (sqrt_def (INR (S n)) (Rlt_le _ _ Hd)) as Hdsq.
  field_simplify.
  - rewrite (pow2_sqrt t Ht).
    replace (sqrt (INR (S n)) ^ 3) with
      (sqrt (INR (S n)) * (sqrt (INR (S n)) * sqrt (INR (S n)))) by ring.
    rewrite Hdsq; f_equal; ring.
  - split; lra.
  - lra.
Qed.

Theorem quadratic_gaussian_time_stein n beta gamma offset coeff Y S t C :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= t ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  List.Forall (gaussian_vector_domain n)
    [(fun x => trace_pair n (quadratic_matrix n (/sqrt (INR (Datatypes.S n))) (matrix_zero n) x)
      (quadratic_gradient n beta gamma offset coeff Y S (sqrt (t / INR (Datatypes.S n))) C x));
     (fun x => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
       (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x)));
     (fun x => chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S
       (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x)) x)] /\
  gaussian_vector_expectation n
    (fun x => trace_pair n (quadratic_matrix n (/sqrt (INR (Datatypes.S n))) (matrix_zero n) x)
      (quadratic_gradient n beta gamma offset coeff Y S (sqrt (t / INR (Datatypes.S n))) C x)) =
  (2 * sqrt t / INR (Datatypes.S n)) * gaussian_vector_expectation n
    (fun x => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x))) +
  (t / (INR (Datatypes.S n) * sqrt (INR (Datatypes.S n)))) * gaussian_vector_expectation n
    (fun x => chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n (sqrt (t / INR (Datatypes.S n))) C x)) x).
Proof.
  intros Hb Hg HY HS Ht HC.
  destruct (quadratic_gaussian_matrix_stein n beta gamma offset coeff Y S
    (sqrt (t / INR (Datatypes.S n))) C Hb Hg HY HS HC) as [Hdomains HE].
  inversion Hdomains as [|? ? HW Htail]; subst.
  inversion Htail as [|? ? HD Htail1]; subst.
  inversion Htail1 as [|? ? HR Hnil]; subst.
  split.
  - constructor.
    + apply gaussian_vector_domain_ext with (f := fun x => /sqrt (INR (Datatypes.S n)) *
        trace_pair n (quadratic_matrix n 1 (matrix_zero n) x)
          (quadratic_gradient n beta gamma offset coeff Y S (sqrt (t / INR (Datatypes.S n))) C x)).
      * intro x; symmetry; apply quadratic_centered_trace_scale.
      * apply gaussian_vector_domain_scale; exact HW.
    + constructor; [exact HD|]; constructor; [exact HR|constructor].
  - transitivity (gaussian_vector_expectation n (fun x => /sqrt (INR (Datatypes.S n)) *
      trace_pair n (quadratic_matrix n 1 (matrix_zero n) x)
        (quadratic_gradient n beta gamma offset coeff Y S (sqrt (t / INR (Datatypes.S n))) C x))).
    + apply gaussian_vector_expectation_ext; intro x; apply quadratic_centered_trace_scale.
    + eapply eq_trans.
      * exact (proj2 (gaussian_vector_scale n _ (/sqrt (INR (Datatypes.S n))) (proj1 HW))).
      * eapply eq_trans.
        -- exact (f_equal (fun z : R => /sqrt (INR (Datatypes.S n)) * z) HE).
        -- apply quadratic_gaussian_time_coefficients; exact Ht.
Qed.
