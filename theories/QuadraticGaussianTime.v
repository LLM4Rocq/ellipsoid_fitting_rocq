From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  TensorDefinitions GradientDefinitions MatrixThirdDefinitions SecondChaosDefinitions
  SymmetricDefinitions QuadraticDefinitions QuadraticExpansion GaussianVectorDefinitions
  GaussianVectorDomain GaussianVectorAlgebra GaussianVectorFinite QuadraticGaussianMatrix.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module QuadraticGaussianTime of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/QuadraticGaussianProofs.v), extracted to
   build/agent2/unbundled/QuadraticGaussianTime.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundle GaussianVectorProofs and named its inner
   modules GaussianVectorDomain, GaussianVectorAlgebra and
   GaussianVectorFinite through it. The port imports these standalone
   ported modules directly.

   The three statements keep their names, their arguments in the same order,
   their hypotheses and their text. No item is added.
   quadratic_centered_trace_scale and quadratic_gaussian_time_coefficients
   mention no analytic notion and mean the same as before. The meaning of
   quadratic_gaussian_time_stein changes only through the ported definitions
   it mentions: gaussian_vector_domain and gaussian_vector_expectation follow
   the ported GaussianVectorDefinitions (difference 4 of analysis/README.md),
   that is Lebesgue integrability against the Gaussian kernel at each level
   of the iterated expectation, and Lebesgue integrals. The functions of the
   statement are continuous and bounded by a polynomial in the Euclidean
   norm of the vector (by the ported QuadraticGaussianMatrix), so they are
   absolutely integrable against the kernel, and the Lebesgue and improper
   Riemann values agree. The statement of quadratic_gaussian_time_stein is
   the text of the clause "Paper-normalized fixed-time identity" of the
   restated challenge ellipsoid_gaussian_matrix.

   The proofs are the original ones. Stdlib's "rewrite ... by tac" is written
   with explicit arguments, in the form that ssreflect accepts. *)

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
