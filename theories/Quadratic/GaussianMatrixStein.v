From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Matrix.OperatorDefinitions
  Tensor.Definitions Gibbs.NestedGradientDefinitions Gibbs.MatrixNestedGradient
  Gibbs.HessianDefinitions Gibbs.NestedHessian
  Gibbs.MatrixThirdDerivativeDefinitions Gibbs.MatrixThirdDerivative
  Chaos.SecondOrderDefinitions Matrix.SymmetricBasisDefinitions
  Matrix.SymmetricDivergence Quadratic.Definitions Quadratic.GradientSymmetry
  Quadratic.GradientSecondContraction Quadratic.GradientRegularity
  Gaussian.VectorDefinitions Gaussian.VectorDomain Gaussian.VectorLinearity
  Gaussian.VectorFiniteSums Quadratic.GradientEntryRegularity
  Quadratic.WeightedEntryRegularity Quadratic.EntryStein.
Import Quadratic.GradientRegularity.QuadraticGrowth.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* The Gaussian Stein identity for the nested Gibbs gradient along the
   quadratic matrix map, for a standard Gaussian vector x and symmetric
   matrices coeff y s (quadratic_gaussian_matrix_stein). Let
     W x = trace_pair (x x^T - I) (quadratic_gradient ... x),
     Div x = symmetric_divergence of matrix_nested_gradient_derivative,
     Chaos x = chaos_contraction of matrix_nested_third_derivative along x,
   where both derivatives are taken at quadratic_matrix n lambda C x. The
   three functions are in the Gaussian domain and
     E[W] = 2 lambda E[Div] + lambda^2 E[Chaos].
   The domains come from continuity and polynomial bounds of the entries
   (gaussian_vector_polynomial_double_sum_domain), and the identity from the
   identity of each entry, quadratic_gaussian_entry_stein, summed over the
   entries. Expectations are iterated Lebesgue integrals. *)

Lemma quadratic_gaussian_weighted_sum_domain n beta gamma offset coeff Y S lambda C :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  gaussian_vector_domain n (fun x => coordinate_sum n (fun a => coordinate_sum n (fun b =>
    (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
    matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b))).
Proof.
  intros Hb Hg HY HS.
  apply (proj1 (gaussian_vector_polynomial_double_sum_domain n n n 2 _ ltac:(
    intros a b Ha Hbb; exact (proj1 (quadratic_gaussian_weighted_entry_regular n beta gamma
      offset coeff Y S lambda C a b Hb Hg HY HS Ha Hbb))) ltac:(
    intros a b Ha Hbb; exact (proj2 (quadratic_gaussian_weighted_entry_regular n beta gamma
      offset coeff Y S lambda C a b Hb Hg HY HS Ha Hbb))))).
Qed.

Theorem quadratic_gaussian_divergence_domain n beta gamma offset coeff Y S lambda C :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  gaussian_vector_domain n (fun x => symmetric_divergence n
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x))).
Proof.
  intros Hb Hg HY HS.
  pose proof (proj1 (gaussian_vector_polynomial_double_sum_domain n n n O
    (fun a b x => matrix_entry n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_second n a b)) a b) ltac:(
    intros a b Ha Hbb; exact (proj1 (quadratic_divergence_component_regular n beta gamma
      offset coeff Y S lambda C a b Hb Hg HY HS Ha Hbb))) ltac:(
    intros a b Ha Hbb; exact (proj2 (quadratic_divergence_component_regular n beta gamma
      offset coeff Y S lambda C a b Hb Hg HY HS Ha Hbb))))) as HD.
  apply gaussian_vector_domain_ext with (f := fun x => /2 * coordinate_sum n (fun a => coordinate_sum n (fun b =>
    matrix_entry n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_second n a b)) a b))).
  - intro x.
    rewrite (symmetric_divergence_identity n
      (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x))
      (matrix_third_is_diff_linear _ _ _
        (matrix_nested_gradient_frechet n beta gamma offset coeff Y S Hb Hg HY HS
          (quadratic_matrix n lambda C x)))).
    field.
  - apply gaussian_vector_domain_scale; exact HD.
Qed.

Theorem quadratic_gaussian_chaos_domain n beta gamma offset coeff Y S lambda C :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  gaussian_vector_domain n (fun x => chaos_contraction n
    (matrix_nested_third_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)) x).
Proof.
  intros Hb Hg HY HS HC.
  pose proof (proj1 (gaussian_vector_polynomial_double_sum_domain n n n 2
    (fun a b x => matrix_entry n (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_first n x a) (chaos_first n x b)) a b) ltac:(
    intros a b Ha Hbb; exact (proj1 (quadratic_chaos_component_regular n beta gamma
      offset coeff Y S lambda C a b Hb Hg HY HS Ha Hbb))) ltac:(
    intros a b Ha Hbb; exact (proj2 (quadratic_chaos_component_regular n beta gamma
      offset coeff Y S lambda C a b Hb Hg HY HS Ha Hbb))))) as HD.
  apply gaussian_vector_domain_ext with (f := fun x => coordinate_sum n (fun a => coordinate_sum n (fun b =>
    matrix_entry n (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_first n x a) (chaos_first n x b)) a b))).
  - intro x; apply quadratic_gradient_second_contraction; assumption.
  - exact HD.
Qed.

Lemma quadratic_gaussian_trace_sum n beta gamma offset coeff Y S lambda C (x : vector n) :
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  trace_pair n (quadratic_matrix n 1 (matrix_zero n) x)
    (quadratic_gradient n beta gamma offset coeff Y S lambda C x) =
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
    matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)).
Proof.
  intro HC; unfold trace_pair; apply coordinate_sum_ext; intros a Ha;
    apply coordinate_sum_ext; intros b Hb.
  unfold quadratic_matrix at 1; rewrite (matrix_entry_build _ _ _ _ Ha Hb).
  rewrite matrix_entry_zero.
  assert (HS : symmetric_matrix n (quadratic_gradient n beta gamma offset coeff Y S lambda C x)).
  { unfold quadratic_gradient; apply quadratic_nested_gradient_symmetric; exact HC. }
  rewrite (HS b a Hb Ha); ring.
Qed.

Theorem quadratic_gaussian_matrix_stein n beta gamma offset coeff Y S lambda C :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  List.Forall (gaussian_vector_domain n)
    [(fun x => trace_pair n (quadratic_matrix n 1 (matrix_zero n) x)
      (quadratic_gradient n beta gamma offset coeff Y S lambda C x));
     (fun x => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
       (quadratic_matrix n lambda C x)));
     (fun x => chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S
       (quadratic_matrix n lambda C x)) x)] /\
  gaussian_vector_expectation n
    (fun x => trace_pair n (quadratic_matrix n 1 (matrix_zero n) x)
      (quadratic_gradient n beta gamma offset coeff Y S lambda C x)) =
  2 * lambda * gaussian_vector_expectation n
    (fun x => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x))) +
  lambda^2 * gaussian_vector_expectation n
    (fun x => chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x)) x).
Proof.
  intros Hb Hg HY HS HC.
  pose proof (quadratic_gaussian_divergence_domain n beta gamma offset coeff Y S lambda C Hb Hg HY HS) as HD.
  pose proof (quadratic_gaussian_chaos_domain n beta gamma offset coeff Y S lambda C Hb Hg HY HS HC) as HR.
  assert (HW : gaussian_vector_domain n (fun x => trace_pair n (quadratic_matrix n 1 (matrix_zero n) x)
    (quadratic_gradient n beta gamma offset coeff Y S lambda C x))).
  { apply gaussian_vector_domain_ext with (f := fun x => coordinate_sum n (fun a => coordinate_sum n (fun b =>
      (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
      matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b))).
    - intro x; symmetry; apply quadratic_gaussian_trace_sum; exact HC.
    - apply quadratic_gaussian_weighted_sum_domain; assumption. }
  split.
  - constructor; [exact HW|]; constructor; [exact HD|]; constructor; [exact HR|constructor].
  - pose (F := fun a b x => matrix_entry n
      (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x
        (chaos_basis n a) (chaos_basis n b)) a b).
    pose (W := fun a b x =>
      (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
      matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b).
    assert (Hentry : forall a b, (a <= n)%coq_nat -> (b <= n)%coq_nat ->
      gaussian_vector_integrable n (F a b) /\ gaussian_vector_integrable n (W a b) /\
      gaussian_vector_expectation n (F a b) = gaussian_vector_expectation n (W a b)).
    { intros a b Ha Hbb.
      destruct (quadratic_gaussian_entry_stein n beta gamma offset coeff Y S lambda C a b Hb Hg HY HS Ha Hbb)
        as [Hdomains HE].
      inversion Hdomains as [|? ? H0 Htail]; subst.
      inversion Htail as [|? ? H1 Htail1]; subst.
      inversion Htail1 as [|? ? H2 Htail2]; subst.
      inversion Htail2 as [|? ? H3 Hnil]; subst.
      split; [exact (proj1 H2)|]; split; [exact (proj1 H3)|exact HE]. }
    assert (Hsum : gaussian_vector_expectation n (fun x => coordinate_sum n (fun a => coordinate_sum n (fun b => W a b x))) =
      gaussian_vector_expectation n (fun x => coordinate_sum n (fun a => coordinate_sum n (fun b => F a b x)))).
    { rewrite (proj2 (gaussian_vector_coordinate_double_sum n n n W
        ltac:(intros a b Ha Hbb; exact (proj1 (proj2 (Hentry a b Ha Hbb)))))).
      rewrite (proj2 (gaussian_vector_coordinate_double_sum n n n F
        ltac:(intros a b Ha Hbb; exact (proj1 (Hentry a b Ha Hbb))))).
      apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hbb.
      symmetry; exact (proj2 (proj2 (Hentry a b Ha Hbb))). }
    transitivity (gaussian_vector_expectation n (fun x => coordinate_sum n (fun a => coordinate_sum n (fun b => W a b x)))) .
    + apply gaussian_vector_expectation_ext; intro x; apply quadratic_gaussian_trace_sum; exact HC.
    + rewrite Hsum.
      transitivity (gaussian_vector_expectation n (fun x =>
        2 * lambda * symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)) +
        lambda^2 * chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)) x)).
      * apply gaussian_vector_expectation_ext; intro x; apply quadratic_gradient_second_sum; assumption.
      * rewrite (proj2 (gaussian_vector_add n _ _
          (proj1 (gaussian_vector_scale n _ (2*lambda) (proj1 HD)))
          (proj1 (gaussian_vector_scale n _ (lambda^2) (proj1 HR))))).
        rewrite (proj2 (gaussian_vector_scale n _ (2*lambda) (proj1 HD))).
        rewrite (proj2 (gaussian_vector_scale n _ (lambda^2) (proj1 HR))); reflexivity.
Qed.
