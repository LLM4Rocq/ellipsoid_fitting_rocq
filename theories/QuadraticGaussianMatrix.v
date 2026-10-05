From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  TensorDefinitions GradientDefinitions MatrixGradient HessianDefinitions MatrixHessian
  MatrixThirdDefinitions MatrixThird SecondChaosDefinitions SymmetricDefinitions
  SymmetricDivergence QuadraticDefinitions QuadraticSymmetry QuadraticExpansion
  QuadraticGrowthProofs GaussianVectorDefinitions GaussianVectorDomain
  GaussianVectorAlgebra GaussianVectorFinite GaussianMatrixComponents
  QuadraticGaussianRegular QuadraticGaussianStein.
Import QuadraticGrowthProofs.QuadraticGrowth.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of the inner module QuadraticGaussianMatrix of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/QuadraticGaussianProofs.v), extracted to
   build/agent2/unbundled/QuadraticGaussianMatrix.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundles QuadraticGrowthProofs and
   GaussianVectorProofs, and named their inner modules
   QuadraticGrowthProofs.QuadraticGrowth,
   GaussianVectorProofs.GaussianVectorDomain,
   GaussianVectorProofs.GaussianVectorAlgebra and
   GaussianVectorProofs.GaussianVectorFinite. The port imports
   analysis/QuadraticGrowthProofs.v, whose inner module QuadraticGrowth
   keeps that name, and the standalone ported modules GaussianVectorDomain,
   GaussianVectorAlgebra and GaussianVectorFinite. It also imports
   MatrixThird, for the reason given below.

   Every lemma and theorem keeps its name, its arguments in the same order
   and its hypotheses. No item is added. The statements are the text of the
   original, and their meaning changes only through the ported definitions
   they mention: gaussian_vector_domain and gaussian_vector_expectation
   follow the ported GaussianVectorDefinitions (difference 4 of
   analysis/README.md), that is Lebesgue integrability against the Gaussian
   kernel at each level of the iterated expectation, and Lebesgue integrals.
   The functions of the statements are continuous and bounded by a
   polynomial in the Euclidean norm of the vector, so they are absolutely
   integrable against the kernel and the Lebesgue and improper Riemann
   values agree. The statement of quadratic_gaussian_matrix_stein is the
   text of the clause "Matrix Gaussian identity and separate domains" of the
   restated challenge ellipsoid_gaussian_matrix.

   One index bound changes form, inside the proof of
   quadratic_gaussian_matrix_stein: with ssreflect loaded, (a <= n)%nat would
   mean ssrnat's boolean leq, so the local assertion writes (a <= n)%coq_nat,
   Stdlib's Peano order le, as the ported lemmas it uses do.

   The proofs are the original ones, with three changes of form.
   1. The linearity and the bound of the derivative of
      matrix_nested_gradient, which the original takes from proj1 of
      Coquelicot's filterdiff to feed symmetric_divergence_identity, come
      from matrix_third_is_diff_linear of MatrixThird applied to the ported
      matrix_nested_gradient_frechet, as in the port of QuadraticExpansion.
   2. Stdlib's "rewrite ... by tac" is written with explicit arguments, in
      the form that ssreflect accepts.
   3. The continuity hypotheses of gaussian_vector_polynomial_double_sum_domain
      are stated with {for x, continuous _} and the bounds with the norm
      `|x|%R, which are the forms given by the ported regularity lemmas. *)

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
