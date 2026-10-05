From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  MatrixGibbsDefinitions MatrixSecondDefinitions GradientDefinitions MatrixGradient
  MatrixHessian OperatorDefinitions CoefficientBounds GibbsDefinitions
  QuadraticGrowthProofs GaussianVectorDefinitions SymmetricBasis
  SecondChaosDefinitions GaussianVectorDomain GaussianVectorStein.
Import QuadraticGrowthProofs.QuadraticUniformBounds
  QuadraticGrowthProofs.QuadraticPolynomialGrowth
  QuadraticGrowthProofs.QuadraticGrowthContinuity.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module AffineGaussianGibbs of
   theories/InterpolationProofs.v (also copied in GoeProofs.v and
   JointProofs.v), extracted to build/agent2/unbundled/AffineGaussianGibbs.v,
   from Coquelicot to MathComp-Analysis, as a standalone module.

   The original imported the bundle GaussianVectorProofs and named its inner
   modules GaussianVectorStein and GaussianVectorDomain through it. The port
   imports these standalone ported modules directly. It imports the three
   inner modules of QuadraticGrowthProofs that the original named, through
   QuadraticGrowthProofs as before.

   The five theorems keep their names and their arguments, in the same
   order. No item is added. The statements change form in five ways, as in
   the ports of MatrixCoordinates, QuadraticGrowthProofs, GaussianVectorStein
   and the restated challenge ellipsoid_goe (group 5, of which
   affine_gaussian_trace_stein is the proof).

   1. Linear maps. Coquelicot's is_linear T, a hypothesis of every theorem
      but affine_gibbs_trace_uniform, becomes the conjunction
        linear T /\ exists M : R, 0 < M /\ forall y, (`|T y|)%R <= M * (`|y|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound
      (analysis/README.md, difference 2). It is equivalent to Coquelicot's
      record, and it is the form of group 5 of the restated challenge.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally x) l becomes
      is_diff x f l of MathComp-Analysis, in affine_matrix_frechet and
      affine_gibbs_trace_frechet: f is differentiable at x and its
      differential 'd f x is l. Both say that l is linear and continuous and
      that f (x + h) = f x + l h + o (h). The real-valued map of
      affine_gibbs_trace_frechet is typed into R^o, the normed module view
      of R; R^o is R by definition, so the map is unchanged. Coquelicot's
      NormedModule R_AbsRing becomes normedModType R.

   3. Pointwise continuity. Coquelicot's continuous f x becomes MathComp's
      {for x, continuous f} (difference 5), in
      affine_gibbs_trace_direction_continuous.

   4. Norms. Coquelicot's norm becomes MathComp's (`|_|)%R, in the constants
      of affine_gibbs_trace_uniform and in the bound of item 1. The norm of
      matrix n is the Frobenius norm and that of vector m the Euclidean
      norm, as in Coquelicot, because the port of MatrixDefinitions nests
      euclidean_product (difference 1). So the constants are the same.

   5. Indices. With ssreflect loaded, (i <= m)%nat would be ssrnat's boolean
      leq. affine_gaussian_trace_stein writes (i <= m)%coq_nat, Stdlib's
      Peano order le, as in the original and the restated challenge.

   The meaning of gaussian_vector_domain and gaussian_vector_expectation, in
   affine_gaussian_trace_stein, follows the ported GaussianVectorDefinitions
   (difference 4): at each level of the iterated expectation, Lebesgue
   integrability over the line against the Gaussian kernel, and Lebesgue
   integrals. The three functions of the conclusion are continuous and
   bounded by a polynomial in the norm, so the ported
   gaussian_vector_first_stein establishes this reading.

   The proofs follow the original. Coquelicot's filterdiff_linear becomes
   matrix_linear_is_diff of MatrixCoordinates, filterdiff_const becomes
   is_diff_cst, filterdiff_scal_r_fct becomes is_diffZ, filterdiff_plus_fct
   becomes is_diffD, filterdiff_ext_lin becomes is_diff_eq with an equation
   of functions, filterdiff_comp' becomes is_diff_comp, filterdiff_continuous
   becomes differentiable_continuous, and norm_ge_0 becomes normr_ge0. *)

Theorem affine_matrix_frechet {E : normedModType R} n
    (T : E -> matrix n) C r x :
  (linear T /\
    exists M : R, 0 < M /\ forall y : E, (`|T y|)%R <= M * (`|y|)%R) ->
  is_diff x (fun z => matrix_add n C (matrix_scale n r (T z)))
    (fun u => matrix_scale n r (T u)).
Proof.
  intros HT; unfold matrix_add, matrix_scale.
  have HL := matrix_linear_is_diff T x HT.
  have HD := is_diffD (is_diff_cst C x) (is_diffZ r HL).
  have E1 : (fun z => (C + r *: T z)%R) = (cst C + r *: T)%R.
  { by apply: funext. }
  rewrite E1; apply: (is_diff_eq HD).
  by apply: funext => u /=; rewrite add0r.
Qed.

Theorem affine_gibbs_trace_frechet {E : normedModType R} n
    beta gamma offset coeff Y S (T : E -> matrix n) C r B x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (linear T /\
    exists M : R, 0 < M /\ forall y : E, (`|T y|)%R <= M * (`|y|)%R) ->
  is_diff x ((fun z => trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z))))) : E -> R^o)
    (fun u => trace_pair n B (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T x))) (matrix_scale n r (T u)))).
Proof.
  intros Hb Hg HY HS HT.
  have HA := affine_matrix_frechet n T C r x HT.
  have HG := matrix_nested_gradient_frechet n beta gamma offset coeff Y S Hb Hg HY HS
    (matrix_add n C (matrix_scale n r (T x))).
  have HP := matrix_linear_is_diff (trace_pair n B : matrix n -> R^o)
    (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T x)))) (trace_pair_linear n B).
  exact (is_diff_comp (is_diff_comp HA HG) HP).
Qed.

Theorem affine_gibbs_trace_direction_continuous {E : normedModType R} n
    beta gamma offset coeff Y S (T : E -> matrix n) C r B U x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (linear T /\
    exists M : R, 0 < M /\ forall y : E, (`|T y|)%R <= M * (`|y|)%R) ->
  {for x, continuous (fun z => trace_pair n B
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z))) U))}.
Proof.
  intros Hb Hg HY HS HT.
  have HA := affine_matrix_frechet n T C r x HT.
  have HS2 := matrix_nested_gradient_second_frechet n beta gamma offset coeff Y S
    (matrix_add n C (matrix_scale n r (T x))) U Hb Hg HY HS.
  have HP := matrix_linear_is_diff (trace_pair n B : matrix n -> R^o)
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T x))) U) (trace_pair_linear n B).
  have HC := is_diff_comp (is_diff_comp HA HS2) HP.
  have Hd : differentiable ((fun z => trace_pair n B
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z))) U)) : E -> R^o) x.
  { by have := HC; case. }
  exact (differentiable_continuous Hd).
Qed.

Theorem affine_gibbs_trace_uniform n beta gamma offset coeff Y S (B U : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists K0 K1 : R, 0 <= K0 /\ 0 <= K1 /\ forall A : matrix n,
    Rabs (trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S A)) <= K0 /\
    Rabs (trace_pair n B (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A U)) <= K1.
Proof.
  intros Hb Hg HY HS.
  destruct (growth_finite_coefficient_bound n coeff Y S) as [K [HK HC]].
  set (L := INR (Datatypes.S n)^2*K).
  assert (HL : 0 <= L) by (unfold L; apply Rmult_le_pos; [apply pow2_ge_0|exact HK]).
  assert (HT : forall y s, In y Y -> In s S -> forall P : matrix n,
    Rabs (trace_pair n (coeff y s) P) <= L * (`|P|)%R).
  { apply growth_trace_coefficient_bound; exact HC. }
  assert (HB0 : 0 <= (`|B|)%R) by (apply/RleP; apply normr_ge0).
  assert (HU0 : 0 <= (`|U|)%R) by (apply/RleP; apply normr_ge0).
  exists (L*(`|B|)%R), (2*L^2*(beta+gamma)*(`|B|)%R*(`|U|)%R).
  split; [apply Rmult_le_pos; [exact HL|exact HB0]|].
  split.
  - apply Rmult_le_pos; [|exact HU0].
    apply Rmult_le_pos; [|exact HB0].
    apply Rmult_le_pos; [|lra].
    apply Rmult_le_pos; [lra|apply pow2_ge_0].
  - intros A; split; rewrite symmetric_trace_pair_comm.
    + rewrite matrix_nested_gradient_trace.
      unfold matrix_nested_derivative; apply growth_gibbs_mean_bound; [exact HY|].
      intros y Hy; unfold matrix_inner_derivative; apply growth_gibbs_mean_bound; [exact HS|].
      intros s Hs; apply HT; assumption.
    + rewrite (matrix_nested_gradient_derivative_trace n beta gamma offset coeff Y S
        A B U Hb Hg HY HS).
      apply growth_matrix_second_bound; assumption.
Qed.

Theorem affine_gaussian_trace_stein n m beta gamma offset coeff Y S
    (T : vector m -> matrix n) C r B i :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (linear T /\
    exists M : R, 0 < M /\ forall x : vector m, (`|T x|)%R <= M * (`|x|)%R) ->
  (i <= m)%coq_nat ->
  List.Forall (gaussian_vector_domain m)
    [(fun z => trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z)))));
     (fun z => trace_pair n B (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z)))
      (matrix_scale n r (T (chaos_basis m i)))));
     (fun z => vector_entry m z i * trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z)))))] /\
  gaussian_vector_expectation m
    (fun z => trace_pair n B (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z)))
      (matrix_scale n r (T (chaos_basis m i))))) =
  gaussian_vector_expectation m
    (fun z => vector_entry m z i * trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z))))).
Proof.
  intros Hb Hg HY HS HT Hi.
  destruct (affine_gibbs_trace_uniform n beta gamma offset coeff Y S B
    (matrix_scale n r (T (chaos_basis m i))) Hb Hg HY HS)
    as [K0 [K1 [HK0 [HK1 Hbound]]]].
  apply (gaussian_vector_first_stein m i
    (fun z => trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z)))))
    (fun z u => trace_pair n B (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z))) (matrix_scale n r (T u)))) K0 O K1 O);
    try assumption.
  - intros x; apply affine_gibbs_trace_frechet; assumption.
  - intros x; apply affine_gibbs_trace_direction_continuous; assumption.
  - intros x; rewrite pow_O Rmult_1_r; apply Hbound.
  - intros x; rewrite pow_O Rmult_1_r; apply Hbound.
Qed.
