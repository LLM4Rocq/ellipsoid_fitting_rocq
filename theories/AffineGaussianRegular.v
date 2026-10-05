From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  MatrixGibbsDefinitions MatrixSecondDefinitions GradientDefinitions MatrixGradient
  MatrixHessian OperatorDefinitions CoefficientBounds QuadraticGrowthProofs
  GaussianVectorDefinitions SecondChaosDefinitions AffineGaussianGibbs
  GaussianVectorDomain.
Import QuadraticGrowthProofs.QuadraticGrowthContinuity.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module AffineGaussianRegular of
   theories/InterpolationProofs.v (also copied in GoeProofs.v and
   JointProofs.v), extracted to build/agent2/unbundled/AffineGaussianRegular.v,
   from Coquelicot to MathComp-Analysis, as a standalone module.

   The original imported the bundle GaussianVectorProofs and named its inner
   module GaussianVectorDomain through it. The port imports the standalone
   ported module GaussianVectorDomain directly. It imports the inner module
   QuadraticGrowthContinuity of QuadraticGrowthProofs through
   QuadraticGrowthProofs, as before.

   The two theorems keep their names and their arguments, in the same order.
   No item is added. The statements change form in three ways, as in the
   port of AffineGaussianGibbs, and none of them changes their meaning.

   1. Linear maps. Coquelicot's is_linear T becomes the conjunction
        linear T /\ exists M : R, 0 < M /\ forall x, (`|T x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound
      (analysis/README.md, difference 2). It is equivalent to Coquelicot's
      record, and it is the hypothesis of the ported theorems of
      AffineGaussianGibbs.

   2. Pointwise continuity. Coquelicot's continuous f z becomes MathComp's
      {for z, continuous f} (difference 5). This is the form of the
      continuity hypothesis of the ported gaussian_vector_polynomial_domain
      and gaussian_vector_polynomial_sum_domain, which are what the importers
      (GoeGibbs) feed these conjuncts to.

   3. Norms. Coquelicot's norm z becomes MathComp's (`|z|)%R. The vectors
      nest euclidean_product (difference 1), so this is still the Euclidean
      norm, and the bounds K * (1 + norm z) ^ p keep their constants.

   The proofs follow the original. Coquelicot's continuous_mult becomes
   MathComp's continuousM at the codomain R^o, filterdiff_continuous becomes
   differentiable_continuous, and norm_ge_0 becomes normr_ge0. *)

Theorem affine_gaussian_weighted_trace_regular n m beta gamma offset coeff Y S
    (T : vector m -> matrix n) C r B i :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (linear T /\
    exists M : R, 0 < M /\ forall x : vector m, (`|T x|)%R <= M * (`|x|)%R) ->
  (forall z : vector m, {for z, continuous
    (fun x => vector_entry m x i * trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T x)))))}) /\
  exists K : R, 0 <= K /\ forall z : vector m,
    Rabs (vector_entry m z i * trace_pair n B (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z))))) <= K * (1 + (`|z|)%R)^1.
Proof.
  intros Hb Hg HY HS HT; split.
  - intro z.
    have HE : {for z, continuous (fun x : vector m => vector_entry m x i)}.
    { exact (@growth_linear_continuous (vector_NormedModule m) R^o
        (tuple_entry R^o m i) z (tuple_entry_linear R^o m i)). }
    have HG : {for z, continuous ((fun x => trace_pair n B
        (matrix_nested_gradient n beta gamma offset coeff Y S
          (matrix_add n C (matrix_scale n r (T x))))) : vector m -> R^o)}.
    { have HD := affine_gibbs_trace_frechet n beta gamma offset coeff Y S T C r B z
        Hb Hg HY HS HT.
      have Hd : differentiable ((fun x => trace_pair n B
          (matrix_nested_gradient n beta gamma offset coeff Y S
            (matrix_add n C (matrix_scale n r (T x))))) : vector m -> R^o) z.
      { by have := HD; case. }
      exact (differentiable_continuous Hd). }
    exact (@continuousM R (vector_NormedModule m) _ _ z HE HG).
  - destruct (affine_gibbs_trace_uniform n beta gamma offset coeff Y S B (matrix_zero n)
      Hb Hg HY HS) as [K0 [K1 [HK0 [HK1 Hbound]]]].
    exists K0; split; [exact HK0|]; intro z; rewrite Rabs_mult.
    apply Rle_trans with ((`|z|)%R * K0).
    + apply Rmult_le_compat; try apply Rabs_pos.
      * rewrite RabsE; exact (tuple_entry_norm_bound R^o m i z).
      * apply Hbound.
    + have Hz : 0 <= (`|z|)%R by apply/RleP; apply normr_ge0.
      simpl; nra.
Qed.

Theorem affine_gaussian_direction_trace_regular n m beta gamma offset coeff Y S
    (T : vector m -> matrix n) C r B U :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (linear T /\
    exists M : R, 0 < M /\ forall x : vector m, (`|T x|)%R <= M * (`|x|)%R) ->
  (forall z : vector m, {for z, continuous
    (fun x => trace_pair n B (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T x))) U))}) /\
  exists K : R, 0 <= K /\ forall z : vector m,
    Rabs (trace_pair n B (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (T z))) U)) <= K * (1 + (`|z|)%R)^0.
Proof.
  intros Hb Hg HY HS HT; split.
  - intro z; apply affine_gibbs_trace_direction_continuous; assumption.
  - destruct (affine_gibbs_trace_uniform n beta gamma offset coeff Y S B U
      Hb Hg HY HS) as [K0 [K1 [HK0 [HK1 Hbound]]]].
    exists K1; split; [exact HK1|]; intro z.
    rewrite pow_O Rmult_1_r; apply Hbound.
Qed.
