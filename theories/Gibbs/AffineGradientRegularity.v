From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Gibbs.MatrixDefinitions
  Gibbs.MatrixSecondDerivativeDefinitions Gibbs.NestedGradientDefinitions
  Gibbs.MatrixNestedGradient Gibbs.NestedHessian Matrix.OperatorDefinitions
  Matrix.EntryNormBounds Quadratic.GradientRegularity
  Gaussian.Vector.Definitions Chaos.SecondOrderDefinitions
  Gibbs.AffineGradientStein Gaussian.Vector.Domain.
Import Quadratic.GradientRegularity.QuadraticGrowthContinuity.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Regularity of two functions of z built from the nested Gibbs gradient
   matrix_nested_gradient at the affine point C + r * T z, where T is linear
   with |T x| <= M * |x|. The norms are Euclidean.
   - affine_gaussian_weighted_trace_regular: z |-> z_i times trace_pair B of
     the gradient is continuous at every point and bounded by
     K * (1 + |z|).
   - affine_gaussian_direction_trace_regular: z |-> trace_pair B of
     matrix_nested_gradient_derivative, the derivative of the gradient, in
     the direction U is continuous at every point and bounded by a constant.
   These are the hypotheses of gaussian_vector_polynomial_domain
   (Gaussian.Vector.Domain). *)

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
