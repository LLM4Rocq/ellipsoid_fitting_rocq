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
  Matrix.EntryNormBounds Gibbs.Definitions Quadratic.GradientRegularity
  Gaussian.Vector.Definitions Matrix.SymmetricBasis
  Chaos.SecondOrderDefinitions Gaussian.Vector.Domain Gaussian.Vector.Stein.
Import Quadratic.GradientRegularity.QuadraticUniformBounds
  Quadratic.GradientRegularity.QuadraticPolynomialGrowth
  Quadratic.GradientRegularity.QuadraticGrowthContinuity.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Gaussian integration by parts for the nested Gibbs gradient along an
   affine family of matrices. Here T : E -> matrix n is a bounded linear
   map: MathComp's linear T with a bound `|T y| <= M * `|y|. The norm of
   matrix n is the Frobenius norm and that of vector m the Euclidean norm.
   Write G z for trace_pair n B applied to the nested gradient
   matrix_nested_gradient at the matrix C + r * T z. The results on the
   nested gradient assume 0 < beta, 0 < gamma and nonempty lists Y and S.
   - affine_matrix_frechet: z |-> C + r * T z is differentiable at every
     point (is_diff), with differential u |-> r * T u.
   - affine_gibbs_trace_frechet: G is differentiable, and its differential
     at x pairs B with matrix_nested_gradient_derivative at C + r * T x in
     the direction r * T u.
   - affine_gibbs_trace_direction_continuous: the pairing of B with the
     derivative of the nested gradient in a fixed direction U is continuous
     along the affine family.
   - affine_gibbs_trace_uniform: the pairings of B with the nested gradient
     and with its derivative in a direction U are bounded uniformly in the
     matrix.
   - affine_gaussian_trace_stein: for i <= m, the Gaussian expectation on
     vector m of the derivative of G in the direction of coordinate i
     equals that of z_i * G z, and the three functions involved satisfy
     gaussian_vector_domain.
   The last result applies gaussian_vector_first_stein with the constant
   bounds of affine_gibbs_trace_uniform. Each level of the iterated
   expectation gaussian_vector_expectation is a Lebesgue integral over the
   line against the Gaussian kernel. *)

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
