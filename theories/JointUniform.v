From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorBounds OperatorProperties NormEquivalence
  TensorDefinitions SecondChaosDefinitions SecondChaosAlgebra
  SymmetricDefinitions SymmetricBasis MatrixGibbsDefinitions
  MatrixSecondDefinitions GradientDefinitions MatrixGradient
  HessianDefinitions MatrixHessian MatrixThirdDefinitions CoefficientBounds
  QuadraticDefinitions QuadraticCalculus QuadraticGrowthProofs
  GaussianMatrixComponents GoeDefinitions GoePairs GoeSynthesis.
Import ListNotations.
Import GRing.Theory Num.Theory.
Import QuadraticGrowthProofs.QuadraticUniformBounds
  QuadraticGrowthProofs.QuadraticPolynomialGrowth.
Open Scope R_scope.

(* Port of the inner module JointUniform of theories/InterpolationProofs.v
   (also copied in JointProofs.v) from Coquelicot to MathComp-Analysis, as a
   standalone module. The original imports the bundle GoeProofs and names
   GoeProofs.GoePairs and GoeProofs.GoeSynthesis through it; this port
   imports the standalone modules GoePairs and GoeSynthesis instead. It
   imports the inner modules QuadraticUniformBounds and
   QuadraticPolynomialGrowth of QuadraticGrowthProofs, as the original did.

   Every lemma and theorem of the original keeps its name and its
   arguments, in the same order. No item is added. The statements change
   form in two ways, the ways of the ports of QuadraticGrowthProofs,
   NormEquivalence and GoeSynthesis, which this module uses.

   1. Norms. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. On
      vector n and matrix n the norms are those of the ports of
      OperatorDefinitions and MatrixDefinitions. They nest euclidean_product
      of MatrixEuclideanProduct and keep Coquelicot's product norm, so they
      are the Euclidean norm of all entries, as in the original, and not
      MathComp's max norm (analysis/README.md, difference 1). Every bound
      therefore means the same, constants included. The bounds are stated
      with Stdlib's order, product, sum, power, inverse and INR around
      MathComp's norms, and Rabs stays Stdlib's.

   2. Order on indices. With ssreflect loaded, (a <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statements of joint_chaos_basis_norm, joint_chaos_first_norm and
      joint_chaos_second_norm write (a <= n)%coq_nat, which is Stdlib's le.
      The meaning is unchanged.

   The proofs follow the original. Coquelicot's norm_ge_0 becomes MathComp's
   normr_ge0, read in Stdlib's order through RleP, in the local tactic
   joint_norm_nonneg, which is not a lemma and is not visible to importers.
   Stdlib's "rewrite A, B" and "rewrite ... by tac" become ssreflect
   rewrites with the side conditions given as explicit arguments. *)

(* A norm is nonnegative, stated with Stdlib's order. *)
Local Ltac joint_norm_nonneg := apply/RleP; apply normr_ge0.

Theorem joint_gibbs_uniform n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists K0 K1 K2 : R, 0 <= K0 /\ 0 <= K1 /\ 0 <= K2 /\
  forall A U V W : matrix n,
    Rabs (trace_pair n U (matrix_nested_gradient n beta gamma offset coeff Y S A)) <=
      K0 * (`|U|)%R /\
    Rabs (trace_pair n U (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A V)) <=
      K1 * (`|U|)%R * (`|V|)%R /\
    Rabs (matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W) <=
      K2 * (`|U|)%R * (`|V|)%R * (`|W|)%R.
Proof.
  intros Hb Hg HY HS.
  destruct (growth_finite_coefficient_bound n coeff Y S) as [K [HK HC]].
  pose L := INR (Datatypes.S n) ^ 2 * K.
  assert (HL : 0 <= L) by (unfold L; apply Rmult_le_pos; [apply pow2_ge_0|exact HK]).
  assert (HT : forall y s, In y Y -> In s S -> forall P : matrix n,
    Rabs (trace_pair n (coeff y s) P) <= L * (`|P|)%R).
  { apply growth_trace_coefficient_bound; exact HC. }
  exists L, (2 * L ^ 2 * (beta + gamma)), (8 * L ^ 3 * (beta + gamma) ^ 2).
  split; [exact HL|].
  split.
  { apply Rmult_le_pos; [pose proof (pow2_ge_0 L); nra|lra]. }
  split.
  { apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow_le; exact HL]|apply pow2_ge_0]. }
  intros A U V W; split.
  - rewrite symmetric_trace_pair_comm matrix_nested_gradient_trace.
    unfold matrix_nested_derivative; apply growth_gibbs_mean_bound; [exact HY|].
    intros y Hy; unfold matrix_inner_derivative; apply growth_gibbs_mean_bound; [exact HS|].
    intros s Hs; apply HT; assumption.
  - split.
    + rewrite symmetric_trace_pair_comm.
      rewrite (matrix_nested_gradient_derivative_trace n beta gamma offset coeff Y S A U V
        Hb Hg HY HS).
      apply growth_matrix_second_bound; assumption.
    + apply growth_matrix_third_bound; assumption.
Qed.

Lemma joint_chaos_basis_norm n a : (a <= n)%coq_nat -> (`|chaos_basis n a|)%R = 1.
Proof.
  intro Ha; change ((`|operator_basis_vector n a|)%R = 1).
  apply operator_basis_vector_norm; exact Ha.
Qed.

Lemma joint_chaos_first_norm n (x : vector n) a : (a <= n)%coq_nat ->
  (`|chaos_first n x a|)%R <= (2 * INR (S n) ^ 2) * (`|x|)%R.
Proof.
  intro Ha; pose proof (matrix_component_chaos_first_norm n x a) as H.
  rewrite (joint_chaos_basis_norm n a Ha) in H; nra.
Qed.

Lemma joint_chaos_second_norm n a b : (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  (`|chaos_second n a b|)%R <= 2 * INR (S n) ^ 2.
Proof.
  intros Ha Hb.
  pose proof (quadratic_second_norm_bound n 1 (chaos_basis n a) (chaos_basis n b)) as H.
  rewrite quadratic_second_basis in H.
  assert (HE : matrix_scale n 1 (chaos_second n a b) = chaos_second n a b).
  { apply matrix_ext; intros i j Hi Hj; rewrite matrix_entry_scale; ring. }
  rewrite HE Rabs_R1 (joint_chaos_basis_norm n a Ha) (joint_chaos_basis_norm n b Hb) in H.
  nra.
Qed.

Theorem joint_divergence_uniform n beta gamma offset coeff Y S K :
  0 <= K ->
  (forall A U V : matrix n,
    Rabs (trace_pair n U (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A V))
      <= K * (`|U|)%R * (`|V|)%R) ->
  forall A : matrix n,
  Rabs (symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A))
    <= INR (Datatypes.S (goe_vector_index n)) * K.
Proof.
  intros HK HB A; rewrite -goe_basis_divergence.
  apply coordinate_sum_abs_bound; [exact HK|].
  intros k Hk; specialize (HB A (goe_basis n k) (goe_basis n k)).
  rewrite (goe_basis_unit_norm n k Hk) in HB; nra.
Qed.

Theorem joint_remainder_uniform n beta gamma offset coeff Y S K :
  0 <= K ->
  (forall A U V W : matrix n,
    Rabs (matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W)
      <= K * (`|U|)%R * (`|V|)%R * (`|W|)%R) ->
  forall (A : matrix n) (x : vector n),
    Rabs (chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S A) x)
      <= (/2 * INR (Datatypes.S n) ^ 2 * K * (2 * INR (Datatypes.S n) ^ 2) ^ 3) *
         (1 + (`|x|)%R) ^ 2.
Proof.
  intros HK HB A x.
  pose J := 2 * INR (Datatypes.S n) ^ 2.
  change (Rabs (chaos_contraction n (matrix_nested_third_derivative n beta gamma offset coeff Y S A) x)
      <= (/2 * INR (Datatypes.S n) ^ 2 * K * J ^ 3) * (1 + (`|x|)%R) ^ 2).
  assert (HJ : 0 <= J) by (unfold J; pose proof (pow2_ge_0 (INR (Datatypes.S n))); nra).
  assert (HL : 0 <= K * J ^ 3 * (`|x|)%R ^ 2).
  { apply Rmult_le_pos; [apply Rmult_le_pos; [exact HK|apply pow_le; exact HJ]|apply pow2_ge_0]. }
  assert (HC : forall a b, (a <= n)%coq_nat -> (b <= n)%coq_nat ->
    Rabs (matrix_nested_third_derivative n beta gamma offset coeff Y S A
      (chaos_first n x a) (chaos_first n x b) (chaos_second n a b)) <=
      K * J ^ 3 * (`|x|)%R ^ 2).
  { intros a b Ha Hb; eapply Rle_trans; [apply HB|].
    replace (K * J ^ 3 * (`|x|)%R ^ 2) with
      (K * (J * (`|x|)%R) * (J * (`|x|)%R) * J) by ring.
    apply Rmult_le_compat; try joint_norm_nonneg.
    - repeat apply Rmult_le_pos; try exact HK; joint_norm_nonneg.
    - apply Rmult_le_compat; try joint_norm_nonneg.
      + apply Rmult_le_pos; [exact HK|joint_norm_nonneg].
      + apply Rmult_le_compat_l; [exact HK|apply joint_chaos_first_norm; exact Ha].
      + apply joint_chaos_first_norm; exact Hb.
    - apply joint_chaos_second_norm; assumption. }
  assert (Hhalf : 0 <= /2) by lra.
  unfold chaos_contraction; rewrite Rabs_mult (Rabs_pos_eq (/2) Hhalf).
  eapply Rle_trans with
    (/2 * (INR (Datatypes.S n) * (INR (Datatypes.S n) * (K * J ^ 3 * (`|x|)%R ^ 2)))).
  - apply Rmult_le_compat_l; [lra|].
    apply coordinate_sum_abs_bound; [apply Rmult_le_pos; [apply pos_INR|exact HL]|].
    intros a Ha; apply coordinate_sum_abs_bound; [exact HL|intros b Hb; apply HC; assumption].
  - replace (/2 * (INR (Datatypes.S n) * (INR (Datatypes.S n) * (K * J ^ 3 * (`|x|)%R ^ 2))))
      with ((/2 * INR (Datatypes.S n) ^ 2 * K * J ^ 3) * (`|x|)%R ^ 2) by ring.
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|exact HK]|apply pow_le; exact HJ].
    + assert (Hx : 0 <= (`|x|)%R) by joint_norm_nonneg.
      nra.
Qed.
