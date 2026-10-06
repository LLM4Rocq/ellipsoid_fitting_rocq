From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import QuadraticGrowthProofs.
From EllipsoidFitting Require Import MatrixDefinitions.
From EllipsoidFitting Require Import MatrixCoordinates.
From EllipsoidFitting Require Import OperatorDefinitions.
From EllipsoidFitting Require Import SecondChaosDefinitions.
From EllipsoidFitting Require Import GradientDefinitions.
From EllipsoidFitting Require Import HessianDefinitions.
From EllipsoidFitting Require Import ContinuityDefinitions.
From EllipsoidFitting Require Import CoefficientDefinitions.
From EllipsoidFitting Require Import CoefficientMaps.
From EllipsoidFitting Require Import MatrixHessian.
From EllipsoidFitting Require Import MatrixThirdContinuity.
From EllipsoidFitting Require Import QuadraticDefinitions.
From EllipsoidFitting Require Import QuadraticCalculus.
Import QuadraticGrowthProofs.QuadraticUniformBounds.
Import QuadraticGrowthProofs.QuadraticPolynomialGrowth.
Import QuadraticGrowthProofs.QuadraticGrowthContinuity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Regularity of matrix entries of derivatives of the nested gradient along
   the quadratic family quadratic_matrix n lambda C x, which is
   C + lambda * (x x^T - I). Here e_a is chaos_basis n a,
   chaos_first n x a = e_a x^T + x e_a^T and
   chaos_second n a b = e_a e_b^T + e_b e_a^T.
   - matrix_component_chaos_first_quadratic, _continuous and _norm:
     chaos_first n x a is quadratic_first n 1 x e_a, it is continuous in x,
     and its norm is at most 2 * (n + 1) ^ 2 * `|x| * `|e_a|.
   - quadratic_divergence_component_regular: entry (a, b) of the derivative
     of the nested gradient at quadratic_matrix n lambda C x, in the
     direction chaos_second n a b, is continuous and bounded in x.
   - quadratic_chaos_component_regular: entry (a, b) of the second
     derivative of the nested gradient at quadratic_matrix n lambda C x, in
     the directions chaos_first n x a and chaos_first n x b, is continuous
     in x and at most K * (1 + `|x|) ^ 2 in absolute value.
   The norms are the Euclidean norm on vector n and the Frobenius norm on
   matrix n. *)

Lemma matrix_component_chaos_first_quadratic n (x : vector n) a :
  chaos_first n x a = quadratic_first n 1 x (chaos_basis n a).
Proof.
  rewrite quadratic_first_basis; unfold matrix_scale.
  rewrite scale1r; reflexivity.
Qed.

Lemma matrix_component_chaos_first_continuous n a (x : vector n) :
  {for x, continuous (fun z => chaos_first n z a)}.
Proof.
  have -> : (fun z => chaos_first n z a) =
    (fun z => quadratic_first n 1 z (chaos_basis n a)).
  { apply: funext => z; apply matrix_component_chaos_first_quadratic. }
  have [HD _] := quadratic_first_frechet n 1 x (chaos_basis n a).
  exact (differentiable_continuous HD).
Qed.

Lemma matrix_component_chaos_first_norm n (x : vector n) a :
  (`|chaos_first n x a|)%R <=
    (2 * INR (S n) ^ 2) * (`|x|)%R * (`|chaos_basis n a|)%R.
Proof.
  rewrite matrix_component_chaos_first_quadratic.
  pose proof (quadratic_first_norm_bound n 1 x (chaos_basis n a)) as H.
  rewrite Rabs_R1 in H; nra.
Qed.

Theorem quadratic_divergence_component_regular n beta gamma offset coeff Y S lambda C a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  (forall x : vector n, {for x, continuous (fun z => matrix_entry n
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C z) (chaos_second n a b)) a b)}) /\
  exists K : R, 0 <= K /\ forall x : vector n,
    Rabs (matrix_entry n
      (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (chaos_second n a b)) a b)
      <= K * (1 + (`|x|)%R) ^ 0.
Proof.
  intros Hb Hg HY HS Ha Hbb; split.
  - intro x.
    have HQ : {for x, continuous (quadratic_matrix n lambda C)}.
    { have [HD _] := quadratic_matrix_frechet n lambda C x.
      exact (differentiable_continuous HD). }
    have HG : {for quadratic_matrix n lambda C x, continuous
        (fun M => matrix_nested_gradient_derivative n beta gamma offset coeff Y S M
          (chaos_second n a b))}.
    { have [HD _] := matrix_nested_gradient_second_frechet n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (chaos_second n a b) Hb Hg HY HS.
      exact (differentiable_continuous HD). }
    have HE := @growth_linear_continuous (matrix_NormedModule n) R^o
      (fun M => matrix_entry n M a b)
      (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (chaos_second n a b))
      (matrix_entry_linear n a b).
    exact (@continuous_comp (vector n) (matrix n) R _ (fun M => matrix_entry n M a b) x
      (@continuous_comp (vector n) (matrix n) (matrix n) _ _ x HQ HG) HE).
  - destruct (growth_finite_coefficient_bound n coeff Y S) as [K [HK HC]].
    set (D := INR (Datatypes.S n) ^ 2 * K).
    assert (HD : 0 <= D).
    { unfold D; apply Rmult_le_pos; [apply pow2_ge_0|exact HK]. }
    assert (HL : forall y s, In y Y -> In s S -> forall P : matrix n,
      Rabs (trace_pair n (coeff y s) P) <= D * (`|P|)%R).
    { apply growth_trace_coefficient_bound; exact HC. }
    set (B := INR (Datatypes.S n) ^ 2 * (2 * D ^ 2 * (beta + gamma))).
    assert (HB : 0 <= B).
    { unfold B; apply Rmult_le_pos; [apply pow2_ge_0|].
      apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|lra]. }
    exists (B * (`|chaos_second n a b|)%R); split.
    + apply Rmult_le_pos; [exact HB|apply/RleP; apply normr_ge0].
    + intro x; replace (B * (`|chaos_second n a b|)%R * (1 + (`|x|)%R) ^ 0)
        with (B * (`|chaos_second n a b|)%R) by ring.
      apply growth_gradient_first_entry_bound; assumption.
Qed.

Theorem quadratic_chaos_component_regular n beta gamma offset coeff Y S lambda C a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  (forall x : vector n, {for x, continuous (fun z => matrix_entry n
    (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C z) (chaos_first n z a) (chaos_first n z b)) a b)}) /\
  exists K : R, 0 <= K /\ forall x : vector n,
    Rabs (matrix_entry n
      (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (chaos_first n x a) (chaos_first n x b)) a b)
      <= K * (1 + (`|x|)%R) ^ 2.
Proof.
  intros Hb Hg HY HS Ha Hbb; split.
  - intro x.
    have HQ : {for x, continuous (quadratic_matrix n lambda C)}.
    { have [HD _] := quadratic_matrix_frechet n lambda C x.
      exact (differentiable_continuous HD). }
    have HT : {for x, continuous (fun z => matrix_nested_third_coefficients n beta gamma
      offset coeff Y S (quadratic_matrix n lambda C z))}.
    { exact (@continuous_comp (vector n) (matrix n) (third_array n) _ _ x HQ
        (matrix_third_coefficients_continuous n beta gamma offset coeff Y S
          (quadratic_matrix n lambda C x) Hg HY HS)). }
    have HF : {for x, continuous (fun z => hessian_action n
        (third_action n (matrix_nested_third_coefficients n beta gamma offset coeff Y S
          (quadratic_matrix n lambda C z)) (chaos_first n z b)) (chaos_first n z a))}.
    { apply: growth_hessian_action_continuous.
      - apply: growth_third_action_continuous; [exact HT|].
        apply matrix_component_chaos_first_continuous.
      - apply matrix_component_chaos_first_continuous. }
    have HQE : (fun z => hessian_action n
        (third_action n (matrix_nested_third_coefficients n beta gamma offset coeff Y S
          (quadratic_matrix n lambda C z)) (chaos_first n z b)) (chaos_first n z a)) =
      (fun z => matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C z) (chaos_first n z a) (chaos_first n z b)).
    { apply: funext => z.
      rewrite actual_third_action // matrix_nested_hessian_derivative_action //. }
    rewrite HQE in HF.
    have HE := @growth_linear_continuous (matrix_NormedModule n) R^o
      (fun M => matrix_entry n M a b)
      (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (chaos_first n x a) (chaos_first n x b))
      (matrix_entry_linear n a b).
    exact (@continuous_comp (vector n) (matrix n) R _ (fun M => matrix_entry n M a b) x
      HF HE).
  - destruct (growth_finite_coefficient_bound n coeff Y S) as [K [HK HC]].
    set (D := INR (Datatypes.S n) ^ 2 * K).
    assert (HD : 0 <= D).
    { unfold D; apply Rmult_le_pos; [apply pow2_ge_0|exact HK]. }
    assert (HL : forall y s, In y Y -> In s S -> forall P : matrix n,
      Rabs (trace_pair n (coeff y s) P) <= D * (`|P|)%R).
    { apply growth_trace_coefficient_bound; exact HC. }
    set (B := INR (Datatypes.S n) ^ 2 * (8 * D ^ 3 * (beta + gamma) ^ 2)).
    set (J := 2 * INR (Datatypes.S n) ^ 2).
    assert (HB : 0 <= B).
    { unfold B; apply Rmult_le_pos; [apply pow2_ge_0|].
      apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow_le; exact HD]|apply pow2_ge_0]. }
    assert (HJ : 0 <= J) by (unfold J; pose proof (pow2_ge_0 (INR (Datatypes.S n))); nra).
    have Hna : 0 <= (`|chaos_basis n a|)%R by apply/RleP; apply normr_ge0.
    have Hnb : 0 <= (`|chaos_basis n b|)%R by apply/RleP; apply normr_ge0.
    set (L := B * J ^ 2 * (`|chaos_basis n a|)%R * (`|chaos_basis n b|)%R).
    assert (HL0 : 0 <= L).
    { unfold L; apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos;
        [exact HB|apply pow2_ge_0]|exact Hna]|exact Hnb]. }
    exists L; split; [exact HL0|]; intro x.
    pose proof (growth_gradient_second_entry_bound n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_first n x a) (chaos_first n x b)
      a b D Hb Hg HY HS Ha Hbb HD HL) as H.
    eapply Rle_trans; [exact H|].
    change (B * (`|chaos_first n x a|)%R * (`|chaos_first n x b|)%R <=
      L * (1 + (`|x|)%R) ^ 2).
    have Hx : 0 <= (`|x|)%R by apply/RleP; apply normr_ge0.
    have Hfa : 0 <= (`|chaos_first n x a|)%R by apply/RleP; apply normr_ge0.
    have Hfb : 0 <= (`|chaos_first n x b|)%R by apply/RleP; apply normr_ge0.
    eapply Rle_trans with (L * (`|x|)%R ^ 2).
    + replace (L * (`|x|)%R ^ 2) with
        (B * ((J * (`|x|)%R * (`|chaos_basis n a|)%R) *
          (J * (`|x|)%R * (`|chaos_basis n b|)%R))) by (unfold L; ring).
      rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact HB|].
      apply Rmult_le_compat; [exact Hfa|exact Hfb| |];
        apply matrix_component_chaos_first_norm.
    + apply Rmult_le_compat_l; [exact HL0|nra].
Qed.

