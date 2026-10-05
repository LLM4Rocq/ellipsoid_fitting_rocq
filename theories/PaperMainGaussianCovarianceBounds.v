(* Quantitative consequences of the proved Gaussian covariance interpolation.
   The smoothness and growth hypotheses are analytic obligations, not axioms.
   This module does not yet prove Gaussian Lipschitz concentration. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianProductDefinitions GaussianProduct GaussianFiniteSums
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions WeightedComparison
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceDomains
  GaussianCovarianceEndpoints GaussianCovarianceDerivative
  GaussianCovarianceComparison.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_covariance_pairing_equal K p q P Q H :
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_covariance_entry p P a b = gaussian_covariance_entry q Q a b) ->
  gaussian_covariance_pairing K p q P Q H = 0.
Proof.
intros Hcov; unfold gaussian_covariance_pairing.
transitivity (finite_sum (fun _ => 0) (List.seq 0 K)); [|apply finite_sum_zero].
apply finite_sum_ext; intros a Ha; apply in_seq_lt in Ha.
transitivity (finite_sum (fun _ => 0) (List.seq 0 K)); [|apply finite_sum_zero].
apply finite_sum_ext; intros b Hb; apply in_seq_lt in Hb.
rewrite (Hcov a b Ha Hb); ring.
Qed.

Section SmoothFunction.
Variables (K : nat) (f : list R -> R) (Df : nat -> list R -> R)
  (D2f : nat -> nat -> list R -> R) (C : R) (r : nat).
Hypothesis Hf : finite_joint_continuous K f.
Hypothesis HD : forall a, (a < K)%coq_nat ->
  finite_coordinate_derivative K a f (Df a).
Hypothesis HDc : forall a, (a < K)%coq_nat ->
  finite_joint_continuous K (Df a).
Hypothesis HD2 : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_coordinate_derivative K b (Df a) (D2f a b).
Hypothesis HD2c : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_joint_continuous K (D2f a b).
Hypothesis Hfb : finite_polynomial_bound K C r f.
Hypothesis HDb : forall a, (a < K)%coq_nat ->
  finite_polynomial_bound K C r (Df a).
Hypothesis HD2b : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_polynomial_bound K C r (D2f a b).

Theorem paper_main_covariance_expected_hessian_bound p q P Q B :
  (forall t, 0 < t < 1 ->
    gaussian_covariance_pairing K p q P Q (fun a b =>
      gaussian_iterated_expectation (p + q)%coq_nat
        (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs))) <= 2 * B) ->
  gaussian_iterated_expectation p (fun xs => f (gaussian_covariance_image K p P xs)) -
  gaussian_iterated_expectation q (fun ys => f (gaussian_covariance_image K q Q ys)) <= B.
Proof.
intros Hb.
set (phi := fun t => gaussian_iterated_expectation (p + q)%coq_nat
  (fun zs => f (gaussian_covariance_path K p q P Q t zs))).
set (dphi := fun t => / 2 * gaussian_covariance_pairing K p q P Q (fun a b =>
  gaussian_iterated_expectation (p + q)%coq_nat
    (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs)))).
assert (HC : forall a, 0 <= a <= 1 ->
  (phi @ within (fun t => 0 <= t <= 1) (nbhs a) --> phi a)%classic).
{ intros a Ha; exact (gaussian_covariance_expectation_continuous_within
    K p q P Q f Df C r a Ha Hf HD HDc Hfb HDb). }
assert (HDphi : forall t, 0 < t < 1 -> @is_derive R R^o R^o t 1 phi (dphi t)).
{ intros t Ht; exact (gaussian_covariance_derivative_clause
    K p q P Q f Df D2f C r Hf HD HDc HD2 HD2c Hfb HDb HD2b t Ht). }
assert (HL : forall a, {for a, continuous (fun t : R => B * t)}).
{ intro a; apply (continuous_mult R (fun _ => B) (fun t => t) a);
    [apply (continuous_const R)|apply continuous_id]. }
assert (HDL : forall t, @is_derive R R^o R^o t 1 (fun s => B * s) B).
{ intro t.
  pose proof (is_derive_scal B (fun s => s) t 1 (is_derive_id_R t)) as Hlin.
  rewrite Rmult_1_r in Hlin; exact Hlin. }
pose proof (unit_interval_primitive_comparison phi dphi (fun t => B * t) (fun _ => B)
  (HC 0 ltac:(lra)) (HC 1 ltac:(lra)) (HL 0) (HL 1) HDphi
  (fun t _ => HDL t)) as Hend.
assert (Hsg : forall t, 0 < t < 1 -> dphi t <= B).
{ intros t Ht; unfold dphi; specialize (Hb t Ht); lra. }
specialize (Hend Hsg).
unfold phi in Hend.
rewrite gaussian_covariance_endpoint_one gaussian_covariance_endpoint_zero in Hend.
lra.
Qed.

Theorem paper_main_covariance_pointwise_hessian_bound p q P Q B :
  (forall u, List.length u = K ->
    gaussian_covariance_pairing K p q P Q (fun a b => D2f a b u) <= 2 * B) ->
  gaussian_iterated_expectation p (fun xs => f (gaussian_covariance_image K p P xs)) -
  gaussian_iterated_expectation q (fun ys => f (gaussian_covariance_image K q Q ys)) <= B.
Proof.
intros Hb; apply paper_main_covariance_expected_hessian_bound.
intros t Ht.
assert (Hint : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  gaussian_iterated_integrable (p + q)%coq_nat
    (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs))).
{ intros a b Ha Hb'.
  exact (proj1 (gaussian_covariance_path_domain K p q P Q (D2f a b) C r t ltac:(lra)
    (HD2c a b Ha Hb') (HD2b a b Ha Hb'))). }
destruct (gaussian_covariance_pairing_expectation K p q P Q D2f t Hint) as [Hi He].
rewrite He.
rewrite <- (proj2 (gaussian_iterated_constant (p + q)%coq_nat (2 * B))).
apply gaussian_iterated_monotone; [exact Hi|apply gaussian_iterated_constant|].
intros zs Hzs; apply Hb; unfold gaussian_covariance_path; apply length_map_seq.
Qed.

Theorem paper_main_covariance_equal_expectation p q P Q :
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_covariance_entry p P a b = gaussian_covariance_entry q Q a b) ->
  gaussian_iterated_expectation p (fun xs => f (gaussian_covariance_image K p P xs)) =
  gaussian_iterated_expectation q (fun ys => f (gaussian_covariance_image K q Q ys)).
Proof.
intros Hcov; apply Rle_antisym.
- apply (gaussian_covariance_comparison K q p Q P f Df D2f C r
    Hf HD HDc HD2 HD2c Hfb HDb HD2b).
  intros u Hu.
  rewrite (paper_main_covariance_pairing_equal K q p Q P (fun a b => D2f a b u)).
  + intros a b Ha Hb; symmetry; apply Hcov; assumption.
  + lra.
- apply (gaussian_covariance_comparison K p q P Q f Df D2f C r
    Hf HD HDc HD2 HD2c Hfb HDb HD2b).
  intros u Hu.
  rewrite (paper_main_covariance_pairing_equal K p q P Q (fun a b => D2f a b u) Hcov).
  lra.
Qed.
End SmoothFunction.
