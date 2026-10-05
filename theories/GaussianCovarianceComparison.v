(* Comparison of Gaussian expectations by interpolation. Let X = P xi and
   Y = Q eta be the Gaussian vectors of R^K of GaussianCovarianceDefinitions,
   and let f be continuous with continuous first and second partial
   derivatives, f and these derivatives all bounded by
   C * prod_i (1 + |x_i|) ^ r (finite_polynomial_bound). If the pairing of
   the covariance difference P P^T - Q Q^T with the Hessian of f is
   nonnegative at every point of R^K, then E f(Y) <= E f(X)
   (gaussian_covariance_comparison).

   Proof. phi(t) = E f(Z(t)) along the interpolation path Z(t) is
   continuous within [0, 1] at 0 and at 1 (GaussianCovarianceEndpoints).
   On (0, 1) its derivative is one half of the pairing of the expectations
   of the second partial derivatives (GaussianCovarianceDerivative). That
   pairing is the expectation of the pointwise pairing, so it is
   nonnegative, and unit_interval_derivative_nonpositive of
   WeightedComparison, applied to - phi, gives phi(0) <= phi(1), that is
   E f(Y) <= E f(X) by the endpoint identities.

   This module loads MathComp through AnalysisBridge2; %coq_nat marks
   Stdlib's order on nat, and the arithmetic on R is Stdlib's, with
   R_scope opened last. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianFiniteSums WeightedComparison
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCovariancePath GaussianCovarianceDomains GaussianCovarianceEndpoints
  GaussianCovarianceDerivative.
Import ListNotations.
Open Scope R_scope.

(* The pairing of expectations is the expectation of the pairing. *)
Lemma gaussian_covariance_pairing_expectation K p q P Q (H : nat -> nat -> list R -> R) t :
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_iterated_integrable (p + q)%coq_nat
      (fun zs => H a b (gaussian_covariance_path K p q P Q t zs))) ->
  gaussian_iterated_integrable (p + q)%coq_nat
    (fun zs => gaussian_covariance_pairing K p q P Q
      (fun a b => H a b (gaussian_covariance_path K p q P Q t zs))) /\
  gaussian_covariance_pairing K p q P Q (fun a b =>
    gaussian_iterated_expectation (p + q)%coq_nat
      (fun zs => H a b (gaussian_covariance_path K p q P Q t zs))) =
  gaussian_iterated_expectation (p + q)%coq_nat
    (fun zs => gaussian_covariance_pairing K p q P Q
      (fun a b => H a b (gaussian_covariance_path K p q P Q t zs))).
Proof.
  intros Hint; unfold gaussian_covariance_pairing.
  assert (Hb : forall a, (a < K)%coq_nat -> forall b, In b (List.seq 0 K) ->
    gaussian_iterated_integrable (p + q)%coq_nat (fun zs =>
      (gaussian_covariance_entry p P a b - gaussian_covariance_entry q Q a b) *
      H a b (gaussian_covariance_path K p q P Q t zs))).
  { intros a Ha b Hb; apply in_seq_lt in Hb.
    exact (proj1 (gaussian_iterated_scale _ _ _ (Hint a b Ha Hb))). }
  assert (Ha : forall a, In a (List.seq 0 K) ->
    gaussian_iterated_integrable (p + q)%coq_nat (fun zs => finite_sum (fun b =>
      (gaussian_covariance_entry p P a b - gaussian_covariance_entry q Q a b) *
      H a b (gaussian_covariance_path K p q P Q t zs)) (List.seq 0 K))).
  { intros a Ha; apply in_seq_lt in Ha.
    exact (proj1 (gaussian_iterated_finite_sum _ _ _ (Hb a Ha))). }
  split; [exact (proj1 (gaussian_iterated_finite_sum _ _ _ Ha))|].
  rewrite (proj2 (gaussian_iterated_finite_sum _ _ _ Ha)).
  apply finite_sum_ext; intros a Ha'; apply in_seq_lt in Ha'.
  rewrite (proj2 (gaussian_iterated_finite_sum _ _ _ (Hb a Ha'))).
  apply finite_sum_ext; intros b Hb'; apply in_seq_lt in Hb'.
  rewrite (proj2 (gaussian_iterated_scale _ _ _ (Hint a b Ha' Hb'))); reflexivity.
Qed.

Theorem gaussian_covariance_comparison K p q (P Q : nat -> nat -> R) (f : list R -> R)
    (Df : nat -> list R -> R) (D2f : nat -> nat -> list R -> R) (C : R) (r : nat) :
  finite_joint_continuous K f ->
  (forall a, (a < K)%coq_nat -> finite_coordinate_derivative K a f (Df a)) ->
  (forall a, (a < K)%coq_nat -> finite_joint_continuous K (Df a)) ->
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    finite_coordinate_derivative K b (Df a) (D2f a b)) ->
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat -> finite_joint_continuous K (D2f a b)) ->
  finite_polynomial_bound K C r f ->
  (forall a, (a < K)%coq_nat -> finite_polynomial_bound K C r (Df a)) ->
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    finite_polynomial_bound K C r (D2f a b)) ->
  (forall u, List.length u = K ->
    0 <= gaussian_covariance_pairing K p q P Q (fun a b => D2f a b u)) ->
  gaussian_iterated_expectation q (fun ys => f (gaussian_covariance_image K q Q ys)) <=
  gaussian_iterated_expectation p (fun xs => f (gaussian_covariance_image K p P xs)).
Proof.
  intros Hf HD HDc HD2 HD2c Hfb HDb HD2b Hsign.
  set (phi := fun t => gaussian_iterated_expectation (p + q)%coq_nat
    (fun zs => f (gaussian_covariance_path K p q P Q t zs))).
  set (dphi := fun t => / 2 * gaussian_covariance_pairing K p q P Q (fun a b =>
    gaussian_iterated_expectation (p + q)%coq_nat
      (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs)))).
  assert (Hc0 : (phi @ within (fun t => 0 <= t <= 1) (nbhs 0) --> phi 0)%classic).
  { exact (gaussian_covariance_expectation_continuous_within K p q P Q f Df C r 0
      ltac:(lra) Hf HD HDc Hfb HDb). }
  assert (Hc1 : (phi @ within (fun t => 0 <= t <= 1) (nbhs 1) --> phi 1)%classic).
  { exact (gaussian_covariance_expectation_continuous_within K p q P Q f Df C r 1
      ltac:(lra) Hf HD HDc Hfb HDb). }
  assert (Hder : forall t, 0 < t < 1 -> @is_derive R R^o R^o t 1 phi (dphi t)).
  { intros t Ht.
    exact (gaussian_covariance_derivative_clause K p q P Q f Df D2f C r Hf HD HDc HD2 HD2c
      Hfb HDb HD2b t Ht). }
  assert (Hsg : forall t, 0 < t < 1 -> 0 <= dphi t).
  { intros t Ht; unfold dphi.
    apply Rmult_le_pos; [lra|].
    assert (Hint : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
      gaussian_iterated_integrable (p + q)%coq_nat
        (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs))).
    { intros a b Ha Hb.
      exact (proj1 (gaussian_covariance_path_domain K p q P Q (D2f a b) C r t ltac:(lra)
        (HD2c a b Ha Hb) (HD2b a b Ha Hb))). }
    destruct (gaussian_covariance_pairing_expectation K p q P Q D2f t Hint) as [Hi Heq].
    rewrite Heq.
    apply gaussian_iterated_nonnegative; [exact Hi|].
    intros zs _; apply Hsign.
    unfold gaussian_covariance_path; apply length_map_seq. }
  assert (Hn0 : ((fun t => - phi t) @ within (fun t => 0 <= t <= 1) (nbhs 0) --> - phi 0)%classic).
  { apply weighted_comparison_within_Reals; intros eps Heps.
    destruct (proj1 (weighted_comparison_within_Reals phi _ 0 (phi 0)) Hc0 eps Heps)
      as [delta [Hd Hdel]].
    exists delta; split; [exact Hd|].
    intros y Hy HDy.
    replace (- phi y - - phi 0) with (- (phi y - phi 0)) by ring.
    rewrite Rabs_Ropp; apply Hdel; assumption. }
  assert (Hn1 : ((fun t => - phi t) @ within (fun t => 0 <= t <= 1) (nbhs 1) --> - phi 1)%classic).
  { apply weighted_comparison_within_Reals; intros eps Heps.
    destruct (proj1 (weighted_comparison_within_Reals phi _ 1 (phi 1)) Hc1 eps Heps)
      as [delta [Hd Hdel]].
    exists delta; split; [exact Hd|].
    intros y Hy HDy.
    replace (- phi y - - phi 1) with (- (phi y - phi 1)) by ring.
    rewrite Rabs_Ropp; apply Hdel; assumption. }
  assert (Hneg : forall t, 0 < t < 1 -> - dphi t <= 0).
  { intros t Ht; pose proof (Hsg t Ht); lra. }
  pose proof (unit_interval_derivative_nonpositive (fun t => - phi t) (fun t => - dphi t)
    Hn0 Hn1 (fun t Ht => is_derive_opp _ _ _ (Hder t Ht)) Hneg) as Hmono.
  pose proof (gaussian_covariance_endpoint_one K p q P Q f) as H1.
  pose proof (gaussian_covariance_endpoint_zero K p q P Q f) as H0.
  unfold phi in Hmono; lra.
Qed.
