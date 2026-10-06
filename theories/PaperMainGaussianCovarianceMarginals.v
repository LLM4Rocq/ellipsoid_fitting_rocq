(* The identity loading paper_main_gaussian_identity: its image of a list of
   d values is the list itself (paper_main_gaussian_identity_image), and its
   covariance entries are those of the identity matrix. So a loading whose
   covariance entries are those of the identity gives the test f the same
   expectation as the standard Gaussian vector
   (paper_main_gaussian_standard_covariance_expectation, from
   paper_main_covariance_equal_expectation). *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  PaperMainGaussianCovarianceBounds.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_identity (a k : nat) : R :=
  if Nat.eqb k a then 1 else 0.

Lemma paper_main_gaussian_identity_row d a xs :
  (a < d)%coq_nat ->
  gaussian_covariance_row d paper_main_gaussian_identity a xs = List.nth a xs 0.
Proof.
intros Ha; unfold gaussian_covariance_row, paper_main_gaussian_identity.
transitivity (finite_sum (fun k => if Nat.eqb k a then List.nth a xs 0 else 0) (List.seq 0 d)).
- apply finite_sum_ext; intros k Hk; destruct (Nat.eqb k a) eqn:E.
  + apply Nat.eqb_eq in E; subst k; ring.
  + ring.
- apply finite_sum_delta; exact Ha.
Qed.

Lemma paper_main_gaussian_identity_image d xs :
  List.length xs = d ->
  gaussian_covariance_image d d paper_main_gaussian_identity xs = xs.
Proof.
intros Hxs; apply (nth_ext _ _ 0 0).
- unfold gaussian_covariance_image; rewrite length_map_seq; symmetry; exact Hxs.
- intros a Ha; unfold gaussian_covariance_image in *.
  rewrite length_map_seq in Ha.
  rewrite nth_map_seq; [exact Ha|apply paper_main_gaussian_identity_row; exact Ha].
Qed.

Lemma paper_main_gaussian_identity_covariance d a b :
  (a < d)%coq_nat ->
  gaussian_covariance_entry d paper_main_gaussian_identity a b =
  paper_main_gaussian_identity b a.
Proof.
intros Ha; unfold gaussian_covariance_entry, paper_main_gaussian_identity.
transitivity (finite_sum (fun k => if Nat.eqb k a then
  (if Nat.eqb a b then 1 else 0) else 0) (List.seq 0 d)).
- apply finite_sum_ext; intros k Hk; destruct (Nat.eqb k a) eqn:E.
  + apply Nat.eqb_eq in E; subst k; ring.
  + ring.
- apply finite_sum_delta; exact Ha.
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

Theorem paper_main_gaussian_standard_covariance_expectation p P :
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_covariance_entry p P a b = paper_main_gaussian_identity b a) ->
  gaussian_iterated_expectation p (fun xs => f (gaussian_covariance_image K p P xs)) =
  gaussian_iterated_expectation K f.
Proof.
intros Hcov.
transitivity (gaussian_iterated_expectation K
  (fun xs => f (gaussian_covariance_image K K paper_main_gaussian_identity xs))).
- apply (paper_main_covariance_equal_expectation K f Df D2f C r
    Hf HD HDc HD2 HD2c Hfb HDb HD2b).
  intros a b Ha Hb; rewrite Hcov; [exact Ha|exact Hb|].
  symmetry; apply paper_main_gaussian_identity_covariance; exact Ha.
- apply gaussian_iterated_expectation_ext; intros xs Hxs.
  rewrite (paper_main_gaussian_identity_image K xs Hxs); reflexivity.
Qed.

End SmoothFunction.
