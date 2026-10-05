(* Gaussian expectations of smooth tests are invariant under loadings
   with orthonormal rows. The equal covariance identity is the checked
   paper_main_covariance_equal_expectation, obtained from
   gaussian_covariance_comparison in both directions with zero covariance
   pairing, and its identity specialization is
   paper_main_gaussian_standard_covariance_expectation. A d-by-d loading O
   has orthonormal rows when its covariance entries are those of the
   identity loading. Then
     E_d f(O xs) = E_d f,   O xs = gaussian_covariance_image d d O xs,
   for every C2 test f whose value and first and second coordinate
   derivatives satisfy the existing finite polynomial bounds. No rotation
   law, spectral decomposition or diagonalization is used. The identity is
   only claimed for such tests here. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateSteinDomains
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCovarianceDomains PaperMainGaussianCovarianceBounds
  PaperMainGaussianCovarianceMarginals PaperMainGaussianSmoothCovariance.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_orthonormal_rows d (O : nat -> nat -> R) : Prop :=
  forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    gaussian_covariance_entry d O a b = if Nat.eqb a b then 1 else 0.

Lemma paper_main_gaussian_orthonormal_rows_identity_covariance d O :
  paper_main_gaussian_orthonormal_rows d O ->
  forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    gaussian_covariance_entry d O a b = paper_main_gaussian_identity b a.
Proof.
intros HO a b Ha Hb; exact (HO a b Ha Hb).
Qed.

Lemma paper_main_gaussian_identity_orthonormal_rows d :
  paper_main_gaussian_orthonormal_rows d paper_main_gaussian_identity.
Proof.
intros a b Ha Hb; exact (paper_main_gaussian_identity_covariance d a b Ha).
Qed.

(* Rows of norm one have entries of absolute value at most one. *)
Lemma paper_main_gaussian_orthonormal_rows_entry_bound d O :
  paper_main_gaussian_orthonormal_rows d O ->
  forall a k, (a < d)%coq_nat -> (k < d)%coq_nat -> Rabs (O a k) <= 1.
Proof.
intros HO a k Ha Hk.
assert (Hsq : O a k * O a k <= 1).
{ transitivity (gaussian_covariance_entry d O a a);
    [|rewrite (HO a a Ha Ha) Nat.eqb_refl; lra].
  unfold gaussian_covariance_entry.
  rewrite <- (finite_sum_delta d k (O a k * O a k) Hk).
  apply finite_sum_le; intros j _.
  destruct (Nat.eqb_spec j k) as [->|_]; [lra|].
  apply Rle_0_sqr. }
apply Rabs_le; nra.
Qed.

Lemma paper_main_gaussian_orthogonal_integrable d O (f : list R -> R) C r :
  finite_joint_continuous d f -> finite_polynomial_bound d C r f ->
  gaussian_iterated_integrable d (fun xs => f (gaussian_covariance_image d d O xs)) /\
  gaussian_iterated_absolutely_integrable d
    (fun xs => f (gaussian_covariance_image d d O xs)).
Proof.
intros Hf Hb.
destruct (gaussian_covariance_image_domain d d O f C r Hf Hb) as [HI [HA _]].
split; assumption.
Qed.

Theorem paper_main_gaussian_orthogonal_expectation d (O : nat -> nat -> R)
    (f : list R -> R) (Df : nat -> list R -> R) (D2f : nat -> nat -> list R -> R)
    (C : R) (r : nat) :
  paper_main_gaussian_orthonormal_rows d O ->
  finite_joint_continuous d f ->
  (forall a, (a < d)%coq_nat -> finite_coordinate_derivative d a f (Df a)) ->
  (forall a, (a < d)%coq_nat -> finite_joint_continuous d (Df a)) ->
  (forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_coordinate_derivative d b (Df a) (D2f a b)) ->
  (forall a b, (a < d)%coq_nat -> (b < d)%coq_nat -> finite_joint_continuous d (D2f a b)) ->
  finite_polynomial_bound d C r f ->
  (forall a, (a < d)%coq_nat -> finite_polynomial_bound d C r (Df a)) ->
  (forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_polynomial_bound d C r (D2f a b)) ->
  gaussian_iterated_expectation d (fun xs => f (gaussian_covariance_image d d O xs)) =
  gaussian_iterated_expectation d f.
Proof.
intros HO Hf HD HDc HD2 HD2c Hfb HDb HD2b.
exact (paper_main_gaussian_standard_covariance_expectation d f Df D2f C r
  Hf HD HDc HD2 HD2c Hfb HDb HD2b d O
  (paper_main_gaussian_orthonormal_rows_identity_covariance d O HO)).
Qed.

Theorem paper_main_gaussian_orthogonal_smooth_expectation d O f Df D2f C r :
  paper_main_gaussian_orthonormal_rows d O ->
  paper_main_gaussian_smooth_test d f Df D2f C r ->
  gaussian_iterated_expectation d (fun xs => f (gaussian_covariance_image d d O xs)) =
  gaussian_iterated_expectation d f.
Proof.
intros HO [Hf HD HDc HD2 HD2c Hfb HDb HD2b].
exact (paper_main_gaussian_orthogonal_expectation d O f Df D2f C r HO
  Hf HD HDc HD2 HD2c Hfb HDb HD2b).
Qed.

(* Two loadings with orthonormal rows give the same expectations. *)
Corollary paper_main_gaussian_orthogonal_pair_expectation d O1 O2 f Df D2f C r :
  paper_main_gaussian_orthonormal_rows d O1 ->
  paper_main_gaussian_orthonormal_rows d O2 ->
  paper_main_gaussian_smooth_test d f Df D2f C r ->
  gaussian_iterated_expectation d (fun xs => f (gaussian_covariance_image d d O1 xs)) =
  gaussian_iterated_expectation d (fun xs => f (gaussian_covariance_image d d O2 xs)).
Proof.
intros H1 H2 Hs.
rewrite (paper_main_gaussian_orthogonal_smooth_expectation d O1 f Df D2f C r H1 Hs).
symmetry; exact (paper_main_gaussian_orthogonal_smooth_expectation d O2 f Df D2f C r H2 Hs).
Qed.
