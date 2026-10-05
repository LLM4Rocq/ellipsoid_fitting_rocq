(* Clause 1 of the draft challenge gaussian_covariance_interpolation of the
   MathComp-Analysis port: the Gaussian domains of the test function and of its
   second partial derivatives along the interpolation path, and of the test
   function at the two endpoint vectors. Solver module written on 30 September
   2026 by a session that did not write the statement. Nothing here is reviewed
   or accepted.

   The path and the endpoint images are linear images of the coordinates
   (GaussianCovariancePath), so a continuous, polynomially bounded g composed
   with them is continuous and polynomially bounded (GaussianCovarianceLinear),
   with constants uniform in t on [0, 1], and
   gaussian_coordinate_polynomial_domain of GaussianCoordinateSteinDomains gives
   the four conjuncts of gaussian_covariance_domain, which are word for word
   those of gaussian_list_domain.

   This module loads MathComp through AnalysisBridge2; %coq_nat marks Stdlib's
   arithmetic on nat, and the arithmetic on R is Stdlib's, with R_scope opened
   last. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateSteinDomains GaussianCovarianceDefinitions
  GaussianCovarianceSums GaussianCovarianceLinear GaussianCovariancePath.
Import ListNotations.
Open Scope R_scope.

(* A common bound for the entries of P (a < K, k < p) and of Q (a < K, k < q). *)
Lemma gaussian_covariance_matrix_bound K p q (P Q : nat -> nat -> R) :
  exists M, 0 <= M /\
    (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) /\
    (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M).
Proof.
  destruct (finite_matrix_bound P K p) as [M1 [HM1 H1]].
  destruct (finite_matrix_bound Q K q) as [M2 [HM2 H2]].
  exists (Rmax M1 M2); split; [apply Rle_trans with M1; [exact HM1|apply Rmax_l]|split].
  - intros a k Ha Hk; apply Rle_trans with M1; [apply H1; assumption|apply Rmax_l].
  - intros a k Ha Hk; apply Rle_trans with M2; [apply H2; assumption|apply Rmax_r].
Qed.

Lemma gaussian_covariance_path_coef_uniform K p q P Q M t :
  0 <= t <= 1 ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  forall a k, (a < K)%coq_nat -> (k < (p + q)%coq_nat)%coq_nat ->
    Rabs (gaussian_covariance_coef p q P Q t a k) <= M.
Proof.
  intros Ht HP HQ a k Ha Hk.
  apply (gaussian_covariance_coef_bound p q P Q M t a k Ht Hk).
  - intros j Hj; apply HP; assumption.
  - intros j Hj; apply HQ; assumption.
Qed.

(* Regularity of g composed with the path, uniformly in t on [0, 1]. *)
Theorem gaussian_covariance_path_regular K p q P Q M (g : list R -> R) C r t :
  0 <= t <= 1 -> 0 <= M ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  finite_joint_continuous K g -> finite_polynomial_bound K C r g ->
  finite_joint_continuous (p + q)%coq_nat
    (fun zs => g (gaussian_covariance_path K p q P Q t zs)) /\
  finite_polynomial_bound (p + q)%coq_nat
    (C * (1 + M * INR (p + q)%coq_nat) ^ (r * K)%coq_nat) (r * K)%coq_nat
    (fun zs => g (gaussian_covariance_path K p q P Q t zs)).
Proof.
  intros Ht HM HP HQ Hg Hb.
  rewrite gaussian_covariance_path_linear; split.
  - apply linear_image_continuous_comp; exact Hg.
  - apply (linear_image_polynomial_bound_comp _ _ _ M _ _ _ HM); [|exact Hb].
    apply gaussian_covariance_path_coef_uniform; assumption.
Qed.

Theorem gaussian_covariance_path_domain K p q P Q (g : list R -> R) C r t :
  0 <= t <= 1 -> finite_joint_continuous K g -> finite_polynomial_bound K C r g ->
  gaussian_covariance_domain (p + q)%coq_nat
    (fun zs => g (gaussian_covariance_path K p q P Q t zs)).
Proof.
  intros Ht Hg Hb.
  destruct (gaussian_covariance_matrix_bound K p q P Q) as [M [HM [HP HQ]]].
  destruct (gaussian_covariance_path_regular K p q P Q M g C r t Ht HM HP HQ Hg Hb) as [Hc Hpb].
  exact (gaussian_coordinate_polynomial_domain _ _ _ _ Hc Hpb).
Qed.

(* Regularity of g composed with an endpoint image. *)
Theorem gaussian_covariance_image_regular K p P M (g : list R -> R) C r :
  0 <= M ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  finite_joint_continuous K g -> finite_polynomial_bound K C r g ->
  finite_joint_continuous p (fun xs => g (gaussian_covariance_image K p P xs)) /\
  finite_polynomial_bound p (C * (1 + M * INR p) ^ (r * K)%coq_nat) (r * K)%coq_nat
    (fun xs => g (gaussian_covariance_image K p P xs)).
Proof.
  intros HM HP Hg Hb.
  rewrite gaussian_covariance_image_linear; split.
  - apply linear_image_continuous_comp; exact Hg.
  - apply (linear_image_polynomial_bound_comp _ _ _ M _ _ _ HM HP Hb).
Qed.

Theorem gaussian_covariance_image_domain K p P (g : list R -> R) C r :
  finite_joint_continuous K g -> finite_polynomial_bound K C r g ->
  gaussian_covariance_domain p (fun xs => g (gaussian_covariance_image K p P xs)).
Proof.
  intros Hg Hb.
  destruct (finite_matrix_bound P K p) as [M [HM HP]].
  destruct (gaussian_covariance_image_regular K p P M g C r HM HP Hg Hb) as [Hc Hpb].
  exact (gaussian_coordinate_polynomial_domain _ _ _ _ Hc Hpb).
Qed.

(* Clause 1. *)
Theorem gaussian_covariance_domains K p q (P Q : nat -> nat -> R) (f : list R -> R)
    (D2f : nat -> nat -> list R -> R) (C : R) (r : nat) :
  finite_joint_continuous K f ->
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat -> finite_joint_continuous K (D2f a b)) ->
  finite_polynomial_bound K C r f ->
  (forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
    finite_polynomial_bound K C r (D2f a b)) ->
  (forall t, 0 <= t <= 1 ->
    gaussian_covariance_domain (p + q)%coq_nat
      (fun zs => f (gaussian_covariance_path K p q P Q t zs))) /\
  (forall t a b, 0 <= t <= 1 -> (a < K)%coq_nat -> (b < K)%coq_nat ->
    gaussian_covariance_domain (p + q)%coq_nat
      (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs))) /\
  gaussian_covariance_domain p (fun xs => f (gaussian_covariance_image K p P xs)) /\
  gaussian_covariance_domain q (fun ys => f (gaussian_covariance_image K q Q ys)).
Proof.
  intros Hf HD2 Hfb HD2b.
  split; [|split; [|split]].
  - intros t Ht; exact (gaussian_covariance_path_domain K p q P Q f C r t Ht Hf Hfb).
  - intros t a b Ht Ha Hb.
    exact (gaussian_covariance_path_domain K p q P Q (D2f a b) C r t Ht (HD2 a b Ha Hb)
      (HD2b a b Ha Hb)).
  - exact (gaussian_covariance_image_domain K p P f C r Hf Hfb).
  - exact (gaussian_covariance_image_domain K q Q f C r Hf Hfb).
Qed.
