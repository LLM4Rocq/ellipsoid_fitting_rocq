(* Differentiation of exponential moments for bounded continuous tests.
   The Gaussian parameter theorem supplies integrability and differentiation;
   the scalar majorants are uniform on a neighbourhood of each real parameter. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2
  GaussianProductDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianCoordinatePolynomialContinuity
  FiniteGaussianParameter PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothExponential PaperMainGaussianSmoothCovariance
  PaperMainGaussianExponentialCovariance.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_exp_monotone x y : x <= y -> exp x <= exp y.
Proof.
intros H; destruct (Rle_lt_or_eq_dec _ _ H) as [Hlt|He].
- apply Rlt_le, exp_increasing; exact Hlt.
- rewrite He; apply Rle_refl.
Qed.

Lemma paper_main_gaussian_exp_parameter_derivative x t :
  @is_derive R R^o R^o t 1 (fun s => exp (s * x)) (x * exp (t * x)).
Proof.
pose proof (is_derive_scal_l x (fun s => s) t 1 (is_derive_id_R t)) as Hlin.
rewrite Rmult_1_l in Hlin.
pose proof (is_derive_exp_comp (fun s => s * x) t x Hlin) as H.
replace (x * exp (t * x)) with (exp (t * x) * x) by ring; exact H.
Qed.

Lemma paper_main_gaussian_exp_parameter_second x t :
  @is_derive R R^o R^o t 1 (fun s => x * exp (s * x)) (x ^ 2 * exp (t * x)).
Proof.
pose proof (is_derive_scal x (fun s => exp (s * x)) t
  (x * exp (t * x)) (paper_main_gaussian_exp_parameter_derivative x t)) as H.
replace (x ^ 2 * exp (t * x)) with (x * (x * exp (t * x))) by ring; exact H.
Qed.

Lemma paper_main_gaussian_exp_parameter_bounds M a t x :
  0 <= M -> Rabs x <= M -> Rabs (t - a) <= 1 ->
  Rabs (exp (t * x)) <= exp ((Rabs a + 1) * M) /\
  Rabs (x * exp (t * x)) <= M * exp ((Rabs a + 1) * M) /\
  Rabs (x ^ 2 * exp (t * x)) <= M ^ 2 * exp ((Rabs a + 1) * M).
Proof.
intros HM Hx Hta.
assert (Ht : Rabs t <= Rabs a + 1).
{ replace t with ((t - a) + a) at 1 by ring; pose proof (Rabs_triang (t - a) a); lra. }
assert (Htx : t * x <= (Rabs a + 1) * M).
{ pose proof (Rle_abs (t * x)) as Habs; rewrite Rabs_mult in Habs.
  pose proof (Rmult_le_compat (Rabs t) (Rabs a + 1) (Rabs x) M
    (Rabs_pos t) (Rabs_pos x) Ht Hx); lra. }
pose proof (paper_main_exp_monotone _ _ Htx) as HE.
assert (HE0 : 0 < exp (t * x)) by apply exp_pos.
assert (HMexp : 0 < exp ((Rabs a + 1) * M)) by apply exp_pos.
split; [rewrite (Rabs_pos_eq (exp (t * x)) ltac:(lra)); exact HE|].
split.
- rewrite Rabs_mult (Rabs_pos_eq (exp (t * x)) ltac:(lra)).
  apply Rmult_le_compat; [apply Rabs_pos|lra|exact Hx|exact HE].
- rewrite Rabs_mult (Rabs_pos_eq (exp (t * x)) ltac:(lra))
    (Rabs_pos_eq (x ^ 2) ltac:(nra)).
  apply Rmult_le_compat; [nra|lra| |exact HE].
  apply Rabs_le_between in Hx; nra.
Qed.

Theorem paper_main_gaussian_bounded_mgf_derivative d f M t :
  finite_joint_continuous d f -> finite_polynomial_bound d M 0 f ->
  @is_derive R R^o R^o t 1
    (fun s => gaussian_iterated_expectation d (fun xs => exp (s * f xs)))
    (gaussian_iterated_expectation d (fun xs => f xs * exp (t * f xs))).
Proof.
intros Hc Hb.
destruct (proj1 (paper_main_polynomial_zero_bound d M f) Hb) as [HM Hbf].
set (A := exp ((Rabs t + 1) * M)).
assert (HA : 0 < A) by (unfold A; apply exp_pos).
assert (HD : forall s xs, Rabs (s - t) <= 1 -> List.length xs = d ->
  @is_derive R R^o R^o s 1 (fun u => exp (u * f xs)) (f xs * exp (s * f xs))).
{ intros s xs Hs Hxs; apply paper_main_gaussian_exp_parameter_derivative. }
assert (HD2 : forall s xs, Rabs (s - t) <= 1 -> List.length xs = d ->
  @is_derive R R^o R^o s 1 (fun u => f xs * exp (u * f xs)) (f xs ^ 2 * exp (s * f xs))).
{ intros s xs Hs Hxs; apply paper_main_gaussian_exp_parameter_second. }
assert (Hbounds : forall s xs, Rabs (s - t) <= 1 -> List.length xs = d ->
  Rabs (exp (s * f xs)) <= A /\ Rabs (f xs * exp (s * f xs)) <= M * A /\
  Rabs (f xs ^ 2 * exp (s * f xs)) <= M ^ 2 * A).
{ intros s xs Hs Hxs; apply paper_main_gaussian_exp_parameter_bounds; [exact HM|apply Hbf; exact Hxs|exact Hs]. }
assert (Hb2 : forall s, Rabs (s - t) <= 1 ->
  finite_polynomial_bound d (M ^ 2 * A) 0 (fun xs => f xs ^ 2 * exp (s * f xs))).
{ intros s Hs; apply paper_main_polynomial_zero_bound; split; [apply Rmult_le_pos; nra|].
  intros xs Hxs; exact (proj2 (proj2 (Hbounds s xs Hs Hxs))). }
assert (Hbc : forall s, Rabs (s - t) <= 1 ->
  finite_joint_continuous d (fun xs => exp (s * f xs))).
{ intros s Hs; apply paper_main_gaussian_exp_continuous; exact Hc. }
assert (Hdc : finite_joint_continuous d (fun xs => f xs * exp (t * f xs))).
{ apply finite_joint_continuous_mult; [exact Hc|apply paper_main_gaussian_exp_continuous; exact Hc]. }
assert (Hb0 : forall s, Rabs (s - t) <= 1 ->
  finite_polynomial_bound d A 0 (fun xs => exp (s * f xs))).
{ intros s Hs; apply paper_main_polynomial_zero_bound; split; [lra|].
  intros xs Hxs; exact (proj1 (Hbounds s xs Hs Hxs)). }
assert (Hb1 : finite_polynomial_bound d (M * A) 0 (fun xs => f xs * exp (t * f xs))).
{ apply paper_main_polynomial_zero_bound; split; [apply Rmult_le_pos; lra|].
  intros xs Hxs; exact (proj1 (proj2 (Hbounds t xs ltac:(rewrite Rminus_diag Rabs_R0; lra) Hxs))). }
exact (proj2 (proj2 (finite_gaussian_parameter_differentiation d
  (fun s xs => exp (s * f xs)) (fun s xs => f xs * exp (s * f xs))
  (fun s xs => f xs ^ 2 * exp (s * f xs)) t 1 (M ^ 2 * A) 0 A 0 (M * A) 0
  ltac:(lra) HD HD2 Hb2 Hbc Hdc Hb0 Hb1))).
Qed.

Theorem paper_main_gaussian_bounded_mgf_differential d f Df D2f M L :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    SoftDefinitions.finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  forall t, 0 <= t ->
    @is_derive R R^o R^o t 1
      (fun s => gaussian_iterated_expectation d (fun xs => exp (s * f xs)))
      (gaussian_iterated_expectation d (fun xs => f xs * exp (t * f xs))) /\
    gaussian_iterated_expectation d (fun xs => f xs * exp (t * f xs)) <=
      (gaussian_iterated_expectation d f + t * L ^ 2) *
        gaussian_iterated_expectation d (fun xs => exp (t * f xs)).
Proof.
intros Hsmooth Hgrad t Ht; split.
- destruct Hsmooth as [Hc HD HDc HD2 HD2c Hb HDb HD2b].
  apply (paper_main_gaussian_bounded_mgf_derivative d f M t Hc Hb).
- pose proof (paper_main_gaussian_exponential_covariance d t f Df D2f M L Ht Hsmooth Hgrad).
  nra.
Qed.
