(* Integrating out the last coordinate of a function F of S d coordinates
   that is continuous (finite_joint_continuous) and polynomially bounded
   (finite_polynomial_bound). Its marginal gaussian_last_marginal F is
   again continuous and polynomially bounded
   (gaussian_last_marginal_continuous,
   gaussian_last_marginal_polynomial_bound), such a function is integrable
   at every level of the iterated Gaussian expectation
   (gaussian_iterated_polynomial_integrable), and the absolute value of its
   expectation is at most C * gaussian_coordinate_weight_moment p ^ d
   (gaussian_iterated_polynomial_admissible). The integrability and the
   continuity come from the library through Gaussian.Law.LibraryBridge: the
   function x |-> F (list_of_row x) of a row vector is integrable against
   the standard Gaussian measure, and the expectation over the last
   coordinate is a parameter integral, continuous by dominated convergence. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Gaussian.Line.MajorantBound Analysis.CoordinateContinuityDefinitions
  Analysis.CoordinateTopology Gaussian.Coordinate.WeightDefinitions
  Gaussian.Coordinate.Weights Gaussian.Iterated.SuffixMarginalDefinitions
  Gaussian.Iterated.LastIntegration.
From EllipsoidFitting Require Gaussian.Law.LibraryBridge.
Import ListNotations.
Open Scope R_scope.

Lemma finite_polynomial_bound_abs d C p F :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => Rabs (F xs)).
Proof.
  intros [HC Hb]; split; [exact HC|].
  intros xs Hxs; rewrite Rabs_Rabsolu; apply Hb; exact Hxs.
Qed.

Lemma gaussian_last_section_polynomial_bound d F C p xs :
  finite_polynomial_bound (S d) C p F -> length xs = d ->
  forall t, Rabs (F (xs++[t])) <=
    (C*gaussian_coordinate_product_weight p xs)*gaussian_coordinate_weight p t.
Proof.
  intros [HC Hb] Hxs t.
  specialize (Hb (xs++[t]) ltac:(rewrite length_app,Hxs; simpl; lia)).
  rewrite gaussian_coordinate_product_weight_append in Hb.
  simpl gaussian_coordinate_product_weight in Hb; nra.
Qed.

Theorem gaussian_last_marginal_polynomial_bound d F C p :
  finite_joint_continuous (S d) F ->
  finite_polynomial_bound (S d) C p F ->
  finite_polynomial_bound d (C*gaussian_coordinate_weight_moment p) p
    (gaussian_last_marginal F).
Proof.
  intros HF Hb; split.
  - pose proof (proj1 Hb); pose proof (gaussian_coordinate_weight_moment_at_least_one p); nra.
  - intros xs Hxs.
    pose proof (gaussian_expectation_majorant_bound (fun t => F (xs++[t]))
      (gaussian_coordinate_weight p) (C*gaussian_coordinate_product_weight p xs)
      (finite_joint_continuous_last_section d F xs HF Hxs)
      (gaussian_coordinate_weight_continuous p)
      (gaussian_last_section_polynomial_bound d F C p xs Hb Hxs)
      (proj1 (gaussian_coordinate_weight_integrable p))) as H.
    change (Rabs (gaussian_expectation (fun t : R => F (xs++[t]))) <=
      C * gaussian_expectation (gaussian_coordinate_weight p) *
      gaussian_coordinate_product_weight p xs).
    replace (C * gaussian_expectation (gaussian_coordinate_weight p) *
      gaussian_coordinate_product_weight p xs) with
      (C * gaussian_coordinate_product_weight p xs *
       gaussian_expectation (gaussian_coordinate_weight p)) by ring.
    exact H.
Qed.

Theorem gaussian_iterated_polynomial_expectation_bound d F C p :
  gaussian_iterated_integrable d F -> finite_polynomial_bound d C p F ->
  Rabs (gaussian_iterated_expectation d F) <= C*gaussian_coordinate_weight_moment p ^ d.
Proof.
  intros HF [HC Hb].
  destruct (gaussian_coordinate_product_weight_expectation p d) as [HI HE].
  destruct (gaussian_iterated_scale d (gaussian_coordinate_product_weight p) C HI) as [HCI HCE].
  pose proof (gaussian_iterated_majorant_bound d F
    (fun xs => C*gaussian_coordinate_product_weight p xs) HF HCI Hb) as H.
  rewrite HCE, HE in H; exact H.
Qed.

Theorem gaussian_last_marginal_continuous d F C p :
  finite_joint_continuous (S d) F ->
  finite_polynomial_bound (S d) C p F ->
  finite_joint_continuous d (gaussian_last_marginal F).
Proof.
  exact (Gaussian.Law.LibraryBridge.gaussian_last_marginal_continuous_gauss d F C p).
Qed.

Theorem gaussian_iterated_polynomial_integrable d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F.
Proof.
  exact (Gaussian.Law.LibraryBridge.gaussian_iterated_polynomial_integrable_gauss d F C p).
Qed.

Theorem gaussian_iterated_polynomial_absolutely_integrable d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_absolutely_integrable d F.
Proof.
  intros HF Hb; unfold gaussian_iterated_absolutely_integrable.
  apply (gaussian_iterated_polynomial_integrable d (fun xs => Rabs (F xs)) C p).
  - exact (finite_joint_continuous_abs d F HF).
  - exact (finite_polynomial_bound_abs d C p F Hb).
Qed.

Theorem gaussian_iterated_polynomial_admissible d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F /\
  gaussian_iterated_absolutely_integrable d F /\
  gaussian_iterated_has_expectation d F (gaussian_iterated_expectation d F) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (F xs))
    (gaussian_iterated_expectation d (fun xs => Rabs (F xs))) /\
  Rabs (gaussian_iterated_expectation d F) <= C*gaussian_coordinate_weight_moment p ^ d.
Proof.
  intros HF Hb.
  pose proof (gaussian_iterated_polynomial_integrable d F C p HF Hb) as HI.
  pose proof (gaussian_iterated_polynomial_absolutely_integrable d F C p HF Hb) as HA.
  split; [exact HI|]; split; [exact HA|]; split.
  - apply gaussian_iterated_has_expectation_correct; exact HI.
  - split.
    + apply gaussian_iterated_has_expectation_correct; exact HA.
    + exact (gaussian_iterated_polynomial_expectation_bound d F C p HI Hb).
Qed.
