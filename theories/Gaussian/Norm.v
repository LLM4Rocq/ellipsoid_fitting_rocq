(* Gaussian Euclidean norm bounds for the finite expected Gordon margin. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Gaussian.CoordinatePolynomialDomain
  Gaussian.CovarianceDefinitions Analysis.FiniteSumAlgebra Radius.Regularity
  Radius.ExpectedMaximum Gordon.Continuity Gordon.ProcessCovariance
  Gordon.Lipschitz.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_norm (xs : list R) := sqrt (gaussian_sum_squares xs).

Lemma paper_main_gaussian_squares_coordinates d xs :
  List.length xs = d ->
  finite_sum (fun i => (List.nth i xs 0)^2) (List.seq 0 d) = gaussian_sum_squares xs.
Proof.
revert d; induction xs as [|x xs IH]; intros d HL; simpl in HL; subst d.
- reflexivity.
- cbn [List.seq finite_sum List.nth gaussian_sum_squares].
  rewrite finite_sum_seq_shift.
  cbn [Nat.add List.nth].
  rewrite (IH (List.length xs) eq_refl); ring.
Qed.

Lemma paper_main_gaussian_norm_nonnegative xs : 0 <= paper_main_gaussian_norm xs.
Proof.
unfold paper_main_gaussian_norm; apply sqrt_pos.
Qed.

Lemma paper_main_gaussian_norm_squared xs :
  (paper_main_gaussian_norm xs)^2 = gaussian_sum_squares xs.
Proof.
unfold paper_main_gaussian_norm; apply pow2_sqrt, maximum_radius_squares_nonnegative.
Qed.

Lemma paper_main_gaussian_norm_continuous d :
  finite_joint_continuous d paper_main_gaussian_norm.
Proof.
unfold paper_main_gaussian_norm.
apply paper_main_gordon_joint_comp.
- apply maximum_radius_squares_continuous.
- intros xs Hxs; apply Analysis.CalculusBridge.continuous_Rsqrt, maximum_radius_squares_nonnegative.
Qed.

Lemma paper_main_gaussian_norm_polynomial d :
  finite_polynomial_bound d (1 + INR d) 2 paper_main_gaussian_norm.
Proof.
split; [pose proof (pos_INR d); lra|].
intros xs Hxs.
rewrite Rabs_pos_eq by apply paper_main_gaussian_norm_nonnegative.
pose proof (paper_main_gaussian_norm_nonnegative xs) as HN.
pose proof (paper_main_gaussian_norm_squared xs) as HS.
pose proof (maximum_radius_squares_polynomial xs) as HB.
pose proof (gaussian_coordinate_product_weight_at_least_one 2 xs) as HW.
rewrite Hxs in HB.
assert (HT : paper_main_gaussian_norm xs <= 1 + gaussian_sum_squares xs) by nra.
nra.
Qed.

Theorem paper_main_gaussian_norm_domain d :
  gaussian_covariance_domain d paper_main_gaussian_norm.
Proof.
apply (gaussian_coordinate_polynomial_domain d paper_main_gaussian_norm (1 + INR d) 2).
- apply paper_main_gaussian_norm_continuous.
- apply paper_main_gaussian_norm_polynomial.
Qed.

Lemma paper_main_gaussian_norm_tangent xs a :
  2 * a * paper_main_gaussian_norm xs <= gaussian_sum_squares xs + a^2.
Proof.
pose proof (paper_main_gaussian_norm_squared xs) as HE.
pose proof (pow2_ge_0 (paper_main_gaussian_norm xs - a)); nra.
Qed.

Theorem paper_main_gaussian_norm_expectation d :
  0 <= gaussian_iterated_expectation d paper_main_gaussian_norm <= sqrt (INR d).
Proof.
pose proof (proj1 (paper_main_gaussian_norm_domain d)) as HN.
split.
- apply gaussian_iterated_nonnegative; [exact HN|].
  intros xs Hxs; apply paper_main_gaussian_norm_nonnegative.
- destruct d as [|d].
  + change (sqrt 0 <= sqrt 0); lra.
  + set (a := sqrt (INR (S d))).
    assert (Ha : 0 < a) by (unfold a; apply sqrt_lt_R0; apply lt_0_INR; lia).
    assert (Ha2 : a^2 = INR (S d)) by (unfold a; apply pow2_sqrt, pos_INR).
    destruct (gaussian_iterated_scale (S d) paper_main_gaussian_norm (2*a) HN)
      as [HL HLE].
    destruct (gaussian_iterated_constant (S d) (a^2)) as [HC HCE].
    destruct (gaussian_iterated_add (S d) gaussian_sum_squares (fun _ => a^2)
      (maximum_radius_squares_integrable (S d)) HC) as [HR HRE].
    pose proof (gaussian_iterated_monotone (S d)
      (fun xs => 2*a*paper_main_gaussian_norm xs)
      (fun xs => gaussian_sum_squares xs + a^2) HL HR
      ltac:(intros xs Hxs; apply paper_main_gaussian_norm_tangent)) as HM.
    rewrite HLE, HRE, HCE, gaussian_sum_squares_expectation in HM.
    fold a; nra.
Qed.

Lemma paper_main_gaussian_unit_dot_bound d u xs :
  List.length xs = d -> paper_main_gordon_dot d u u = 1 ->
  Rabs (paper_main_gordon_dot d u (fun i => List.nth i xs 0)) <= paper_main_gaussian_norm xs.
Proof.
intros Hxs Hu.
pose proof (paper_main_gordon_sum_cauchy u (fun i => List.nth i xs 0) (List.seq 0 d)) as HC.
assert (HE : finite_sum (fun i => (u i)^2) (List.seq 0 d) = paper_main_gordon_dot d u u).
{ unfold paper_main_gordon_dot; apply finite_sum_ext; intros; ring. }
rewrite HE, Hu, (paper_main_gaussian_squares_coordinates d xs Hxs), Rmult_1_l in HC.
fold (paper_main_gordon_dot d u (fun i => List.nth i xs 0)) in HC.
pose proof (paper_main_gaussian_norm_squared xs) as HN.
pose proof (paper_main_gaussian_norm_nonnegative xs) as HNP.
pose proof (Rsqr_abs (paper_main_gordon_dot d u (fun i => List.nth i xs 0))) as HA.
pose proof (Rabs_pos (paper_main_gordon_dot d u (fun i => List.nth i xs 0))) as HAP.
unfold Rsqr in HA; nra.
Qed.
