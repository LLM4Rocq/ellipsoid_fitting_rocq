(* Sharp variance and mean control for the Euclidean Gaussian norm, used
   in the escape side of Gaussian comparison. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCovarianceSums
  MaximumRadiusComparison PaperMainGordonLipschitz PaperMainGaussianNorm
  PaperMainGaussianLipschitzVariance.
Open Scope R_scope.

Theorem paper_main_gaussian_norm_lipschitz d xs ys :
  List.length xs = d -> List.length ys = d ->
  Rabs (paper_main_gaussian_norm xs - paper_main_gaussian_norm ys) <=
    1 * paper_main_gordon_distance d xs ys.
Proof.
intros Hxs Hys.
set (a := paper_main_gaussian_norm xs).
set (b := paper_main_gaussian_norm ys).
set (c := paper_main_gordon_distance d xs ys).
set (p := finite_sum (fun i => List.nth i xs 0 * List.nth i ys 0) (List.seq 0 d)).
pose proof (paper_main_gaussian_norm_nonnegative xs) as Ha.
pose proof (paper_main_gaussian_norm_nonnegative ys) as Hb.
pose proof (paper_main_gordon_distance_nonnegative d xs ys) as Hc.
pose proof (paper_main_gaussian_norm_squared xs) as Ha2.
pose proof (paper_main_gaussian_norm_squared ys) as Hb2.
pose proof (paper_main_gordon_distance_squared d xs ys) as Hc2.
pose proof (paper_main_gordon_sum_cauchy (fun i => List.nth i xs 0)
  (fun i => List.nth i ys 0) (List.seq 0 d)) as HP.
rewrite (paper_main_gaussian_squares_coordinates d xs Hxs)
  (paper_main_gaussian_squares_coordinates d ys Hys) in HP.
assert (HE : finite_sum (fun i => (List.nth i xs 0 - List.nth i ys 0)^2) (List.seq 0 d) =
  gaussian_sum_squares xs + gaussian_sum_squares ys - 2 * p).
{ transitivity (finite_sum (fun i => (List.nth i xs 0)^2 + (List.nth i ys 0)^2 -
    2*(List.nth i xs 0 * List.nth i ys 0)) (List.seq 0 d)).
  - apply finite_sum_ext; intros i _; ring.
  - rewrite finite_sum_minus finite_sum_plus finite_sum_scale.
    rewrite (paper_main_gaussian_squares_coordinates d xs Hxs)
      (paper_main_gaussian_squares_coordinates d ys Hys); reflexivity. }
fold a in Ha; fold a in Ha2.
fold b in Hb; fold b in Hb2.
fold c in Hc; fold c in Hc2; fold p in HP.
assert (Hab : 0 <= a*b) by nra.
assert (Hab2 : (a*b)^2 = a^2*b^2) by ring.
assert (Hpb : p <= a*b) by nra.
pose proof (Rabs_pos (a-b)) as Habs.
pose proof (Rsqr_abs (a-b)) as Habs2; unfold Rsqr in Habs2.
change (Rabs (a-b) <= 1*c); nra.
Qed.

Theorem paper_main_gaussian_norm_second_moment d :
  gaussian_iterated_expectation d
    (fun xs => paper_main_gaussian_norm xs * paper_main_gaussian_norm xs) = INR d.
Proof.
rewrite <- (gaussian_sum_squares_expectation d).
apply gaussian_iterated_expectation_ext; intros xs _.
replace (paper_main_gaussian_norm xs * paper_main_gaussian_norm xs)
  with (paper_main_gaussian_norm xs ^ 2) by ring.
exact (paper_main_gaussian_norm_squared xs).
Qed.

Theorem paper_main_gaussian_norm_variance d :
  paper_main_gaussian_variance d paper_main_gaussian_norm <= 1.
Proof.
replace 1 with (1^2) by ring.
apply (paper_main_gaussian_lipschitz_variance d paper_main_gaussian_norm 1 Rle_0_1).
exact (paper_main_gaussian_norm_lipschitz d).
Qed.

Theorem paper_main_gaussian_norm_mean_squared d :
  INR d - 1 <= (gaussian_iterated_expectation d paper_main_gaussian_norm)^2.
Proof.
pose proof (paper_main_gaussian_variance_identity d paper_main_gaussian_norm 1
  Rle_0_1 (paper_main_gaussian_norm_lipschitz d)) as H.
rewrite paper_main_gaussian_norm_second_moment in H.
pose proof (paper_main_gaussian_norm_variance d); lra.
Qed.

Theorem paper_main_gaussian_norm_mean_lower d :
  sqrt (INR d - 1) <= gaussian_iterated_expectation d paper_main_gaussian_norm.
Proof.
pose proof (proj1 (paper_main_gaussian_norm_expectation d)) as Hm.
destruct d as [|d].
- replace (INR 0 - 1) with (-1) by (simpl; lra).
  rewrite sqrt_neg_0; lra.
- assert (Hd : 0 <= INR (S d) - 1).
  { rewrite S_INR; pose proof (pos_INR d); lra. }
  pose proof (pow2_sqrt (INR (S d) - 1) Hd).
  pose proof (sqrt_pos (INR (S d) - 1)).
  pose proof (paper_main_gaussian_norm_mean_squared (S d)); nra.
Qed.
