(* Exponential covariance estimate for bounded C2 Gaussian tests.
   The gradient-square bound is uniform and its coefficient is independent
   of dimension. Integrating the MGF differential inequality remains a
   separate step. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianProductDefinitions GaussianCoordinateSteinDomains
  GaussianCovarianceSums PaperMainGaussianBlockTestCalculus
  PaperMainGaussianSmoothCovariance PaperMainGaussianSmoothExponential
  PaperMainGaussianSmoothProduct.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gaussian_sum_cross_bound d (u v : nat -> R) L :
  finite_sum (fun i => u i ^ 2) (List.seq 0 d) <= L ^ 2 ->
  finite_sum (fun i => v i ^ 2) (List.seq 0 d) <= L ^ 2 ->
  finite_sum (fun i => u i * v i) (List.seq 0 d) <= L ^ 2.
Proof.
intros Hu Hv.
assert (H : finite_sum (fun i => 2 * (u i * v i)) (List.seq 0 d) <=
  finite_sum (fun i => u i ^ 2 + v i ^ 2) (List.seq 0 d)).
{ apply finite_sum_le; intros i Hi.
  pose proof (Rle_0_sqr (u i - v i)); unfold Rsqr in *; nra. }
rewrite finite_sum_scale finite_sum_plus in H; lra.
Qed.

Lemma paper_main_gaussian_exp_mixed_hessian d t f Df D2f zs :
  finite_sum (fun a =>
    paper_main_gaussian_product_second d f (paper_main_gaussian_exp_test t f)
      Df (paper_main_gaussian_exp_first t f Df)
      D2f (paper_main_gaussian_exp_second t f Df D2f) a (Nat.add d a) zs +
    paper_main_gaussian_product_second d f (paper_main_gaussian_exp_test t f)
      Df (paper_main_gaussian_exp_first t f Df)
      D2f (paper_main_gaussian_exp_second t f Df D2f) (Nat.add d a) a zs)
    (List.seq 0 d) =
  2 * t * paper_main_gaussian_exp_test t f (List.skipn d zs) *
    finite_sum (fun a => Df a (List.firstn d zs) * Df a (List.skipn d zs)) (List.seq 0 d).
Proof.
rewrite <- finite_sum_scale.
apply finite_sum_ext; intros a Ha; apply in_seq_lt in Ha.
unfold paper_main_gaussian_product_second.
assert (Ea : Nat.ltb a d = true) by (apply Nat.ltb_lt; exact Ha).
assert (Eb : Nat.ltb (Nat.add d a) d = false) by (apply Nat.ltb_ge; lia).
rewrite Ea Eb.
replace (Nat.sub (Nat.add d a) d) with a by lia.
unfold paper_main_gaussian_exp_first; ring.
Qed.

Theorem paper_main_gaussian_exponential_covariance d t f Df D2f M L :
  0 <= t ->
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  gaussian_iterated_expectation d (fun xs => f xs * exp (t * f xs)) -
    gaussian_iterated_expectation d f *
      gaussian_iterated_expectation d (fun xs => exp (t * f xs)) <=
  t * L ^ 2 * gaussian_iterated_expectation d (fun xs => exp (t * f xs)).
Proof.
intros Ht Hsmooth Hgrad.
pose proof (paper_main_gaussian_exp_smooth d t f Df D2f M Ht Hsmooth) as HE.
pose proof (paper_main_gaussian_product_smooth d f (paper_main_gaussian_exp_test t f)
  Df (paper_main_gaussian_exp_first t f Df) D2f (paper_main_gaussian_exp_second t f Df D2f)
  M (paper_main_gaussian_exp_constant t M) Hsmooth HE) as HP.
apply (paper_main_gaussian_weighted_covariance_bound d f (paper_main_gaussian_exp_test t f)
  (paper_main_gaussian_product_first d f (paper_main_gaussian_exp_test t f) Df (paper_main_gaussian_exp_first t f Df))
  (paper_main_gaussian_product_second d f (paper_main_gaussian_exp_test t f) Df
    (paper_main_gaussian_exp_first t f Df) D2f (paper_main_gaussian_exp_second t f Df D2f))
  (M * paper_main_gaussian_exp_constant t M) 0
  (paper_main_gaussian_exp_first t f Df) (paper_main_gaussian_exp_second t f Df D2f)
  (paper_main_gaussian_exp_constant t M) 0 (t * L ^ 2) HP HE).
- destruct Hsmooth as [Hc HD HDc HD2 HD2c Hb HDb HD2b].
  exact (proj1 (gaussian_coordinate_polynomial_domain d f M 0 Hc Hb)).
- intros zs Hzs; rewrite paper_main_gaussian_exp_mixed_hessian.
  destruct (paper_main_gaussian_block_lengths d zs Hzs) as [Hl Hr].
  pose proof (paper_main_gaussian_sum_cross_bound d
    (fun a => Df a (List.firstn d zs)) (fun a => Df a (List.skipn d zs))
    L (Hgrad _ Hl) (Hgrad _ Hr)) as Hcross.
  assert (Hfac : 0 <= 2 * t * paper_main_gaussian_exp_test t f (List.skipn d zs)).
  { unfold paper_main_gaussian_exp_test; pose proof (exp_pos (t * f (List.skipn d zs))); nra. }
  pose proof (Rmult_le_compat_l _ _ _ Hfac Hcross) as HB.
  nra.
Qed.
