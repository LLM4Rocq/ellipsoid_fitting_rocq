(* The actual isotropic PSD sphere width has normalized limit 1/2. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidFitting Require Import GoeDefinitions GoePairs
  PaperMainGaussianFeatureCoordinates PaperMainGaussianPsdWidth.
Open Scope R_scope.

Lemma paper_main_symmetric_dimension_real n :
  INR (paper_main_symmetric_dimension n) = INR (S n) * (INR (S n)+1)/2.
Proof.
pose proof (goe_pairs_length_twice n) as H.
rewrite <- goe_vector_dimension in H.
apply (f_equal INR) in H.
rewrite !mult_INR in H.
change (2*INR (paper_main_symmetric_dimension n) = INR (S n)*INR (S (S n))) in H.
rewrite (S_INR (S n)) in H; lra.
Qed.

Theorem paper_main_gaussian_psd_width_error n :
  Rabs (paper_main_gaussian_psd_width n - INR (S n)/2) <= 1.
Proof.
pose proof (paper_main_gaussian_psd_width_bounds n) as [Hlo Hhi].
rewrite paper_main_symmetric_dimension_real in Hlo.
rewrite paper_main_symmetric_dimension_real in Hhi.
pose proof (paper_main_gaussian_psd_width_nonnegative n) as Hnon.
set (d := INR (S n)) in *.
assert (Hd : 1 <= d) by (unfold d; rewrite S_INR; pose proof (pos_INR n); lra).
assert (HR : 0 <= d*(d+1)/2/2) by nra.
pose proof (pow2_sqrt _ HR) as Hsqhi.
pose proof (sqrt_pos (d*(d+1)/2/2)) as Hphi.
assert (Hup : paper_main_gaussian_psd_width n - d/2 <= 1) by nra.
assert (Hlow : d/2-1 <= paper_main_gaussian_psd_width n).
{ destruct (Rle_dec d 2) as [Hsmall|Hsmall]; [lra|].
  assert (HRlo : 0 <= d*(d+1)/2/2-1) by nra.
  pose proof (pow2_sqrt _ HRlo).
  pose proof (sqrt_pos (d*(d+1)/2/2-1)); nra. }
apply Rabs_le; lra.
Qed.

Theorem paper_main_gaussian_psd_width_normalized_error n :
  Rabs (paper_main_gaussian_psd_width n / INR (S n) - 1/2) <= /INR (S n).
Proof.
assert (Hd : 0 < INR (S n)) by (apply lt_0_INR; lia).
replace (paper_main_gaussian_psd_width n/INR (S n)-1/2) with
  ((paper_main_gaussian_psd_width n-INR (S n)/2) * /INR (S n)) by (field; lra).
rewrite Rabs_mult (Rabs_pos_eq (/INR (S n)) ltac:(left; apply Rinv_0_lt_compat; exact Hd)).
pose proof (Rmult_le_compat_r (/INR (S n)) _ _
  ltac:(left; apply Rinv_0_lt_compat; exact Hd) (paper_main_gaussian_psd_width_error n)).
lra.
Qed.

Theorem paper_main_gaussian_psd_width_limit :
  Un_cv (fun n => paper_main_gaussian_psd_width n/INR (S n)) (1/2).
Proof.
intros eps Heps.
destruct (INR_unbounded (/eps)) as [K HK].
exists K; intros n Hn.
assert (Hd : 0 < INR (S n)) by (apply lt_0_INR; lia).
assert (Hlarge : /eps < INR (S n)).
{ pose proof (le_INR K (S n) ltac:(lia)); lra. }
assert (Hrate : /INR (S n) < eps).
{ apply (Rmult_lt_reg_r (INR (S n))); [exact Hd|].
  replace (/INR (S n)*INR (S n)) with 1 by (field; lra).
  pose proof (Rmult_lt_compat_l eps _ _ Heps Hlarge) as H.
  rewrite (Rinv_r eps ltac:(lra)) in H; nra. }
unfold R_dist.
pose proof (paper_main_gaussian_psd_width_normalized_error n); lra.
Qed.
