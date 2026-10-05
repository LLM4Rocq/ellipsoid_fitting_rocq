(* Concrete approximants of a Euclidean-Lipschitz test F on lists of
   length d: clip F at the level n+1, then smooth it with the Gaussian
   width 1/(n+1). For every d (including d = 0) and every L >= 0
   (including L = 0): F is integrable by its linear growth; the
   approximants converge to F pointwise; they have an integrable envelope
   independent of n; and their iterated Gaussian means converge to the
   mean of F, with the explicit rate 1/(n+1). The smooth-test and
   gradient properties of the approximants are conditional on the
   one-dimensional interface of PaperMainGaussianLipschitzSmoothDerivativeLift. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateSteinDomains GaussianCoordinateWeights
  GaussianCoordinatePolynomialContinuity GaussianExpectationContinuity
  GaussianCovarianceSums PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainGordonLipschitz PaperMainGaussianNorm
  PaperMainGaussianLipschitzClip PaperMainGaussianLipschitzSmooth
  PaperMainGaussianLipschitzSmoothDerivative
  PaperMainGaussianLipschitzSmoothDerivativeLift.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_level (n : nat) : R := INR (S n).

Definition paper_main_gaussian_width (n : nat) : R := / INR (S n).

Definition paper_main_gaussian_approximant d (F : list R -> R) (n : nat)
    (xs : list R) : R :=
  paper_main_gaussian_smoothing d (paper_main_gaussian_width n)
    (paper_main_gaussian_clipped (paper_main_gaussian_level n) F) xs.

Definition paper_main_gaussian_zero_list d : list R :=
  map (fun _ => 0) (List.seq 0 d).

Lemma paper_main_gaussian_level_pos n : 0 < paper_main_gaussian_level n.
Proof. unfold paper_main_gaussian_level; apply lt_0_INR; lia. Qed.

Lemma paper_main_gaussian_width_pos n : 0 < paper_main_gaussian_width n.
Proof.
unfold paper_main_gaussian_width; apply Rinv_0_lt_compat.
exact (paper_main_gaussian_level_pos n).
Qed.

Lemma paper_main_gaussian_width_le_one n : paper_main_gaussian_width n <= 1.
Proof.
unfold paper_main_gaussian_width; rewrite <- Rinv_1.
apply Rinv_le_contravar; [lra|].
rewrite S_INR; pose proof (pos_INR n); lra.
Qed.

Lemma paper_main_gaussian_width_level n :
  paper_main_gaussian_width n = / paper_main_gaussian_level n.
Proof. reflexivity. Qed.

Lemma paper_main_gaussian_zero_list_length d :
  List.length (paper_main_gaussian_zero_list d) = d.
Proof. unfold paper_main_gaussian_zero_list; apply length_map_seq. Qed.

Lemma paper_main_gaussian_distance_zero d xs :
  List.length xs = d ->
  paper_main_gordon_distance d xs (paper_main_gaussian_zero_list d) =
    paper_main_gaussian_norm xs.
Proof.
intros Hxs; unfold paper_main_gordon_distance, paper_main_gaussian_norm.
f_equal; rewrite <- (paper_main_gaussian_squares_coordinates d xs Hxs).
apply finite_sum_ext; intros k Hk; apply in_seq in Hk.
unfold paper_main_gaussian_zero_list.
rewrite (nth_map_seq (fun _ => 0) d k ltac:(lia)); ring.
Qed.

Lemma paper_main_gaussian_clip_abs_le K z :
  0 <= K -> Rabs (paper_main_gaussian_clip K z) <= Rabs z.
Proof.
intros HK; unfold paper_main_gaussian_clip, Rmax, Rmin.
destruct (Rle_dec K z) as [h1|h1];
  repeat match goal with |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b) end;
  repeat match goal with H : ~ (_ <= _) |- _ => apply Rnot_le_lt in H end;
  unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.

Lemma paper_main_gaussian_clip_minus_abs_le K z :
  0 <= K -> Rabs (paper_main_gaussian_clip K z - z) <= Rabs z.
Proof.
intros HK; unfold paper_main_gaussian_clip, Rmax, Rmin.
destruct (Rle_dec K z) as [h1|h1];
  repeat match goal with |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b) end;
  repeat match goal with H : ~ (_ <= _) |- _ => apply Rnot_le_lt in H end;
  unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.

Lemma paper_main_gaussian_clip_error K z :
  0 < K -> Rabs (paper_main_gaussian_clip K z - z) <= z * z / K.
Proof.
intros HK.
assert (Hq : 0 <= z * z / K).
{ unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; exact HK]. }
destruct (Rle_dec (Rabs z) K) as [Hz|Hz].
- rewrite (paper_main_gaussian_clip_eq K z Hz).
  rewrite Rminus_diag; rewrite Rabs_R0; exact Hq.
- apply Rnot_le_lt in Hz.
  apply Rle_trans with (Rabs z);
    [exact (paper_main_gaussian_clip_minus_abs_le K z (Rlt_le _ _ HK))|].
  apply (Rmult_le_reg_r K _ _ HK).
  replace (z * z / K * K) with (Rabs z * Rabs z)
    by (rewrite <- Rabs_mult; rewrite Rabs_pos_eq; [field; lra|nra]).
  pose proof (Rabs_pos z); nra.
Qed.

Lemma paper_main_gaussian_lipschitz_linear_growth d F L xs :
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  List.length xs = d ->
  Rabs (F xs) <=
    Rabs (F (paper_main_gaussian_zero_list d)) + L * paper_main_gaussian_norm xs.
Proof.
intros HLip Hxs.
pose proof (HLip xs (paper_main_gaussian_zero_list d) Hxs
  (paper_main_gaussian_zero_list_length d)) as H.
rewrite (paper_main_gaussian_distance_zero d xs Hxs) in H.
pose proof (Rabs_triang_inv (F xs) (F (paper_main_gaussian_zero_list d))) as Ht.
lra.
Qed.

Definition paper_main_gaussian_growth_constant d (F : list R -> R) L : R :=
  Rabs (F (paper_main_gaussian_zero_list d)) + L * (1 + INR d).

Lemma paper_main_gaussian_growth_constant_nonnegative d F L :
  0 <= L -> 0 <= paper_main_gaussian_growth_constant d F L.
Proof.
intros HL; unfold paper_main_gaussian_growth_constant.
apply Rplus_le_le_0_compat; [apply Rabs_pos|].
apply Rmult_le_pos; [exact HL|pose proof (pos_INR d); lra].
Qed.

Theorem paper_main_gaussian_lipschitz_polynomial_bound d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  finite_polynomial_bound d (paper_main_gaussian_growth_constant d F L) 2 F.
Proof.
intros HL HLip; split; [exact (paper_main_gaussian_growth_constant_nonnegative d F L HL)|].
intros xs Hxs.
pose proof (paper_main_gaussian_lipschitz_linear_growth d F L xs HLip Hxs) as Hg.
destruct (paper_main_gaussian_norm_polynomial d) as [_ Hn].
pose proof (Hn xs Hxs) as Hnb.
pose proof (gaussian_coordinate_product_weight_at_least_one 2 xs) as Hw.
pose proof (paper_main_gaussian_norm_nonnegative xs) as Hn0.
rewrite (Rabs_pos_eq _ Hn0) in Hnb.
pose proof (Rabs_pos (F (paper_main_gaussian_zero_list d))) as HF0.
pose proof (pos_INR d) as Hd.
unfold paper_main_gaussian_growth_constant; nra.
Qed.

Theorem paper_main_gaussian_lipschitz_domain d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_integrable d F /\ gaussian_iterated_absolutely_integrable d F.
Proof.
intros HL HLip.
destruct (gaussian_coordinate_polynomial_domain d F _ 2
  (paper_main_gaussian_lipschitz_continuous d F L HL HLip)
  (paper_main_gaussian_lipschitz_polynomial_bound d F L HL HLip)) as [HI [HA _]].
split; [exact HI|exact HA].
Qed.

(* Properties of one approximant. *)

Lemma paper_main_gaussian_level_clipped_bound d F n :
  forall xs, List.length xs = d ->
    Rabs (paper_main_gaussian_clipped (paper_main_gaussian_level n) F xs) <=
      paper_main_gaussian_level n.
Proof.
intros xs _; apply paper_main_gaussian_clipped_abs_bound.
exact (Rlt_le _ _ (paper_main_gaussian_level_pos n)).
Qed.

Theorem paper_main_gaussian_approximant_bound d F L n xs :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  Rabs (paper_main_gaussian_approximant d F n xs) <= paper_main_gaussian_level n.
Proof.
intros HL HLip; unfold paper_main_gaussian_approximant.
exact (paper_main_gaussian_smoothing_bound d (paper_main_gaussian_level n) L
  (paper_main_gaussian_width n) _ xs (Rlt_le _ _ (paper_main_gaussian_level_pos n)) HL
  (paper_main_gaussian_level_clipped_bound d F n)
  (paper_main_gaussian_clipped_lipschitz d (paper_main_gaussian_level n) F L HLip)).
Qed.

Theorem paper_main_gaussian_approximant_lipschitz d F L n :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (paper_main_gaussian_approximant d F n xs -
          paper_main_gaussian_approximant d F n ys) <=
      L * paper_main_gordon_distance d xs ys.
Proof.
intros HL HLip; unfold paper_main_gaussian_approximant.
exact (paper_main_gaussian_smoothing_lipschitz d (paper_main_gaussian_level n) L
  (paper_main_gaussian_width n) _ (Rlt_le _ _ (paper_main_gaussian_level_pos n)) HL
  (paper_main_gaussian_level_clipped_bound d F n)
  (paper_main_gaussian_clipped_lipschitz d (paper_main_gaussian_level n) F L HLip)).
Qed.

Theorem paper_main_gaussian_approximant_continuous d F L n :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  finite_joint_continuous d (paper_main_gaussian_approximant d F n).
Proof.
intros HL HLip.
exact (paper_main_gaussian_lipschitz_continuous d _ L HL
  (paper_main_gaussian_approximant_lipschitz d F L n HL HLip)).
Qed.

Theorem paper_main_gaussian_approximant_domain d F L n :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_integrable d (paper_main_gaussian_approximant d F n) /\
  gaussian_iterated_absolutely_integrable d (paper_main_gaussian_approximant d F n).
Proof.
intros HL HLip.
assert (HB : finite_polynomial_bound d (paper_main_gaussian_level n) 0
  (paper_main_gaussian_approximant d F n)).
{ apply (proj2 (paper_main_polynomial_zero_bound d _ _)); split;
    [exact (Rlt_le _ _ (paper_main_gaussian_level_pos n))|].
  intros xs _; exact (paper_main_gaussian_approximant_bound d F L n xs HL HLip). }
destruct (gaussian_coordinate_polynomial_domain d _ _ 0
  (paper_main_gaussian_approximant_continuous d F L n HL HLip) HB) as [HI [HA _]].
split; [exact HI|exact HA].
Qed.

(* Pointwise convergence. *)

Theorem paper_main_gaussian_approximant_pointwise_error d F L n xs :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  List.length xs = d -> Rabs (F xs) <= paper_main_gaussian_level n ->
  Rabs (paper_main_gaussian_approximant d F n xs - F xs) <=
    L * sqrt (INR d) / paper_main_gaussian_level n.
Proof.
intros HL HLip Hxs HF.
rewrite <- (paper_main_gaussian_clipped_eq (paper_main_gaussian_level n) F xs HF).
unfold paper_main_gaussian_approximant.
eapply Rle_trans.
- exact (paper_main_gaussian_smoothing_error d (paper_main_gaussian_level n) L
    (paper_main_gaussian_width n) _ xs (Rlt_le _ _ (paper_main_gaussian_level_pos n)) HL
    (Rlt_le _ _ (paper_main_gaussian_width_pos n))
    (paper_main_gaussian_level_clipped_bound d F n)
    (paper_main_gaussian_clipped_lipschitz d (paper_main_gaussian_level n) F L HLip) Hxs).
- rewrite paper_main_gaussian_width_level; right; unfold Rdiv; ring.
Qed.

Theorem paper_main_gaussian_approximant_pointwise d F L xs :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  List.length xs = d ->
  Un_cv (fun n => paper_main_gaussian_approximant d F n xs) (F xs).
Proof.
intros HL HLip Hxs eps Heps.
set (c := L * sqrt (INR d)).
assert (Hc0 : 0 <= c) by (unfold c; apply Rmult_le_pos; [exact HL|apply sqrt_pos]).
destruct (INR_unbounded (Rmax (Rabs (F xs)) (c / eps))) as [N HN].
exists N; intros n Hn; unfold R_dist.
assert (HnN : INR N <= INR n) by (apply le_INR; lia).
assert (Hlev : INR n < paper_main_gaussian_level n)
  by (unfold paper_main_gaussian_level; rewrite S_INR; lra).
pose proof (Rmax_l (Rabs (F xs)) (c / eps)) as Hm1.
pose proof (Rmax_r (Rabs (F xs)) (c / eps)) as Hm2.
assert (HF : Rabs (F xs) <= paper_main_gaussian_level n) by lra.
pose proof (paper_main_gaussian_level_pos n) as Hpos.
eapply Rle_lt_trans;
  [exact (paper_main_gaussian_approximant_pointwise_error d F L n xs HL HLip Hxs HF)|].
fold c.
assert (Hcl : c / eps < paper_main_gaussian_level n) by lra.
apply (Rmult_lt_reg_r (paper_main_gaussian_level n) _ _ Hpos).
replace (c / paper_main_gaussian_level n * paper_main_gaussian_level n) with c
  by (field; lra).
apply (Rmult_lt_reg_r (/ eps)); [apply Rinv_0_lt_compat; exact Heps|].
replace (eps * paper_main_gaussian_level n * / eps) with (paper_main_gaussian_level n)
  by (field; lra).
exact Hcl.
Qed.

(* An integrable envelope independent of n. *)

Theorem paper_main_gaussian_approximant_envelope d F L n xs :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  List.length xs = d ->
  Rabs (paper_main_gaussian_approximant d F n xs) <=
    Rabs (F (paper_main_gaussian_zero_list d)) + L * paper_main_gaussian_norm xs +
    L * sqrt (INR d).
Proof.
intros HL HLip Hxs; unfold paper_main_gaussian_approximant, paper_main_gaussian_smoothing.
set (w := paper_main_gaussian_width n).
set (K := paper_main_gaussian_level n).
set (c := Rabs (F (paper_main_gaussian_zero_list d)) + L * paper_main_gaussian_norm xs).
assert (Hw0 : 0 <= w) by exact (Rlt_le _ _ (paper_main_gaussian_width_pos n)).
assert (Hw1 : w <= 1) by exact (paper_main_gaussian_width_le_one n).
assert (HK0 : 0 <= K) by exact (Rlt_le _ _ (paper_main_gaussian_level_pos n)).
destruct (paper_main_gaussian_smoothing_domain d K L w
  (paper_main_gaussian_clipped K F) xs HK0 HL
  (paper_main_gaussian_level_clipped_bound d F n)
  (paper_main_gaussian_clipped_lipschitz d K F L HLip)) as [HI _].
destruct (gaussian_coordinate_polynomial_domain d paper_main_gaussian_norm
  (1 + INR d) 2 (paper_main_gaussian_norm_continuous d)
  (paper_main_gaussian_norm_polynomial d)) as [HIn _].
destruct (gaussian_iterated_scale d paper_main_gaussian_norm (L * w) HIn) as [HIs HEs].
destruct (gaussian_iterated_constant d c) as [HIc HEc].
destruct (gaussian_iterated_add d (fun _ => c)
  (fun zs => L * w * paper_main_gaussian_norm zs) HIc HIs) as [HIh HEh].
rewrite HEc in HEh; rewrite HEs in HEh.
destruct (paper_main_gaussian_norm_expectation d) as [HE0 HEd].
assert (Hpt : forall zs, List.length zs = d ->
  Rabs (paper_main_gaussian_clipped K F (paper_main_gaussian_shift d xs w zs)) <=
    c + L * w * paper_main_gaussian_norm zs).
{ intros zs Hzs.
  eapply Rle_trans; [apply paper_main_gaussian_clip_abs_le; exact HK0|].
  pose proof (HLip (paper_main_gaussian_shift d xs w zs) xs
    (paper_main_gaussian_shift_length d xs w zs) Hxs) as H1.
  rewrite (paper_main_gaussian_shift_center_distance d xs w zs Hw0 Hzs) in H1.
  pose proof (paper_main_gaussian_lipschitz_linear_growth d F L xs HLip Hxs) as H2.
  pose proof (Rabs_triang_inv (F (paper_main_gaussian_shift d xs w zs)) (F xs)) as H3.
  unfold c; lra. }
assert (Hup : gaussian_iterated_expectation d
    (fun zs => paper_main_gaussian_clipped K F (paper_main_gaussian_shift d xs w zs)) <=
  c + L * w * gaussian_iterated_expectation d paper_main_gaussian_norm).
{ rewrite <- HEh; apply gaussian_iterated_monotone; [exact HI|exact HIh|].
  intros zs Hzs; pose proof (Hpt zs Hzs).
  pose proof (Rle_abs (paper_main_gaussian_clipped K F (paper_main_gaussian_shift d xs w zs))).
  lra. }
destruct (gaussian_iterated_scale d (fun zs => c + L * w * paper_main_gaussian_norm zs)
  (-1) HIh) as [HIm HEm].
rewrite HEh in HEm.
assert (Hlo : - (c + L * w * gaussian_iterated_expectation d paper_main_gaussian_norm) <=
  gaussian_iterated_expectation d
    (fun zs => paper_main_gaussian_clipped K F (paper_main_gaussian_shift d xs w zs))).
{ replace (- (c + L * w * gaussian_iterated_expectation d paper_main_gaussian_norm)) with
    (-1 * (c + L * w * gaussian_iterated_expectation d paper_main_gaussian_norm)) by ring.
  rewrite <- HEm; apply gaussian_iterated_monotone; [exact HIm|exact HI|].
  intros zs Hzs; pose proof (Hpt zs Hzs).
  pose proof (Rle_abs (- paper_main_gaussian_clipped K F
    (paper_main_gaussian_shift d xs w zs))) as H0.
  rewrite Rabs_Ropp in H0; lra. }
assert (Hbound : L * w * gaussian_iterated_expectation d paper_main_gaussian_norm <=
  L * sqrt (INR d)).
{ assert (HLw : L * w <= L) by nra.
  pose proof (Rmult_le_compat (L * w) L
    (gaussian_iterated_expectation d paper_main_gaussian_norm) (sqrt (INR d))
    ltac:(nra) HE0 HLw HEd); lra. }
apply Rabs_le; split; lra.
Qed.

(* Explicit convergence of the iterated Gaussian means. *)

Theorem paper_main_gaussian_approximant_mean_error d F L n :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  Rabs (gaussian_iterated_expectation d (paper_main_gaussian_approximant d F n) -
        gaussian_iterated_expectation d F) <=
    (L * sqrt (INR d) +
     (paper_main_gaussian_growth_constant d F L * paper_main_gaussian_growth_constant d F L) *
       gaussian_coordinate_weight_moment 4 ^ d) / paper_main_gaussian_level n.
Proof.
intros HL HLip.
set (K := paper_main_gaussian_level n).
set (C := paper_main_gaussian_growth_constant d F L).
assert (HKp : 0 < K) by exact (paper_main_gaussian_level_pos n).
assert (HC0 : 0 <= C) by exact (paper_main_gaussian_growth_constant_nonnegative d F L HL).
destruct (paper_main_gaussian_approximant_domain d F L n HL HLip) as [HIA _].
destruct (paper_main_gaussian_lipschitz_domain d F L HL HLip) as [HIF _].
pose proof (paper_main_gaussian_lipschitz_polynomial_bound d F L HL HLip) as HFb.
pose proof (finite_polynomial_bound_mult d C C 2 2 F F HFb HFb) as HF2b.
pose proof (finite_joint_continuous_mult d F F
  (paper_main_gaussian_lipschitz_continuous d F L HL HLip)
  (paper_main_gaussian_lipschitz_continuous d F L HL HLip)) as HF2c.
destruct (gaussian_coordinate_polynomial_domain d _ _ _ HF2c HF2b) as [HIF2 _].
pose proof (paper_main_gaussian_iterated_weighted_abs_le d _ _ _ HIF2 HF2b) as HEF2.
destruct (gaussian_iterated_difference d _ _ HIA HIF) as [HID HED].
rewrite <- HED.
set (e := L * paper_main_gaussian_width n * sqrt (INR d)).
destruct (gaussian_iterated_constant d e) as [HIe HEe].
destruct (gaussian_iterated_scale d (fun xs => F xs * F xs) (/ K) HIF2) as [HIs HEs].
destruct (gaussian_iterated_add d (fun _ => e) (fun xs => / K * (F xs * F xs)) HIe HIs)
  as [HIB HEB].
rewrite HEe in HEB; rewrite HEs in HEB.
assert (Hpt : forall xs, List.length xs = d ->
  Rabs (paper_main_gaussian_approximant d F n xs - F xs) <= e + / K * (F xs * F xs)).
{ intros xs Hxs.
  pose proof (paper_main_gaussian_smoothing_error d K L (paper_main_gaussian_width n)
    (paper_main_gaussian_clipped K F) xs (Rlt_le _ _ HKp) HL
    (Rlt_le _ _ (paper_main_gaussian_width_pos n))
    (paper_main_gaussian_level_clipped_bound d F n)
    (paper_main_gaussian_clipped_lipschitz d K F L HLip) Hxs) as H1.
  pose proof (paper_main_gaussian_clip_error K (F xs) HKp) as H2.
  change (paper_main_gaussian_approximant d F n xs) with
    (paper_main_gaussian_smoothing d (paper_main_gaussian_width n)
       (paper_main_gaussian_clipped K F) xs).
  change (paper_main_gaussian_clipped K F xs) with
    (paper_main_gaussian_clip K (F xs)) in H1.
  set (Sv := paper_main_gaussian_smoothing d (paper_main_gaussian_width n)
    (paper_main_gaussian_clipped K F) xs) in *.
  set (cz := paper_main_gaussian_clip K (F xs)) in *.
  pose proof (Rabs_triang (Sv - cz) (cz - F xs)) as H3.
  replace (Sv - cz + (cz - F xs)) with (Sv - F xs) in H3 by ring.
  assert (Hdiv : F xs * F xs / K = / K * (F xs * F xs)) by (unfold Rdiv; ring).
  fold e in H1; lra. }
assert (Hup : gaussian_iterated_expectation d
    (fun xs => paper_main_gaussian_approximant d F n xs - F xs) <=
  e + / K * gaussian_iterated_expectation d (fun xs => F xs * F xs)).
{ rewrite <- HEB; apply gaussian_iterated_monotone; [exact HID|exact HIB|].
  intros xs Hxs; pose proof (Hpt xs Hxs).
  pose proof (Rle_abs (paper_main_gaussian_approximant d F n xs - F xs)); lra. }
destruct (gaussian_iterated_scale d (fun xs => e + / K * (F xs * F xs)) (-1) HIB)
  as [HIm HEm].
rewrite HEB in HEm.
assert (Hlo : - (e + / K * gaussian_iterated_expectation d (fun xs => F xs * F xs)) <=
  gaussian_iterated_expectation d
    (fun xs => paper_main_gaussian_approximant d F n xs - F xs)).
{ replace (- (e + / K * gaussian_iterated_expectation d (fun xs => F xs * F xs))) with
    (-1 * (e + / K * gaussian_iterated_expectation d (fun xs => F xs * F xs))) by ring.
  rewrite <- HEm; apply gaussian_iterated_monotone; [exact HIm|exact HID|].
  intros xs Hxs; pose proof (Hpt xs Hxs).
  pose proof (Rle_abs (- (paper_main_gaussian_approximant d F n xs - F xs))) as H0.
  rewrite Rabs_Ropp in H0; lra. }
assert (HE2 : gaussian_iterated_expectation d (fun xs => F xs * F xs) <=
  C * C * gaussian_coordinate_weight_moment 4 ^ d).
{ pose proof (Rle_abs (gaussian_iterated_expectation d (fun xs => F xs * F xs))).
  change (gaussian_coordinate_weight_moment (2 + 2)%nat) with
    (gaussian_coordinate_weight_moment 4) in HEF2; lra. }
assert (HiK : 0 < / K) by (apply Rinv_0_lt_compat; exact HKp).
assert (Htot : e + / K * gaussian_iterated_expectation d (fun xs => F xs * F xs) <=
  (L * sqrt (INR d) + C * C * gaussian_coordinate_weight_moment 4 ^ d) / K).
{ unfold e; rewrite paper_main_gaussian_width_level; fold K.
  pose proof (Rmult_le_compat_l (/ K) _ _ (Rlt_le _ _ HiK) HE2).
  unfold Rdiv; nra. }
apply Rabs_le; split; lra.
Qed.

Theorem paper_main_gaussian_approximant_mean d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  Un_cv (fun n => gaussian_iterated_expectation d (paper_main_gaussian_approximant d F n))
    (gaussian_iterated_expectation d F).
Proof.
intros HL HLip eps Heps.
set (c := L * sqrt (INR d) +
  (paper_main_gaussian_growth_constant d F L * paper_main_gaussian_growth_constant d F L) *
    gaussian_coordinate_weight_moment 4 ^ d).
assert (Hc0 : 0 <= c).
{ unfold c; apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos; [exact HL|apply sqrt_pos].
  - apply Rmult_le_pos;
      [apply Rmult_le_pos; apply paper_main_gaussian_growth_constant_nonnegative; exact HL|].
    apply paper_main_gaussian_moment_power_nonnegative. }
destruct (INR_unbounded (c / eps)) as [N HN].
exists N; intros n Hn; unfold R_dist.
assert (HnN : INR N <= INR n) by (apply le_INR; lia).
assert (Hlev : INR n < paper_main_gaussian_level n)
  by (unfold paper_main_gaussian_level; rewrite S_INR; lra).
pose proof (paper_main_gaussian_level_pos n) as Hpos.
eapply Rle_lt_trans; [exact (paper_main_gaussian_approximant_mean_error d F L n HL HLip)|].
fold c.
assert (Hcl : c / eps < paper_main_gaussian_level n) by lra.
apply (Rmult_lt_reg_r (paper_main_gaussian_level n) _ _ Hpos).
replace (c / paper_main_gaussian_level n * paper_main_gaussian_level n) with c
  by (field; lra).
apply (Rmult_lt_reg_r (/ eps)); [apply Rinv_0_lt_compat; exact Heps|].
replace (eps * paper_main_gaussian_level n * / eps) with (paper_main_gaussian_level n)
  by (field; lra).
exact Hcl.
Qed.

(* CONDITIONAL on the one-dimensional interface at width 1/(n+1). *)

Theorem paper_main_gaussian_approximant_smooth_test_conditional d F L n :
  paper_main_gaussian_shift_derivative_interface (paper_main_gaussian_width n) ->
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  paper_main_gaussian_smooth_test d (paper_main_gaussian_approximant d F n)
    (paper_main_gaussian_smoothing_first d (paper_main_gaussian_width n)
       (paper_main_gaussian_clipped (paper_main_gaussian_level n) F))
    (paper_main_gaussian_smoothing_second d (paper_main_gaussian_width n)
       (paper_main_gaussian_clipped (paper_main_gaussian_level n) F))
    (paper_main_gaussian_smoothing_constant d (paper_main_gaussian_level n)
       (paper_main_gaussian_width n)) 0.
Proof.
intros Hint HL HLip; unfold paper_main_gaussian_approximant.
exact (paper_main_gaussian_smoothing_smooth_test_conditional d
  (paper_main_gaussian_level n) L (paper_main_gaussian_width n) _ Hint
  (Rlt_le _ _ (paper_main_gaussian_level_pos n)) HL (paper_main_gaussian_width_pos n)
  (paper_main_gaussian_level_clipped_bound d F n)
  (paper_main_gaussian_clipped_lipschitz d (paper_main_gaussian_level n) F L HLip)).
Qed.

Theorem paper_main_gaussian_approximant_gradient_conditional d F L n :
  paper_main_gaussian_shift_derivative_interface (paper_main_gaussian_width n) ->
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs, List.length xs = d ->
    finite_sum (fun a => paper_main_gaussian_smoothing_first d
      (paper_main_gaussian_width n)
      (paper_main_gaussian_clipped (paper_main_gaussian_level n) F) a xs ^ 2)
      (List.seq 0 d) <= L ^ 2.
Proof.
intros Hint HL HLip.
exact (paper_main_gaussian_smoothing_gradient_conditional d
  (paper_main_gaussian_level n) L (paper_main_gaussian_width n) _ Hint
  (Rlt_le _ _ (paper_main_gaussian_level_pos n)) HL (paper_main_gaussian_width_pos n)
  (paper_main_gaussian_level_clipped_bound d F n)
  (paper_main_gaussian_clipped_lipschitz d (paper_main_gaussian_level n) F L HLip)).
Qed.
