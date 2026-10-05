(* Gaussian smoothing of bounded Euclidean-Lipschitz tests on lists of
   length d. The shift list is x + eps z on the first d coordinates and
   S_eps G xs is the iterated Gaussian expectation of G (xs + eps zs).
   For G bounded by K and L-Lipschitz, the integrand is continuous,
   bounded and integrable; S_eps G is bounded by K, L-Lipschitz, and
   within L * eps * sqrt d of G. These are actual approximants; no
   differentiability is claimed here. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateSteinDomains GaussianCovarianceSums
  GaussianExpectationContinuity PaperMainGaussianSmoothCalculus
  PaperMainGordonLipschitz PaperMainGaussianNorm PaperMainGaussianLipschitzClip.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_shift d (xs : list R) (eps : R) (zs : list R) :
    list R :=
  map (fun a => List.nth a xs 0 + eps * List.nth a zs 0) (List.seq 0 d).

Definition paper_main_gaussian_smoothing d (eps : R) (G : list R -> R)
    (xs : list R) : R :=
  gaussian_iterated_expectation d (fun zs => G (paper_main_gaussian_shift d xs eps zs)).

Lemma paper_main_gaussian_shift_length d xs eps zs :
  List.length (paper_main_gaussian_shift d xs eps zs) = d.
Proof. unfold paper_main_gaussian_shift; apply length_map_seq. Qed.

Lemma paper_main_gaussian_shift_nth d xs eps zs a :
  (a < d)%nat ->
  List.nth a (paper_main_gaussian_shift d xs eps zs) 0 =
    List.nth a xs 0 + eps * List.nth a zs 0.
Proof.
intros Ha; unfold paper_main_gaussian_shift.
exact (nth_map_seq (fun a => List.nth a xs 0 + eps * List.nth a zs 0) d a Ha).
Qed.

Lemma paper_main_gaussian_shift_zero d xs zs :
  List.length xs = d -> paper_main_gaussian_shift d xs 0 zs = xs.
Proof.
intros Hxs; apply (nth_ext _ _ 0 0).
- rewrite paper_main_gaussian_shift_length; symmetry; exact Hxs.
- intros a Ha; rewrite paper_main_gaussian_shift_length in Ha.
  rewrite (paper_main_gaussian_shift_nth d xs 0 zs a Ha); ring.
Qed.

Lemma paper_main_gaussian_shift_distance d xs ys eps zs :
  paper_main_gordon_distance d (paper_main_gaussian_shift d xs eps zs)
    (paper_main_gaussian_shift d ys eps zs) =
  paper_main_gordon_distance d xs ys.
Proof.
unfold paper_main_gordon_distance; f_equal.
apply finite_sum_ext; intros k Hk; apply in_seq in Hk.
rewrite (paper_main_gaussian_shift_nth d xs eps zs k ltac:(lia)).
rewrite (paper_main_gaussian_shift_nth d ys eps zs k ltac:(lia)); ring.
Qed.

Lemma paper_main_gaussian_shift_noise_distance d xs eps zs ws :
  paper_main_gordon_distance d (paper_main_gaussian_shift d xs eps zs)
    (paper_main_gaussian_shift d xs eps ws) =
  Rabs eps * paper_main_gordon_distance d zs ws.
Proof.
unfold paper_main_gordon_distance.
assert (Hsum : finite_sum (fun k =>
    (List.nth k (paper_main_gaussian_shift d xs eps zs) 0 -
     List.nth k (paper_main_gaussian_shift d xs eps ws) 0) ^ 2) (List.seq 0 d) =
  eps ^ 2 * finite_sum (fun k => (List.nth k zs 0 - List.nth k ws 0) ^ 2)
    (List.seq 0 d)).
{ rewrite <- finite_sum_scale; apply finite_sum_ext; intros k Hk.
  apply in_seq in Hk.
  rewrite (paper_main_gaussian_shift_nth d xs eps zs k ltac:(lia)).
  rewrite (paper_main_gaussian_shift_nth d xs eps ws k ltac:(lia)); ring. }
rewrite Hsum.
assert (HT : 0 <= finite_sum (fun k => (List.nth k zs 0 - List.nth k ws 0) ^ 2)
  (List.seq 0 d)) by (apply finite_sum_nonneg; intros; apply pow2_ge_0).
rewrite (sqrt_mult _ _ (pow2_ge_0 eps) HT).
f_equal; rewrite <- sqrt_Rsqr_abs; f_equal; unfold Rsqr; ring.
Qed.

Lemma paper_main_gaussian_shift_center_distance d xs eps zs :
  0 <= eps -> List.length zs = d ->
  paper_main_gordon_distance d (paper_main_gaussian_shift d xs eps zs) xs =
  eps * paper_main_gaussian_norm zs.
Proof.
intros Heps Hzs; unfold paper_main_gordon_distance, paper_main_gaussian_norm.
assert (Hsum : finite_sum (fun k =>
    (List.nth k (paper_main_gaussian_shift d xs eps zs) 0 - List.nth k xs 0) ^ 2)
    (List.seq 0 d) =
  eps ^ 2 * gaussian_sum_squares zs).
{ rewrite <- (paper_main_gaussian_squares_coordinates d zs Hzs).
  rewrite <- finite_sum_scale; apply finite_sum_ext; intros k Hk.
  apply in_seq in Hk.
  rewrite (paper_main_gaussian_shift_nth d xs eps zs k ltac:(lia)); ring. }
rewrite Hsum.
assert (HT : 0 <= gaussian_sum_squares zs).
{ rewrite <- (paper_main_gaussian_squares_coordinates d zs Hzs).
  apply finite_sum_nonneg; intros; apply pow2_ge_0. }
rewrite (sqrt_mult _ _ (pow2_ge_0 eps) HT).
rewrite (sqrt_pow2 _ Heps); reflexivity.
Qed.

Lemma paper_main_gaussian_smoothing_integrand_continuous d L eps G xs :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  finite_joint_continuous d (fun zs => G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HL HLip.
apply (paper_main_gaussian_lipschitz_continuous d _ (L * Rabs eps)).
- apply Rmult_le_pos; [exact HL|apply Rabs_pos].
- intros zs ws _ _.
  eapply Rle_trans; [apply HLip; apply paper_main_gaussian_shift_length|].
  rewrite paper_main_gaussian_shift_noise_distance; right; ring.
Qed.

Lemma paper_main_gaussian_smoothing_integrand_bound d K eps G xs :
  0 <= K -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  finite_polynomial_bound d K 0 (fun zs => G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HK HG.
apply (proj2 (paper_main_polynomial_zero_bound d K _)); split; [exact HK|].
intros zs _; apply HG; apply paper_main_gaussian_shift_length.
Qed.

Theorem paper_main_gaussian_smoothing_domain d K L eps G xs :
  0 <= K -> 0 <= L -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_integrable d (fun zs => G (paper_main_gaussian_shift d xs eps zs)) /\
  gaussian_iterated_absolutely_integrable d
    (fun zs => G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HK HL HG HLip.
destruct (gaussian_coordinate_polynomial_domain d _ K 0
  (paper_main_gaussian_smoothing_integrand_continuous d L eps G xs HL HLip)
  (paper_main_gaussian_smoothing_integrand_bound d K eps G xs HK HG)) as [HI [HA _]].
split; [exact HI|exact HA].
Qed.

(* An integrable function with values in [-c, c] has expectation in
   [-c, c]. *)
Lemma paper_main_gaussian_iterated_abs_le d (F : list R -> R) c :
  gaussian_iterated_integrable d F ->
  (forall zs, List.length zs = d -> Rabs (F zs) <= c) ->
  Rabs (gaussian_iterated_expectation d F) <= c.
Proof.
intros HI Hb.
destruct (gaussian_iterated_constant d c) as [HIc HEc].
destruct (gaussian_iterated_constant d (- c)) as [HIn HEn].
assert (Hup : gaussian_iterated_expectation d F <= c).
{ rewrite <- HEc; apply gaussian_iterated_monotone; [exact HI|exact HIc|].
  intros zs Hzs; pose proof (Hb zs Hzs); pose proof (Rle_abs (F zs)); lra. }
assert (Hlo : - c <= gaussian_iterated_expectation d F).
{ rewrite <- HEn; apply gaussian_iterated_monotone; [exact HIn|exact HI|].
  intros zs Hzs; pose proof (Hb zs Hzs).
  pose proof (Rle_abs (- F zs)); rewrite Rabs_Ropp in H0; lra. }
apply Rabs_le; split; assumption.
Qed.

Theorem paper_main_gaussian_smoothing_bound d K L eps G xs :
  0 <= K -> 0 <= L -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  Rabs (paper_main_gaussian_smoothing d eps G xs) <= K.
Proof.
intros HK HL HG HLip; unfold paper_main_gaussian_smoothing.
apply paper_main_gaussian_iterated_abs_le.
- exact (proj1 (paper_main_gaussian_smoothing_domain d K L eps G xs HK HL HG HLip)).
- intros zs _; apply HG; apply paper_main_gaussian_shift_length.
Qed.

Theorem paper_main_gaussian_smoothing_lipschitz d K L eps G :
  0 <= K -> 0 <= L -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (paper_main_gaussian_smoothing d eps G xs -
          paper_main_gaussian_smoothing d eps G ys) <=
      L * paper_main_gordon_distance d xs ys.
Proof.
intros HK HL HG HLip xs ys _ _; unfold paper_main_gaussian_smoothing.
destruct (gaussian_iterated_difference d
  (fun zs => G (paper_main_gaussian_shift d xs eps zs))
  (fun zs => G (paper_main_gaussian_shift d ys eps zs))
  (proj1 (paper_main_gaussian_smoothing_domain d K L eps G xs HK HL HG HLip))
  (proj1 (paper_main_gaussian_smoothing_domain d K L eps G ys HK HL HG HLip)))
  as [HI HE].
rewrite <- HE.
apply paper_main_gaussian_iterated_abs_le; [exact HI|].
intros zs _.
eapply Rle_trans; [apply HLip; apply paper_main_gaussian_shift_length|].
rewrite paper_main_gaussian_shift_distance; apply Rle_refl.
Qed.

Theorem paper_main_gaussian_smoothing_continuous d K L eps G :
  0 <= K -> 0 <= L -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  finite_joint_continuous d (paper_main_gaussian_smoothing d eps G).
Proof.
intros HK HL HG HLip.
apply (paper_main_gaussian_lipschitz_continuous d _ L HL).
exact (paper_main_gaussian_smoothing_lipschitz d K L eps G HK HL HG HLip).
Qed.

Theorem paper_main_gaussian_smoothing_error d K L eps G xs :
  0 <= K -> 0 <= L -> 0 <= eps -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  List.length xs = d ->
  Rabs (paper_main_gaussian_smoothing d eps G xs - G xs) <=
    L * eps * sqrt (INR d).
Proof.
intros HK HL Heps HG HLip Hxs; unfold paper_main_gaussian_smoothing.
destruct (gaussian_iterated_constant d (G xs)) as [HIc HEc].
destruct (gaussian_iterated_difference d
  (fun zs => G (paper_main_gaussian_shift d xs eps zs)) (fun _ => G xs)
  (proj1 (paper_main_gaussian_smoothing_domain d K L eps G xs HK HL HG HLip)) HIc)
  as [HI HE].
rewrite HEc in HE; rewrite <- HE.
destruct (gaussian_coordinate_polynomial_domain d paper_main_gaussian_norm
  (1 + INR d) 2 (paper_main_gaussian_norm_continuous d)
  (paper_main_gaussian_norm_polynomial d)) as [HIn _].
destruct (gaussian_iterated_scale d paper_main_gaussian_norm (L * eps) HIn)
  as [HIs HEs].
destruct (gaussian_iterated_scale d paper_main_gaussian_norm (- (L * eps)) HIn)
  as [HIs' HEs'].
destruct (paper_main_gaussian_norm_expectation d) as [HE0 HEd].
assert (Hpt : forall zs, List.length zs = d ->
  Rabs (G (paper_main_gaussian_shift d xs eps zs) - G xs) <=
    L * eps * paper_main_gaussian_norm zs).
{ intros zs Hzs.
  eapply Rle_trans; [apply HLip; [apply paper_main_gaussian_shift_length|exact Hxs]|].
  rewrite (paper_main_gaussian_shift_center_distance d xs eps zs Heps Hzs).
  right; ring. }
assert (Hup : gaussian_iterated_expectation d
    (fun zs => G (paper_main_gaussian_shift d xs eps zs) - G xs) <=
  L * eps * gaussian_iterated_expectation d paper_main_gaussian_norm).
{ rewrite <- HEs; apply gaussian_iterated_monotone; [exact HI|exact HIs|].
  intros zs Hzs; pose proof (Hpt zs Hzs).
  pose proof (Rle_abs (G (paper_main_gaussian_shift d xs eps zs) - G xs)); lra. }
assert (Hlo : - (L * eps) * gaussian_iterated_expectation d paper_main_gaussian_norm <=
  gaussian_iterated_expectation d
    (fun zs => G (paper_main_gaussian_shift d xs eps zs) - G xs)).
{ rewrite <- HEs'; apply gaussian_iterated_monotone; [exact HIs'|exact HI|].
  intros zs Hzs; pose proof (Hpt zs Hzs).
  pose proof (Rle_abs (- (G (paper_main_gaussian_shift d xs eps zs) - G xs))).
  rewrite Rabs_Ropp in H0; lra. }
assert (HLe : 0 <= L * eps) by (apply Rmult_le_pos; assumption).
apply Rabs_le; split.
- apply Rle_trans with (- (L * eps) * gaussian_iterated_expectation d
    paper_main_gaussian_norm); [|exact Hlo].
  pose proof (Rmult_le_compat_l (L * eps) _ _ HLe HEd); nra.
- apply Rle_trans with (L * eps * gaussian_iterated_expectation d
    paper_main_gaussian_norm); [exact Hup|].
  apply Rmult_le_compat_l; [exact HLe|exact HEd].
Qed.

Lemma paper_main_gaussian_smoothing_dim_zero eps G xs :
  paper_main_gaussian_smoothing 0 eps G xs = G [].
Proof. reflexivity. Qed.
