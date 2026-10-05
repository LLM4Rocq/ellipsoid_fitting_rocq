(* Candidate first and second derivatives of the Gaussian smoothing
   S_eps G of a bounded Euclidean-Lipschitz test, written as
   Gaussian-weighted expectations with the Hermite weights z_a and
   z_a z_b - delta_ab, and divided by eps and eps^2. For eps > 0 this
   module proves their integrability, explicit bounds, Lipschitz
   dependence on the base point and joint continuity. That they are the
   actual derivatives of S_eps G needs the affine change of variables
   and is not claimed here. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateSteinDomains GaussianCoordinateWeights
  GaussianCoordinatePolynomialContinuity GaussianExpectationContinuity
  PaperMainGaussianSmoothCalculus PaperMainGordonLipschitz
  PaperMainGaussianLipschitzClip PaperMainGaussianLipschitzSmooth.
Import ListNotations.
Open Scope R_scope.

(* The Hermite weight of a pair of coordinates: z_a^2 - 1 on the diagonal
   and z_a z_b off it. *)
Definition paper_main_gaussian_hermite_pair (a b : nat) (zs : list R) : R :=
  if Nat.eqb a b then List.nth a zs 0 * List.nth a zs 0 - 1
  else List.nth a zs 0 * List.nth b zs 0.

Definition paper_main_gaussian_smoothing_first d eps (G : list R -> R) a xs :=
  / eps * gaussian_iterated_expectation d
    (fun zs => List.nth a zs 0 * G (paper_main_gaussian_shift d xs eps zs)).

Definition paper_main_gaussian_smoothing_second d eps (G : list R -> R) a b xs :=
  / eps ^ 2 * gaussian_iterated_expectation d
    (fun zs => paper_main_gaussian_hermite_pair a b zs *
       G (paper_main_gaussian_shift d xs eps zs)).

Lemma paper_main_gaussian_polynomial_bound_ext d C p F H :
  (forall zs, List.length zs = d -> F zs = H zs) ->
  finite_polynomial_bound d C p F -> finite_polynomial_bound d C p H.
Proof.
intros He [HC HF]; split; [exact HC|].
intros zs Hzs; rewrite <- (He zs Hzs); exact (HF zs Hzs).
Qed.

Lemma paper_main_gaussian_hermite_times_bound d C p F a b :
  finite_polynomial_bound d C p F -> (a < d)%nat -> (b < d)%nat ->
  finite_polynomial_bound d C (S (S p))
    (fun zs => paper_main_gaussian_hermite_pair a b zs * F zs).
Proof.
intros HF Ha Hb; unfold paper_main_gaussian_hermite_pair.
destruct (Nat.eqb a b).
- exact (finite_polynomial_bound_times_centered_square d C p F a HF Ha).
- exact (finite_polynomial_bound_times_two_coordinates d C p F a b HF Ha Hb).
Qed.

Lemma paper_main_gaussian_hermite_times_continuous d F a b :
  finite_joint_continuous d F -> (a < d)%nat -> (b < d)%nat ->
  finite_joint_continuous d
    (fun zs => paper_main_gaussian_hermite_pair a b zs * F zs).
Proof.
intros HF Ha Hb; unfold paper_main_gaussian_hermite_pair.
destruct (Nat.eqb a b).
- exact (finite_joint_continuous_times_centered_square d F a HF Ha).
- exact (finite_joint_continuous_times_two_coordinates d F a b HF Ha Hb).
Qed.

(* An integrable function with a polynomial bound of degree p and constant
   C has expectation of size at most C times the p-th weight moment to the
   power d. *)
Lemma paper_main_gaussian_iterated_weighted_abs_le d (F : list R -> R) C p :
  gaussian_iterated_integrable d F -> finite_polynomial_bound d C p F ->
  Rabs (gaussian_iterated_expectation d F) <=
    C * gaussian_coordinate_weight_moment p ^ d.
Proof.
intros HI HF.
destruct (gaussian_iterated_constant d 0) as [HI0 HE0].
assert (HF0 : finite_polynomial_bound d C p (fun zs => F zs - 0)).
{ apply (paper_main_gaussian_polynomial_bound_ext d C p F); [|exact HF].
  intros zs _; ring. }
pose proof (gaussian_iterated_difference_bound d F (fun _ => 0) C p HI HI0 HF0) as H.
rewrite HE0 in H.
rewrite Rminus_0_r in H.
exact H.
Qed.

Lemma paper_main_gaussian_moment_power_nonnegative p d :
  0 <= gaussian_coordinate_weight_moment p ^ d.
Proof.
apply pow_le; pose proof (gaussian_coordinate_weight_moment_at_least_one p); lra.
Qed.

Lemma paper_main_gaussian_first_integrand_bound d K eps G a xs :
  0 <= K -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) -> (a < d)%nat ->
  finite_polynomial_bound d K 1
    (fun zs => List.nth a zs 0 * G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HK HG Ha.
exact (finite_polynomial_bound_times_coordinate d K 0 _ a
  (paper_main_gaussian_smoothing_integrand_bound d K eps G xs HK HG) Ha).
Qed.

Lemma paper_main_gaussian_first_integrand_continuous d L eps G a xs :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat ->
  finite_joint_continuous d
    (fun zs => List.nth a zs 0 * G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HL HLip Ha.
exact (finite_joint_continuous_times_coordinate d _ a
  (paper_main_gaussian_smoothing_integrand_continuous d L eps G xs HL HLip) Ha).
Qed.

Theorem paper_main_gaussian_first_domain d K L eps G a xs :
  0 <= K -> 0 <= L -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat ->
  gaussian_iterated_integrable d
    (fun zs => List.nth a zs 0 * G (paper_main_gaussian_shift d xs eps zs)) /\
  gaussian_iterated_absolutely_integrable d
    (fun zs => List.nth a zs 0 * G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HK HL HG HLip Ha.
destruct (gaussian_coordinate_polynomial_domain d _ K 1
  (paper_main_gaussian_first_integrand_continuous d L eps G a xs HL HLip Ha)
  (paper_main_gaussian_first_integrand_bound d K eps G a xs HK HG Ha))
  as [HI [HA _]].
split; [exact HI|exact HA].
Qed.

Theorem paper_main_gaussian_smoothing_first_bound d K L eps G a xs :
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat ->
  Rabs (paper_main_gaussian_smoothing_first d eps G a xs) <=
    / eps * (K * gaussian_coordinate_weight_moment 1 ^ d).
Proof.
intros HK HL Heps HG HLip Ha; unfold paper_main_gaussian_smoothing_first.
assert (Hie : 0 < / eps) by (apply Rinv_0_lt_compat; exact Heps).
rewrite Rabs_mult.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hie)).
apply Rmult_le_compat_l; [exact (Rlt_le _ _ Hie)|].
apply paper_main_gaussian_iterated_weighted_abs_le.
- exact (proj1 (paper_main_gaussian_first_domain d K L eps G a xs HK HL HG HLip Ha)).
- exact (paper_main_gaussian_first_integrand_bound d K eps G a xs HK HG Ha).
Qed.

Theorem paper_main_gaussian_smoothing_first_lipschitz d K L eps G a :
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (paper_main_gaussian_smoothing_first d eps G a xs -
          paper_main_gaussian_smoothing_first d eps G a ys) <=
      (/ eps * L * gaussian_coordinate_weight_moment 1 ^ d) *
        paper_main_gordon_distance d xs ys.
Proof.
intros HK HL Heps HG HLip Ha xs ys Hxs Hys.
unfold paper_main_gaussian_smoothing_first.
assert (Hie : 0 < / eps) by (apply Rinv_0_lt_compat; exact Heps).
pose proof (paper_main_gordon_distance_nonnegative d xs ys) as Hd0.
destruct (paper_main_gaussian_first_domain d K L eps G a xs HK HL HG HLip Ha) as [HIx _].
destruct (paper_main_gaussian_first_domain d K L eps G a ys HK HL HG HLip Ha) as [HIy _].
assert (HH : finite_polynomial_bound d (L * paper_main_gordon_distance d xs ys) 0
  (fun zs => G (paper_main_gaussian_shift d xs eps zs) -
             G (paper_main_gaussian_shift d ys eps zs))).
{ apply (proj2 (paper_main_polynomial_zero_bound d _ _)); split.
  - apply Rmult_le_pos; assumption.
  - intros zs _.
    eapply Rle_trans; [apply HLip; apply paper_main_gaussian_shift_length|].
    rewrite paper_main_gaussian_shift_distance; apply Rle_refl. }
assert (HB : finite_polynomial_bound d (L * paper_main_gordon_distance d xs ys) 1
  (fun zs => List.nth a zs 0 * G (paper_main_gaussian_shift d xs eps zs) -
             List.nth a zs 0 * G (paper_main_gaussian_shift d ys eps zs))).
{ apply (paper_main_gaussian_polynomial_bound_ext d _ 1
    (fun zs => List.nth a zs 0 * (G (paper_main_gaussian_shift d xs eps zs) -
                                  G (paper_main_gaussian_shift d ys eps zs)))).
  - intros zs _; ring.
  - exact (finite_polynomial_bound_times_coordinate d _ 0 _ a HH Ha). }
pose proof (gaussian_iterated_difference_bound d _ _ _ 1 HIx HIy HB) as Hdiff.
rewrite <- Rmult_minus_distr_l.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hie)).
replace (/ eps * L * gaussian_coordinate_weight_moment 1 ^ d *
  paper_main_gordon_distance d xs ys) with
  (/ eps * (L * paper_main_gordon_distance d xs ys *
    gaussian_coordinate_weight_moment 1 ^ d)) by ring.
apply Rmult_le_compat_l; [exact (Rlt_le _ _ Hie)|exact Hdiff].
Qed.

Theorem paper_main_gaussian_smoothing_first_continuous d K L eps G a :
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat ->
  finite_joint_continuous d (paper_main_gaussian_smoothing_first d eps G a).
Proof.
intros HK HL Heps HG HLip Ha.
apply (paper_main_gaussian_lipschitz_continuous d _
  (/ eps * L * gaussian_coordinate_weight_moment 1 ^ d)).
- apply Rmult_le_pos; [apply Rmult_le_pos; [left; apply Rinv_0_lt_compat; exact Heps|exact HL]|].
  apply paper_main_gaussian_moment_power_nonnegative.
- exact (paper_main_gaussian_smoothing_first_lipschitz d K L eps G a HK HL Heps HG HLip Ha).
Qed.

Lemma paper_main_gaussian_second_integrand_bound d K eps G a b xs :
  0 <= K -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (a < d)%nat -> (b < d)%nat ->
  finite_polynomial_bound d K 2
    (fun zs => paper_main_gaussian_hermite_pair a b zs *
       G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HK HG Ha Hb.
exact (paper_main_gaussian_hermite_times_bound d K 0 _ a b
  (paper_main_gaussian_smoothing_integrand_bound d K eps G xs HK HG) Ha Hb).
Qed.

Lemma paper_main_gaussian_second_integrand_continuous d L eps G a b xs :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat -> (b < d)%nat ->
  finite_joint_continuous d
    (fun zs => paper_main_gaussian_hermite_pair a b zs *
       G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HL HLip Ha Hb.
exact (paper_main_gaussian_hermite_times_continuous d _ a b
  (paper_main_gaussian_smoothing_integrand_continuous d L eps G xs HL HLip) Ha Hb).
Qed.

Theorem paper_main_gaussian_second_domain d K L eps G a b xs :
  0 <= K -> 0 <= L -> (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat -> (b < d)%nat ->
  gaussian_iterated_integrable d
    (fun zs => paper_main_gaussian_hermite_pair a b zs *
       G (paper_main_gaussian_shift d xs eps zs)) /\
  gaussian_iterated_absolutely_integrable d
    (fun zs => paper_main_gaussian_hermite_pair a b zs *
       G (paper_main_gaussian_shift d xs eps zs)).
Proof.
intros HK HL HG HLip Ha Hb.
destruct (gaussian_coordinate_polynomial_domain d _ K 2
  (paper_main_gaussian_second_integrand_continuous d L eps G a b xs HL HLip Ha Hb)
  (paper_main_gaussian_second_integrand_bound d K eps G a b xs HK HG Ha Hb))
  as [HI [HA _]].
split; [exact HI|exact HA].
Qed.

Theorem paper_main_gaussian_smoothing_second_bound d K L eps G a b xs :
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat -> (b < d)%nat ->
  Rabs (paper_main_gaussian_smoothing_second d eps G a b xs) <=
    / eps ^ 2 * (K * gaussian_coordinate_weight_moment 2 ^ d).
Proof.
intros HK HL Heps HG HLip Ha Hb; unfold paper_main_gaussian_smoothing_second.
assert (Hie : 0 < / eps ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact Heps).
rewrite Rabs_mult.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hie)).
apply Rmult_le_compat_l; [exact (Rlt_le _ _ Hie)|].
apply paper_main_gaussian_iterated_weighted_abs_le.
- exact (proj1 (paper_main_gaussian_second_domain d K L eps G a b xs HK HL HG HLip Ha Hb)).
- exact (paper_main_gaussian_second_integrand_bound d K eps G a b xs HK HG Ha Hb).
Qed.

Theorem paper_main_gaussian_smoothing_second_lipschitz d K L eps G a b :
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat -> (b < d)%nat ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (paper_main_gaussian_smoothing_second d eps G a b xs -
          paper_main_gaussian_smoothing_second d eps G a b ys) <=
      (/ eps ^ 2 * L * gaussian_coordinate_weight_moment 2 ^ d) *
        paper_main_gordon_distance d xs ys.
Proof.
intros HK HL Heps HG HLip Ha Hb xs ys Hxs Hys.
unfold paper_main_gaussian_smoothing_second.
assert (Hie : 0 < / eps ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact Heps).
pose proof (paper_main_gordon_distance_nonnegative d xs ys) as Hd0.
destruct (paper_main_gaussian_second_domain d K L eps G a b xs HK HL HG HLip Ha Hb)
  as [HIx _].
destruct (paper_main_gaussian_second_domain d K L eps G a b ys HK HL HG HLip Ha Hb)
  as [HIy _].
assert (HH : finite_polynomial_bound d (L * paper_main_gordon_distance d xs ys) 0
  (fun zs => G (paper_main_gaussian_shift d xs eps zs) -
             G (paper_main_gaussian_shift d ys eps zs))).
{ apply (proj2 (paper_main_polynomial_zero_bound d _ _)); split.
  - apply Rmult_le_pos; assumption.
  - intros zs _.
    eapply Rle_trans; [apply HLip; apply paper_main_gaussian_shift_length|].
    rewrite paper_main_gaussian_shift_distance; apply Rle_refl. }
assert (HB : finite_polynomial_bound d (L * paper_main_gordon_distance d xs ys) 2
  (fun zs => paper_main_gaussian_hermite_pair a b zs *
               G (paper_main_gaussian_shift d xs eps zs) -
             paper_main_gaussian_hermite_pair a b zs *
               G (paper_main_gaussian_shift d ys eps zs))).
{ apply (paper_main_gaussian_polynomial_bound_ext d _ 2
    (fun zs => paper_main_gaussian_hermite_pair a b zs *
      (G (paper_main_gaussian_shift d xs eps zs) -
       G (paper_main_gaussian_shift d ys eps zs)))).
  - intros zs _; ring.
  - exact (paper_main_gaussian_hermite_times_bound d _ 0 _ a b HH Ha Hb). }
pose proof (gaussian_iterated_difference_bound d _ _ _ 2 HIx HIy HB) as Hdiff.
rewrite <- Rmult_minus_distr_l.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hie)).
replace (/ eps ^ 2 * L * gaussian_coordinate_weight_moment 2 ^ d *
  paper_main_gordon_distance d xs ys) with
  (/ eps ^ 2 * (L * paper_main_gordon_distance d xs ys *
    gaussian_coordinate_weight_moment 2 ^ d)) by ring.
apply Rmult_le_compat_l; [exact (Rlt_le _ _ Hie)|exact Hdiff].
Qed.

Theorem paper_main_gaussian_smoothing_second_continuous d K L eps G a b :
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = d -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance d xs ys) ->
  (a < d)%nat -> (b < d)%nat ->
  finite_joint_continuous d (paper_main_gaussian_smoothing_second d eps G a b).
Proof.
intros HK HL Heps HG HLip Ha Hb.
apply (paper_main_gaussian_lipschitz_continuous d _
  (/ eps ^ 2 * L * gaussian_coordinate_weight_moment 2 ^ d)).
- apply Rmult_le_pos;
    [apply Rmult_le_pos; [left; apply Rinv_0_lt_compat; apply pow_lt; exact Heps|exact HL]|].
  apply paper_main_gaussian_moment_power_nonnegative.
- exact (paper_main_gaussian_smoothing_second_lipschitz d K L eps G a b
    HK HL Heps HG HLip Ha Hb).
Qed.
