(* The translated Gaussian quadratic form Y = x^T H x - Tr H - b and its
   rotation to independent centered squares. For a real symmetric H of size
   d and real b, paper_main_symmetric_quadratic_list
   (Spectral.DiagonalizationLists) gives a loading O with
   orthonormal rows and coefficients c with
     x^T H x - Tr H = sum_(i < d) c_i (z_i^2 - 1),  z = O x,
     sum_(i < d) c_i^2 = |H|_F^2.
   - For every k the function (sum_i c_i (z_i^2 - 1) - b)^(k+2) is a smooth
     test in the sense of Gaussian.SmoothCovariance: explicit first
     and second coordinate derivatives (chain and product rules of
     Gaussian.OrthogonalCutoff), continuity, and polynomial bounds
     with the weight prod_j (1 + |z_j|)^(2(k+2))
     (paper_main_head_small_ball_test_smooth).
   - Hence, by the rotation invariance
     paper_main_gaussian_orthogonal_smooth_expectation, the iterated
     Gaussian expectation of Y^(k+2) equals that of
     (sum_i c_i (x_i^2 - 1) - b)^(k+2)
     (paper_main_head_small_ball_rotation). The loading and the
     coefficients do not depend on b or k.
   The case d = 0 is included. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Soft.Extrema Analysis.CoordinateContinuityDefinitions
  Gaussian.CoordinateWeightDefinitions Gaussian.CoordinateWeights
  Gaussian.CoordinateDerivativeDefinitions Analysis.CoordinateTopology
  Gaussian.CoordinatePolynomialContinuity Gaussian.FiniteSums
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages
  Gaussian.IteratedExpectationDefinitions Gaussian.CovarianceDefinitions
  Gaussian.IteratedExpectation Gaussian.Moments PaperMainDefinitions
  Geometry.Psd Gordon.Continuity Gaussian.SmoothCalculus
  Gaussian.SmoothCovariance Gaussian.WeightedSquare Gaussian.WeightedSquareLaw
  Gaussian.Orthogonal Gaussian.OrthogonalCutoff Spectral.DiagonalizationLists
  Gaussian.QuadraticTail.
Import ListNotations.
Open Scope R_scope.

(* The shifted power and its derivatives. *)

Lemma paper_main_head_small_ball_power_derive (b : R) (n : nat) (y : R) :
  @is_derive R R^o R^o y 1 (fun t => (t - b) ^ S n) (INR (S n) * (y - b) ^ n).
Proof.
assert (H2 : @is_derive R R^o R^o y 1 (fun t => t - b) 1).
{ eapply paper_main_gaussian_orthogonal_derive_value;
    [|exact (is_derive_minus (fun t => t) (fun _ => b) y 1 0
      (is_derive_id_R y) (is_derive_const _ _))].
  ring. }
pose proof (is_derive_comp (fun t => t ^ S n) (fun t => t - b) y
  (INR (S n) * (y - b) ^ n) 1 (gaussian_power_derivative n (y - b)) H2) as H.
eapply paper_main_gaussian_orthogonal_derive_value; [|exact H].
ring.
Qed.

Lemma paper_main_head_small_ball_scaled_derive (b a : R) (n : nat) (y : R) :
  @is_derive R R^o R^o y 1 (fun t => a * (t - b) ^ S n) (a * INR (S n) * (y - b) ^ n).
Proof.
pose proof (is_derive_scal a _ _ _ (paper_main_head_small_ball_power_derive b n y)) as H.
eapply paper_main_gaussian_orthogonal_derive_value; [|exact H].
ring.
Qed.

Lemma paper_main_head_small_ball_power_continuous (b a : R) (m : nat) (y : R) :
  {for y, continuous (fun t => a * (t - b) ^ m)}.
Proof.
destruct m as [|n].
- have E : (fun t : R => a * (t - b) ^ 0) = (fun _ => a).
  { by apply/funext => t; rewrite /= Rmult_1_r. }
  rewrite E; exact (continuous_const R a y).
- exact (is_derive_continuous _ _ _ (paper_main_head_small_ball_scaled_derive b a n y)).
Qed.

(* The test function and its coordinate derivatives. *)

Definition paper_main_head_small_ball_test d (c : nat -> R) (b : R) (k : nat)
    (xs : list R) : R :=
  (paper_main_weighted_square d c xs - b) ^ S (S k).

Definition paper_main_head_small_ball_test1 d (c : nat -> R) (b : R) (k : nat) i
    (xs : list R) : R :=
  INR (S (S k)) * (paper_main_weighted_square d c xs - b) ^ S k *
  paper_main_gaussian_orthogonal_square_first c i xs.

Definition paper_main_head_small_ball_test2 d (c : nat -> R) (b : R) (k : nat) i j
    (xs : list R) : R :=
  INR (S (S k)) * INR (S k) * (paper_main_weighted_square d c xs - b) ^ k *
    paper_main_gaussian_orthogonal_square_first c j xs *
    paper_main_gaussian_orthogonal_square_first c i xs +
  INR (S (S k)) * (paper_main_weighted_square d c xs - b) ^ S k *
    paper_main_gaussian_orthogonal_square_second c i j xs.

Lemma paper_main_head_small_ball_test_derivative d (c : nat -> R) b k i :
  (i < d)%coq_nat ->
  finite_coordinate_derivative d i (paper_main_head_small_ball_test d c b k)
    (paper_main_head_small_ball_test1 d c b k i).
Proof.
intros Hi.
exact (paper_main_gaussian_orthogonal_coordinate_comp d i
  (fun y => (y - b) ^ S (S k)) (fun y => INR (S (S k)) * (y - b) ^ S k) _ _
  (paper_main_head_small_ball_power_derive b (S k))
  (paper_main_gaussian_orthogonal_square_derivative d c i Hi)).
Qed.

Lemma paper_main_head_small_ball_test1_derivative d (c : nat -> R) b k i j :
  (j < d)%coq_nat ->
  finite_coordinate_derivative d j (paper_main_head_small_ball_test1 d c b k i)
    (paper_main_head_small_ball_test2 d c b k i j).
Proof.
intros Hj.
exact (paper_main_coordinate_derivative_mult d j _ _ _ _
  (paper_main_gaussian_orthogonal_coordinate_comp d j
    (fun y => INR (S (S k)) * (y - b) ^ S k)
    (fun y => INR (S (S k)) * INR (S k) * (y - b) ^ k) _ _
    (paper_main_head_small_ball_scaled_derive b (INR (S (S k))) k)
    (paper_main_gaussian_orthogonal_square_derivative d c j Hj))
  (paper_main_gaussian_orthogonal_square_second_derivative d c i j Hj)).
Qed.

Lemma paper_main_head_small_ball_comp_continuous d (c : nat -> R) (b a : R) (m : nat) :
  finite_joint_continuous d (fun xs => a * (paper_main_weighted_square d c xs - b) ^ m).
Proof.
apply (paper_main_gordon_joint_comp d (paper_main_weighted_square d c)
  (fun y => a * (y - b) ^ m)).
- exact (paper_main_weighted_square_continuous d c).
- intros xs _; apply paper_main_head_small_ball_power_continuous.
Qed.

Lemma paper_main_head_small_ball_test_continuous d (c : nat -> R) b k :
  finite_joint_continuous d (paper_main_head_small_ball_test d c b k).
Proof.
apply (finite_joint_continuous_ext d
  (fun xs => 1 * (paper_main_weighted_square d c xs - b) ^ S (S k))).
- by intros xs _; rewrite /paper_main_head_small_ball_test Rmult_1_l.
- exact (paper_main_head_small_ball_comp_continuous d c b 1 (S (S k))).
Qed.

Lemma paper_main_head_small_ball_test1_continuous d (c : nat -> R) b k i :
  (i < d)%coq_nat ->
  finite_joint_continuous d (paper_main_head_small_ball_test1 d c b k i).
Proof.
intros Hi; unfold paper_main_head_small_ball_test1.
apply finite_joint_continuous_mult.
- exact (paper_main_head_small_ball_comp_continuous d c b (INR (S (S k))) (S k)).
- exact (paper_main_gaussian_orthogonal_square_first_continuous d c i Hi).
Qed.

Lemma paper_main_head_small_ball_test2_continuous d (c : nat -> R) b k i j :
  (i < d)%coq_nat -> (j < d)%coq_nat ->
  finite_joint_continuous d (paper_main_head_small_ball_test2 d c b k i j).
Proof.
intros Hi Hj; unfold paper_main_head_small_ball_test2.
apply finite_joint_continuous_add; apply finite_joint_continuous_mult.
- apply finite_joint_continuous_mult.
  + exact (paper_main_head_small_ball_comp_continuous d c b
      (INR (S (S k)) * INR (S k)) k).
  + exact (paper_main_gaussian_orthogonal_square_first_continuous d c j Hj).
- exact (paper_main_gaussian_orthogonal_square_first_continuous d c i Hi).
- exact (paper_main_head_small_ball_comp_continuous d c b (INR (S (S k))) (S k)).
- exact (paper_main_gaussian_orthogonal_square_second_continuous d c i j).
Qed.

(* Polynomial bounds. W is the weight prod_j (1 + |x_j|), K = |b| + 2 d L + 1
   and B = K W^2. *)

Lemma paper_main_head_small_ball_square_bound d (c : nat -> R) (L : R) (xs : list R) :
  0 <= L -> (forall i, (i < d)%coq_nat -> Rabs (c i) <= L) -> List.length xs = d ->
  Rabs (paper_main_weighted_square d c xs) <=
    2 * INR d * L * gaussian_coordinate_product_weight 1 xs ^ 2.
Proof.
intros HL Hc Hxs.
pose proof (gaussian_coordinate_product_weight_at_least_one 1 xs) as HW.
unfold paper_main_weighted_square.
eapply Rle_trans; [apply finite_sum_abs_le|].
eapply Rle_trans.
- apply (finite_sum_le _ (fun _ => 2 * L * gaussian_coordinate_product_weight 1 xs ^ 2)).
  intros i Hi.
  have Hi' : (i < d)%coq_nat by have := proj1 (in_seq d 0 i) Hi; lia.
  pose proof (coordinate_le_weight_one xs i ltac:(lia)) as Hx.
  pose proof (Hc i Hi') as Hci.
  pose proof (Rabs_pos (c i)) as Hc0.
  pose proof (Rabs_pos (List.nth i xs 0)) as Hx0.
  rewrite Rabs_mult.
  have Hsq : Rabs (List.nth i xs 0 ^ 2 - 1) <=
      2 * gaussian_coordinate_product_weight 1 xs ^ 2.
  { apply Rabs_le; split.
    - pose proof (pow2_ge_0 (List.nth i xs 0)); nra.
    - have Hx2 : List.nth i xs 0 ^ 2 <= gaussian_coordinate_product_weight 1 xs ^ 2.
      { rewrite -(pow2_abs (List.nth i xs 0)); apply pow_incr; lra. }
      nra. }
  nra.
- rewrite finite_sum_const List.length_seq; nra.
Qed.

Lemma paper_main_head_small_ball_weight_power (K W : R) (k : nat) :
  K ^ S (S k) * W ^ (2 * S (S k)) = (K * W ^ 2) ^ S (S k).
Proof. by rewrite Rpow_mult_distr pow_mult. Qed.

Theorem paper_main_head_small_ball_test_smooth d (c : nat -> R) (b L : R) (k : nat) :
  0 <= L -> (forall i, (i < d)%coq_nat -> Rabs (c i) <= L) ->
  paper_main_gaussian_smooth_test d (paper_main_head_small_ball_test d c b k)
    (paper_main_head_small_ball_test1 d c b k) (paper_main_head_small_ball_test2 d c b k)
    (2 * INR (S (S k)) ^ 2 * (2 * L + 1) ^ 2 * (Rabs b + 2 * INR d * L + 1) ^ S (S k))
    (2 * S (S k)).
Proof.
intros HL Hc.
set (K := Rabs b + 2 * INR d * L + 1).
assert (HK : 1 <= K) by (unfold K; pose proof (Rabs_pos b); pose proof (pos_INR d); nra).
assert (HkR : 2 <= INR (S (S k))) by (rewrite !S_INR; pose proof (pos_INR k); lra).
assert (HC0 : 0 <= 2 * INR (S (S k)) ^ 2 * (2 * L + 1) ^ 2 * K ^ S (S k)).
{ repeat apply Rmult_le_pos; try lra; try apply pow2_ge_0; apply pow_le; lra. }
(* The common estimate at a point. *)
assert (Hpt : forall xs, List.length xs = d ->
  let W := gaussian_coordinate_product_weight 1 xs in
  let B := K * W ^ 2 in
  1 <= W /\ W <= B /\ 1 <= B /\
  Rabs (paper_main_weighted_square d c xs - b) <= B /\
  (forall i, (i < d)%coq_nat ->
    Rabs (paper_main_gaussian_orthogonal_square_first c i xs) <= 2 * L * B) /\
  (forall i j, (i < d)%coq_nat ->
    Rabs (paper_main_gaussian_orthogonal_square_second c i j xs) <= 2 * L) /\
  2 * INR (S (S k)) ^ 2 * (2 * L + 1) ^ 2 * K ^ S (S k) *
    gaussian_coordinate_product_weight (2 * S (S k)) xs =
  2 * INR (S (S k)) ^ 2 * (2 * L + 1) ^ 2 * B ^ S (S k)).
{ intros xs Hxs W B.
  assert (HW : 1 <= W) by apply gaussian_coordinate_product_weight_at_least_one.
  assert (HW2 : W <= W ^ 2) by nra.
  assert (HB : W ^ 2 <= B) by (unfold B; nra).
  split; [exact HW|]; split; [lra|]; split; [nra|].
  split.
  { pose proof (paper_main_head_small_ball_square_bound d c L xs HL Hc Hxs) as Hs.
    fold W in Hs.
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite Rabs_Ropp.
    unfold B, K.
    pose proof (Rabs_pos b); pose proof (pos_INR d); nra. }
  split.
  { intros i Hi.
    pose proof (paper_main_gaussian_orthogonal_square_first_bound c L i xs (Hc i Hi)
      ltac:(lia)) as H1; fold W in H1.
    nra. }
  split.
  { intros i j Hi; exact (paper_main_gaussian_orthogonal_square_second_bound c L i j xs
      (Hc i Hi) HL). }
  rewrite -(product_weight_one_pow (2 * S (S k)) xs); fold W.
  rewrite Rmult_assoc (paper_main_head_small_ball_weight_power K W k).
  by unfold B; ring. }
split.
- exact (paper_main_head_small_ball_test_continuous d c b k).
- intros i Hi; exact (paper_main_head_small_ball_test_derivative d c b k i Hi).
- intros i Hi; exact (paper_main_head_small_ball_test1_continuous d c b k i Hi).
- intros i j Hi Hj; exact (paper_main_head_small_ball_test1_derivative d c b k i j Hj).
- intros i j Hi Hj; exact (paper_main_head_small_ball_test2_continuous d c b k i j Hi Hj).
- (* The bound of the test. *)
  split; [exact HC0|]; intros xs Hxs.
  destruct (Hpt xs Hxs) as [HW [HWB [HB1 [HA [_ [_ HE]]]]]].
  rewrite HE.
  set (W := gaussian_coordinate_product_weight 1 xs) in *.
  set (B := K * W ^ 2) in *.
  unfold paper_main_head_small_ball_test.
  set (A := paper_main_weighted_square d c xs - b) in *.
  clearbody A.
  rewrite -(RPow_abs A (S (S k))).
  have Hp : Rabs A ^ S (S k) <= B ^ S (S k).
  { apply pow_incr; split; [apply Rabs_pos|exact HA]. }
  have HBp : 1 <= B ^ S (S k) by (apply pow_R1_Rle; lra).
  have Hf : 1 <= 2 * INR (S (S k)) ^ 2 * (2 * L + 1) ^ 2 by nra.
  nra.
- (* The bound of the first derivatives. *)
  intros i Hi; split; [exact HC0|]; intros xs Hxs.
  destruct (Hpt xs Hxs) as [HW [HWB [HB1 [HA [Hf1 [_ HE]]]]]].
  rewrite HE.
  have Hq := Hf1 i Hi.
  set (W := gaussian_coordinate_product_weight 1 xs) in *.
  set (B := K * W ^ 2) in *.
  unfold paper_main_head_small_ball_test1.
  set (A := paper_main_weighted_square d c xs - b) in *.
  set (F := paper_main_gaussian_orthogonal_square_first c i xs) in *.
  set (m := INR (S (S k))) in *.
  clearbody A F m.
  rewrite (Rabs_mult (m * A ^ S k) F) (Rabs_mult m (A ^ S k)) -(RPow_abs A (S k)).
  have Hm0 : 0 <= m by lra.
  rewrite (Rabs_pos_eq m Hm0).
  have Hp : Rabs A ^ S k <= B ^ S k.
  { apply pow_incr; split; [apply Rabs_pos|exact HA]. }
  have HBk : B ^ S (S k) = B ^ S k * B by (rewrite /=; ring).
  have HBp : 1 <= B ^ S k by (apply pow_R1_Rle; lra).
  have HP0 : 0 <= Rabs A ^ S k by (apply pow_le; apply Rabs_pos).
  have HD0 : 0 <= Rabs F by apply Rabs_pos.
  rewrite HBk.
  set (P := Rabs A ^ S k) in *.
  set (Q := B ^ S k) in *.
  clearbody P Q.
  have Hstep : m * P * Rabs F <= m * Q * (2 * L * B).
  { apply Rmult_le_compat; try nra. }
  have Hmm : m ^ 2 = m * m by ring.
  have HLL : (2 * L + 1) ^ 2 = (2 * L + 1) * (2 * L + 1) by ring.
  rewrite Hmm HLL.
  have Ha : m <= m * m by nra.
  have Hb : 2 * L <= 2 * ((2 * L + 1) * (2 * L + 1)) by nra.
  have H1 : m * (2 * L) <= 2 * (m * m) * ((2 * L + 1) * (2 * L + 1)).
  { have H0 : 0 <= 2 * L by lra.
    have H4 := Rmult_le_compat m (m * m) (2 * L) (2 * ((2 * L + 1) * (2 * L + 1)))
      Hm0 H0 Ha Hb.
    have H5 : m * m * (2 * ((2 * L + 1) * (2 * L + 1))) =
      2 * (m * m) * ((2 * L + 1) * (2 * L + 1)) by ring.
    lra. }
  have HQB : 0 <= Q * B by nra.
  have H3 := Rmult_le_compat_r (Q * B) _ _ HQB H1.
  have H2 : m * Q * (2 * L * B) = m * (2 * L) * (Q * B) by ring.
  lra.
- (* The bound of the second derivatives. *)
  intros i j Hi Hj; split; [exact HC0|]; intros xs Hxs.
  destruct (Hpt xs Hxs) as [HW [HWB [HB1 [HA [Hf1 [Hf2 HE]]]]]].
  rewrite HE.
  have Hqi := Hf1 i Hi.
  have Hqj := Hf1 j Hj.
  have Hs := Hf2 i j Hi.
  set (W := gaussian_coordinate_product_weight 1 xs) in *.
  set (B := K * W ^ 2) in *.
  unfold paper_main_head_small_ball_test2.
  set (A := paper_main_weighted_square d c xs - b) in *.
  set (Fi := paper_main_gaussian_orthogonal_square_first c i xs) in *.
  set (Fj := paper_main_gaussian_orthogonal_square_first c j xs) in *.
  set (F2 := paper_main_gaussian_orthogonal_square_second c i j xs) in *.
  set (m := INR (S (S k))) in *.
  have Hm1m : INR (S k) <= m by (unfold m; rewrite (S_INR (S k)); lra).
  have Hm10 : 0 <= INR (S k) by apply pos_INR.
  set (m1 := INR (S k)) in *.
  clearbody A Fi Fj F2 m m1.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite (Rabs_mult (m * m1 * A ^ k * Fj) Fi) (Rabs_mult (m * m1 * A ^ k) Fj).
  rewrite (Rabs_mult (m * m1) (A ^ k)) (Rabs_mult m m1) -(RPow_abs A k).
  rewrite (Rabs_mult (m * A ^ S k) F2) (Rabs_mult m (A ^ S k)) -(RPow_abs A (S k)).
  have Hm0 : 0 <= m by lra.
  rewrite (Rabs_pos_eq m Hm0) (Rabs_pos_eq m1 Hm10).
  have Hpk : Rabs A ^ k <= B ^ k by (apply pow_incr; split; [apply Rabs_pos|exact HA]).
  have Hpk1 : Rabs A ^ S k <= B ^ k * B.
  { have -> : B ^ k * B = B ^ S k by (rewrite /=; ring).
    apply pow_incr; split; [apply Rabs_pos|exact HA]. }
  have HB2k : B ^ S (S k) = B ^ k * B * B by (rewrite /=; ring).
  have HBk : 1 <= B ^ k by (apply pow_R1_Rle; lra).
  have HPk0 : 0 <= Rabs A ^ k by (apply pow_le; apply Rabs_pos).
  have HPk10 : 0 <= Rabs A ^ S k by (apply pow_le; apply Rabs_pos).
  have HDi := Rabs_pos Fi.
  have HDj := Rabs_pos Fj.
  have HD2 := Rabs_pos F2.
  rewrite HB2k.
  set (Pk := Rabs A ^ k) in *.
  set (Pk1 := Rabs A ^ S k) in *.
  set (Q := B ^ k) in *.
  clearbody Pk Pk1 Q.
  set (Di := Rabs Fi) in *.
  set (Dj := Rabs Fj) in *.
  set (D2 := Rabs F2) in *.
  clearbody Di Dj D2.
  have Hmm : m ^ 2 = m * m by ring.
  have HLL : (2 * L + 1) ^ 2 = (2 * L + 1) * (2 * L + 1) by ring.
  rewrite Hmm HLL.
  have Ht1 : m * m1 * Pk * Dj * Di <= m * m1 * Q * (2 * L * B) * (2 * L * B).
  { apply Rmult_le_compat; try nra.
    - repeat apply Rmult_le_pos; lra.
    - apply Rmult_le_compat; try (repeat apply Rmult_le_pos; lra).
      apply Rmult_le_compat_l; [repeat apply Rmult_le_pos; lra|exact Hpk]. }
  have Ht2 : m * Pk1 * D2 <= m * (Q * B) * (2 * L).
  { apply Rmult_le_compat; try (repeat apply Rmult_le_pos; lra).
    apply Rmult_le_compat_l; [lra|exact Hpk1]. }
  have HQB : 0 <= Q * B * B by (repeat apply Rmult_le_pos; lra).
  have Hu1 : m * m1 * Q * (2 * L * B) * (2 * L * B) <=
      (m * m) * ((2 * L + 1) * (2 * L + 1)) * (Q * B * B).
  { have E1 : m * m1 * Q * (2 * L * B) * (2 * L * B) =
        (m * m1) * ((2 * L) * (2 * L)) * (Q * B * B) by ring.
    rewrite E1; apply Rmult_le_compat_r; [exact HQB|].
    apply Rmult_le_compat; try (repeat apply Rmult_le_pos; lra).
    apply Rmult_le_compat_l; lra. }
  have Hu2 : m * (Q * B) * (2 * L) <=
      (m * m) * ((2 * L + 1) * (2 * L + 1)) * (Q * B * B).
  { have E2 : m * (Q * B) * (2 * L) = (m * (2 * L)) * (Q * B) by ring.
    have E3 : (m * m) * ((2 * L + 1) * (2 * L + 1)) * (Q * B * B) =
        ((m * m) * ((2 * L + 1) * (2 * L + 1)) * B) * (Q * B) by ring.
    rewrite E2 E3; apply Rmult_le_compat_r; [repeat apply Rmult_le_pos; lra|].
    have Ha : m <= m * m by nra.
    have Hb : 2 * L <= (2 * L + 1) * (2 * L + 1) * B by nra.
    have H0 : 0 <= 2 * L by lra.
    have H4 := Rmult_le_compat m (m * m) (2 * L) ((2 * L + 1) * (2 * L + 1) * B)
      Hm0 H0 Ha Hb.
    have E4 : m * m * ((2 * L + 1) * (2 * L + 1) * B) =
        m * m * ((2 * L + 1) * (2 * L + 1)) * B by ring.
    lra. }
  lra.
Qed.

(* The rotation of the translated quadratic form. *)

Theorem paper_main_head_small_ball_rotation d (H : 'M[R]_d) :
  paper_main_symmetric H ->
  exists (O : nat -> nat -> R) (c : nat -> R),
    paper_main_gaussian_orthonormal_rows d O /\
    (forall xs : list R,
      paper_main_gaussian_quadratic_statistic H xs =
      paper_main_weighted_square d c (gaussian_covariance_image d d O xs)) /\
    finite_sum (fun i => c i ^ 2) (List.seq 0 d) = paper_main_pairing H H /\
    (forall i, (i < d)%coq_nat ->
      Rabs (c i) <= finite_sum (fun j => Rabs (c j)) (List.seq 0 d)) /\
    forall (b : R) (k : nat),
      gaussian_iterated_expectation d
        (fun xs => (paper_main_gaussian_quadratic_statistic H xs - b) ^ S (S k)) =
      gaussian_iterated_expectation d (paper_main_head_small_ball_test d c b k).
Proof.
intros HH.
destruct (paper_main_symmetric_quadratic_list d H HH) as [O [c [HO [Hid [Hfr _]]]]].
set (Lc := finite_sum (fun j => Rabs (c j)) (List.seq 0 d)).
assert (Hc : forall i, (i < d)%coq_nat -> Rabs (c i) <= Lc).
{ intros i Hi; unfold Lc.
  apply (finite_sum_member (fun j => Rabs (c j)) (List.seq 0 d) i).
  - intros j _; apply Rabs_pos.
  - apply in_seq; lia. }
assert (HL : 0 <= Lc).
{ unfold Lc; apply finite_sum_nonnegative; intros j _; apply Rabs_pos. }
assert (Hid' : forall xs, paper_main_gaussian_quadratic_statistic H xs =
    paper_main_weighted_square d c (gaussian_covariance_image d d O xs)).
{ intros xs; exact (Hid xs). }
exists O, c; split; [exact HO|]; split; [exact Hid'|]; split; [exact Hfr|].
split; [exact Hc|].
intros b k.
transitivity (gaussian_iterated_expectation d
  (fun xs => paper_main_head_small_ball_test d c b k (gaussian_covariance_image d d O xs))).
- apply gaussian_iterated_expectation_ext; intros xs _.
  by rewrite /paper_main_head_small_ball_test Hid'.
- exact (paper_main_gaussian_orthogonal_smooth_expectation d O _ _ _ _ _ HO
    (paper_main_head_small_ball_test_smooth d c b Lc k HL Hc)).
Qed.
