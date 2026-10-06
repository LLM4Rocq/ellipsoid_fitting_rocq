(* The endpoints of the Gaussian interpolation, and its continuity in time.
   Write Z(t, zs) = gaussian_covariance_path K p q P Q t zs for p + q
   coordinates zs, and E for the iterated Gaussian expectation.
   - gaussian_covariance_endpoint_one and gaussian_covariance_endpoint_zero:
     E f(Z(1)) is the expectation of f(P xi) over the p coordinates of xi,
     and E f(Z(0)) that of f(Q eta) over the q coordinates of eta.
   - gaussian_covariance_path_difference_bound: when f has continuous,
     polynomially bounded partial derivatives Df, the difference
     f(Z(b, zs)) - f(Z(a, zs)) is bounded by a constant times
     |sqrt b - sqrt a| + |sqrt (1-b) - sqrt (1-a)| times a polynomial
     weight of zs.
   - gaussian_covariance_expectation_continuous_within: t |-> E f(Z(t)) is
     continuous within [0, 1] at every point of [0, 1].
   For the endpoints, Z(1, zs) = P (firstn p zs) and Z(0, zs) =
   Q (skipn p zs), and the iterated expectation over p + q coordinates
   integrates the last q coordinates first
   (gaussian_iterated_suffix_expectation). The difference bound applies
   the mean value theorem along the segment from Z(a, zs) to Z(b, zs).
   Continuity then follows from
   gaussian_iterated_expectation_continuous_modulus_within, with this
   bound as modulus. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianLastDefinitions GaussianLastIntegration GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinateDerivativeDefinitions GaussianExpectationContinuity
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCovariancePath GaussianCovarianceDomains.
Import ListNotations.
Open Scope R_scope.

Lemma firstn_app_exact (xs ys : list R) :
  List.firstn (List.length xs) (xs ++ ys)%list = xs.
Proof. induction xs as [|x xs IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma skipn_app_exact (xs ys : list R) :
  List.skipn (List.length xs) (xs ++ ys)%list = ys.
Proof. induction xs as [|x xs IH]; simpl; [reflexivity|exact IH]. Qed.

(* The endpoint values. *)
Theorem gaussian_covariance_endpoint_one K p q P Q (f : list R -> R) :
  gaussian_iterated_expectation (p + q)%coq_nat
    (fun zs => f (gaussian_covariance_path K p q P Q 1 zs)) =
  gaussian_iterated_expectation p (fun xs => f (gaussian_covariance_image K p P xs)).
Proof.
  assert (H1 : forall zs, List.length zs = (p + q)%coq_nat ->
    f (gaussian_covariance_path K p q P Q 1 zs) =
    f (gaussian_covariance_image K p P (List.firstn p zs))).
  { intros zs _; rewrite gaussian_covariance_path_one; reflexivity. }
  rewrite (gaussian_iterated_expectation_ext _ _ _ H1).
  rewrite gaussian_iterated_suffix_expectation.
  apply gaussian_iterated_expectation_ext; intros xs Hxs.
  unfold gaussian_suffix_marginal.
  assert (H2 : forall ys, List.length ys = q ->
    f (gaussian_covariance_image K p P (List.firstn p (xs ++ ys)%list)) =
    f (gaussian_covariance_image K p P xs)).
  { intros ys _; rewrite <- Hxs; rewrite firstn_app_exact; reflexivity. }
  rewrite (gaussian_iterated_expectation_ext _ _ _ H2).
  exact (proj2 (gaussian_iterated_constant q _)).
Qed.

Theorem gaussian_covariance_endpoint_zero K p q P Q (f : list R -> R) :
  gaussian_iterated_expectation (p + q)%coq_nat
    (fun zs => f (gaussian_covariance_path K p q P Q 0 zs)) =
  gaussian_iterated_expectation q (fun ys => f (gaussian_covariance_image K q Q ys)).
Proof.
  assert (H1 : forall zs, List.length zs = (p + q)%coq_nat ->
    f (gaussian_covariance_path K p q P Q 0 zs) =
    f (gaussian_covariance_image K q Q (List.skipn p zs))).
  { intros zs _; rewrite gaussian_covariance_path_zero; reflexivity. }
  rewrite (gaussian_iterated_expectation_ext _ _ _ H1).
  rewrite gaussian_iterated_suffix_expectation.
  transitivity (gaussian_iterated_expectation p
    (fun _ => gaussian_iterated_expectation q (fun ys => f (gaussian_covariance_image K q Q ys)))).
  - apply gaussian_iterated_expectation_ext; intros xs Hxs.
    unfold gaussian_suffix_marginal.
    apply gaussian_iterated_expectation_ext; intros ys _.
    rewrite <- Hxs; rewrite skipn_app_exact; reflexivity.
  - exact (proj2 (gaussian_iterated_constant p _)).
Qed.

(* The difference of the path values along the segment. *)
Lemma gaussian_covariance_coef_difference_bound p q P Q M a b c k :
  0 <= M -> (k < (p + q)%coq_nat)%coq_nat ->
  (forall k, (k < p)%coq_nat -> Rabs (P c k) <= M) ->
  (forall k, (k < q)%coq_nat -> Rabs (Q c k) <= M) ->
  Rabs (gaussian_covariance_coef p q P Q b c k - gaussian_covariance_coef p q P Q a c k) <=
  M * (Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a))).
Proof.
  intros HM Hk HP HQ; unfold gaussian_covariance_coef.
  pose proof (Rabs_pos (sqrt b - sqrt a)); pose proof (Rabs_pos (sqrt (1 - b) - sqrt (1 - a))).
  destruct (Nat.ltb k p) eqn:E.
  - apply Nat.ltb_lt in E.
    replace (sqrt b * P c k - sqrt a * P c k) with ((sqrt b - sqrt a) * P c k) by ring.
    rewrite Rabs_mult.
    pose proof (HP k E); pose proof (Rabs_pos (P c k)); nra.
  - apply Nat.ltb_ge in E.
    replace (sqrt (1 - b) * Q c (k - p)%coq_nat - sqrt (1 - a) * Q c (k - p)%coq_nat)
      with ((sqrt (1 - b) - sqrt (1 - a)) * Q c (k - p)%coq_nat) by ring.
    rewrite Rabs_mult.
    pose proof (HQ (k - p)%coq_nat ltac:(lia)); pose proof (Rabs_pos (Q c (k - p)%coq_nat)); nra.
Qed.

Lemma gaussian_covariance_segment_coef_bound p q P Q M a b xi c k :
  0 <= M -> 0 <= a <= 1 -> 0 <= b <= 1 -> 0 <= xi <= 1 -> (k < (p + q)%coq_nat)%coq_nat ->
  (forall k, (k < p)%coq_nat -> Rabs (P c k) <= M) ->
  (forall k, (k < q)%coq_nat -> Rabs (Q c k) <= M) ->
  Rabs (gaussian_covariance_coef p q P Q a c k +
    xi * (gaussian_covariance_coef p q P Q b c k - gaussian_covariance_coef p q P Q a c k)) <= M.
Proof.
  intros HM Ha Hb Hxi Hk HP HQ.
  pose proof (gaussian_covariance_coef_bound p q P Q M a c k Ha Hk HP HQ) as H1.
  pose proof (gaussian_covariance_coef_bound p q P Q M b c k Hb Hk HP HQ) as H2.
  replace (gaussian_covariance_coef p q P Q a c k +
    xi * (gaussian_covariance_coef p q P Q b c k - gaussian_covariance_coef p q P Q a c k))
    with ((1 - xi) * gaussian_covariance_coef p q P Q a c k +
      xi * gaussian_covariance_coef p q P Q b c k) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite !Rabs_mult (Rabs_right (1 - xi) ltac:(lra)) (Rabs_right xi ltac:(lra)).
  nra.
Qed.

Theorem gaussian_covariance_path_difference_bound K p q P Q M (f : list R -> R)
    (Df : nat -> list R -> R) C r a b zs :
  0 <= M ->
  (forall c k, (c < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P c k) <= M) ->
  (forall c k, (c < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q c k) <= M) ->
  0 <= a <= 1 -> 0 <= b <= 1 -> List.length zs = (p + q)%coq_nat ->
  (forall c, (c < K)%coq_nat -> finite_coordinate_derivative K c f (Df c)) ->
  (forall c, (c < K)%coq_nat -> finite_joint_continuous K (Df c)) ->
  (forall c, (c < K)%coq_nat -> finite_polynomial_bound K C r (Df c)) ->
  Rabs (f (gaussian_covariance_path K p q P Q b zs) - f (gaussian_covariance_path K p q P Q a zs)) <=
  INR K * (C * (1 + M * INR (p + q)%coq_nat) ^ (r * K)%coq_nat) * (M * INR (p + q)%coq_nat)
    * (Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a)))
    * gaussian_coordinate_product_weight ((r * K)%coq_nat + 1)%coq_nat zs.
Proof.
  intros HM HP HQ Ha Hb Hzs HD HC HDb.
  set (ca := gaussian_covariance_coef p q P Q a).
  set (cb := gaussian_covariance_coef p q P Q b).
  set (cs := fun (s : R) (c k : nat) => ca c k + s * (cb c k - ca c k)).
  set (dcs := fun (c k : nat) => cb c k - ca c k).
  set (u := fun s => linear_image (p + q)%coq_nat K (cs s) zs).
  set (delta := Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a))).
  assert (Hdelta : 0 <= delta).
  { unfold delta; pose proof (Rabs_pos (sqrt b - sqrt a));
    pose proof (Rabs_pos (sqrt (1 - b) - sqrt (1 - a))); lra. }
  assert (Hg : forall s, @is_derive R R^o R^o s 1 (fun s => f (u s))
    (finite_sum (fun c => Df c (u s) * linear_form (p + q)%coq_nat (dcs c) zs) (List.seq 0 K))).
  { intros s.
    apply (linear_image_parameter_derivative (p + q)%coq_nat K cs (fun _ => dcs) s zs f Df HD HC).
    intros c k Hc Hk; unfold cs, dcs.
    pose proof (is_derive_plus (fun _ => ca c k) (fun s' => s' * (cb c k - ca c k)) s
      0 (1 * (cb c k - ca c k)) (is_derive_const _ _)
      (is_derive_scal_l (cb c k - ca c k) (fun y => y) s 1 (is_derive_id_R s))) as H.
    rewrite Rplus_0_l Rmult_1_l in H; exact H. }
  destruct (MVT_Reals (fun s => f (u s))
    (fun s => finite_sum (fun c => Df c (u s) * linear_form (p + q)%coq_nat (dcs c) zs)
      (List.seq 0 K)) 0 1 Rlt_0_1 (fun x _ => Hg x)
    (fun x _ => is_derive_continuity_pt _ _ _ (Hg x))) as [xi [Hxi Hmvt]].
  assert (Hu1 : u 1 = gaussian_covariance_path K p q P Q b zs).
  { unfold u; rewrite gaussian_covariance_path_linear; unfold linear_image.
    apply map_ext; intros c; unfold linear_form; apply finite_sum_ext; intros k _.
    unfold cs, ca, cb; ring. }
  assert (Hu0 : u 0 = gaussian_covariance_path K p q P Q a zs).
  { unfold u; rewrite gaussian_covariance_path_linear; unfold linear_image.
    apply map_ext; intros c; unfold linear_form; apply finite_sum_ext; intros k _.
    unfold cs, ca, cb; ring. }
  rewrite <- Hu1; rewrite <- Hu0; rewrite Hmvt Rminus_0_r Rmult_1_r.
  assert (Hcs : forall c k, (c < K)%coq_nat -> (k < (p + q)%coq_nat)%coq_nat -> Rabs (cs xi c k) <= M).
  { intros c k Hc Hk; unfold cs, ca, cb.
    apply (gaussian_covariance_segment_coef_bound p q P Q M a b xi c k HM Ha Hb
      ltac:(lra) Hk (fun j Hj => HP c j Hc Hj) (fun j Hj => HQ c j Hc Hj)). }
  assert (Hdcs : forall c k, (c < K)%coq_nat -> (k < (p + q)%coq_nat)%coq_nat ->
    Rabs (dcs c k) <= M * delta).
  { intros c k Hc Hk; unfold dcs, ca, cb, delta.
    apply (gaussian_covariance_coef_difference_bound p q P Q M a b c k HM Hk
      (fun j Hj => HP c j Hc Hj) (fun j Hj => HQ c j Hc Hj)). }
  eapply Rle_trans.
  { apply (finite_sum_bound _ _ ((C * (1 + M * INR (p + q)%coq_nat) ^ (r * K)%coq_nat *
      gaussian_coordinate_product_weight (r * K)%coq_nat zs) *
      (M * delta * INR (p + q)%coq_nat * gaussian_coordinate_product_weight 1 zs))).
    intros c Hc; apply in_seq_lt in Hc.
    rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos| |].
    - destruct (linear_image_polynomial_bound_comp (p + q)%coq_nat K (cs xi) M (Df c) C r HM
        Hcs (HDb c Hc)) as [_ Hpb].
      apply Hpb; exact Hzs.
    - apply linear_form_abs_bound; [apply Rmult_le_pos; assumption| |exact Hzs].
      intros k Hk; apply Hdcs; assumption. }
  rewrite length_seq.
  rewrite (gaussian_coordinate_product_weight_degree_add (r * K)%coq_nat 1 zs).
  apply Req_le; unfold delta; ring.
Qed.

(* The modulus is continuous at a and vanishes there. *)
Lemma gaussian_covariance_modulus_continuous (Cm a : R) :
  0 <= a <= 1 ->
  {for a, continuous (fun b => Cm * (Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a))))}.
Proof.
  intros Ha; apply continuous_Reals; intros eps Heps.
  pose proof (Rabs_pos Cm) as HC.
  assert (Hpos : 0 < eps / (2 * (Rabs Cm + 1))).
  { apply Rdiv_lt_0_compat; [exact Heps|lra]. }
  destruct (proj1 (continuous_Reals sqrt a) (continuous_Rsqrt a (proj1 Ha)) _ Hpos)
    as [d1 [Hd1 H1]].
  destruct (proj1 (continuous_Reals sqrt (1 - a)) (continuous_Rsqrt (1 - a) ltac:(lra)) _ Hpos)
    as [d2 [Hd2 H2]].
  exists (Rmin d1 d2); split; [apply Rmin_pos; assumption|].
  intros b Hb.
  assert (Hb1 : Rabs (sqrt b - sqrt a) < eps / (2 * (Rabs Cm + 1))).
  { apply H1; eapply Rlt_le_trans; [exact Hb|apply Rmin_l]. }
  assert (Hb2 : Rabs (sqrt (1 - b) - sqrt (1 - a)) < eps / (2 * (Rabs Cm + 1))).
  { apply H2; replace (1 - b - (1 - a)) with (- (b - a)) by ring.
    rewrite Rabs_Ropp; eapply Rlt_le_trans; [exact Hb|apply Rmin_r]. }
  rewrite !Rminus_diag !Rabs_R0 Rplus_0_r Rmult_0_r Rminus_0_r.
  rewrite Rabs_mult (Rabs_right (Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a)))
    ltac:(pose proof (Rabs_pos (sqrt b - sqrt a));
          pose proof (Rabs_pos (sqrt (1 - b) - sqrt (1 - a))); lra)).
  apply Rle_lt_trans with (Rabs Cm * (eps / (Rabs Cm + 1))).
  - apply Rmult_le_compat_l; [exact HC|].
    apply Rle_trans with (eps / (2 * (Rabs Cm + 1)) + eps / (2 * (Rabs Cm + 1))); [lra|].
    apply Req_le; field; lra.
  - replace (Rabs Cm * (eps / (Rabs Cm + 1))) with ((Rabs Cm / (1 + Rabs Cm)) * eps) by (field; lra).
    pose proof (Rmult_lt_compat_r eps _ _ Heps (ratio_lt_one (Rabs Cm) HC)) as H.
    rewrite Rmult_1_l in H; exact H.
Qed.

(* Continuity of t |-> E f(Z(t)) within [0, 1] at every a of [0, 1]. *)
Theorem gaussian_covariance_expectation_continuous_within K p q P Q (f : list R -> R)
    (Df : nat -> list R -> R) C r a :
  0 <= a <= 1 ->
  finite_joint_continuous K f ->
  (forall c, (c < K)%coq_nat -> finite_coordinate_derivative K c f (Df c)) ->
  (forall c, (c < K)%coq_nat -> finite_joint_continuous K (Df c)) ->
  finite_polynomial_bound K C r f ->
  (forall c, (c < K)%coq_nat -> finite_polynomial_bound K C r (Df c)) ->
  ((fun t => gaussian_iterated_expectation (p + q)%coq_nat
      (fun zs => f (gaussian_covariance_path K p q P Q t zs)))
    @ within (fun t : R => 0 <= t <= 1) (nbhs a) -->
   gaussian_iterated_expectation (p + q)%coq_nat
     (fun zs => f (gaussian_covariance_path K p q P Q a zs)))%classic.
Proof.
  intros Ha Hf HD HC Hfb HDb.
  destruct (gaussian_covariance_matrix_bound K p q P Q) as [M [HM [HP HQ]]].
  pose proof (Rmult_le_pos M (INR (p + q)%coq_nat) HM (pos_INR _)) as HX.
  set (Cm := INR K * (C * (1 + M * INR (p + q)%coq_nat) ^ (r * K)%coq_nat) *
    (M * INR (p + q)%coq_nat)).
  assert (HCm : 0 <= Cm).
  { unfold Cm; apply Rmult_le_pos; [|exact HX].
    apply Rmult_le_pos; [apply pos_INR|].
    apply Rmult_le_pos; [exact (proj1 Hfb)|apply pow_le; lra]. }
  assert (H1 : finite_polynomial_bound (p + q)%coq_nat
    (C * (1 + M * INR (p + q)%coq_nat) ^ (r * K)%coq_nat) (r * K)%coq_nat
    (fun zs => f (gaussian_covariance_path K p q P Q a zs))).
  { exact (proj2 (gaussian_covariance_path_regular K p q P Q M f C r a Ha HM HP HQ Hf Hfb)). }
  assert (H2 : exists eta, 0 < eta /\ forall b, 0 <= b <= 1 -> Rabs (b - a) < eta ->
    finite_joint_continuous (p + q)%coq_nat
      (fun zs => f (gaussian_covariance_path K p q P Q b zs))).
  { exists 1; split; [lra|]; intros b Hb _.
    exact (proj1 (gaussian_covariance_path_regular K p q P Q M f C r b Hb HM HP HQ Hf Hfb)). }
  assert (H3 : {for a, continuous (fun b =>
    Cm * (Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a))))}).
  { apply gaussian_covariance_modulus_continuous; exact Ha. }
  assert (H4 : Cm * (Rabs (sqrt a - sqrt a) + Rabs (sqrt (1 - a) - sqrt (1 - a))) = 0).
  { rewrite !Rminus_diag !Rabs_R0; ring. }
  assert (H5 : exists eta, 0 < eta /\ forall b, 0 <= b <= 1 -> Rabs (b - a) < eta ->
    finite_polynomial_bound (p + q)%coq_nat
      (Cm * (Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a))))
      ((r * K)%coq_nat + 1)%coq_nat
      (fun zs => f (gaussian_covariance_path K p q P Q b zs) -
        f (gaussian_covariance_path K p q P Q a zs))).
  { exists 1; split; [lra|]; intros b Hb _.
    split.
    + apply Rmult_le_pos; [exact HCm|].
      pose proof (Rabs_pos (sqrt b - sqrt a)); pose proof (Rabs_pos (sqrt (1 - b) - sqrt (1 - a))); lra.
    + intros zs Hzs.
      eapply Rle_trans.
      { apply (gaussian_covariance_path_difference_bound K p q P Q M f Df C r a b zs HM HP HQ
          Ha Hb Hzs HD HC HDb). }
      apply Req_le; unfold Cm; ring. }
  exact (proj1 (gaussian_iterated_expectation_continuous_modulus_within (p + q)%coq_nat
    (fun t zs => f (gaussian_covariance_path K p q P Q t zs)) (fun t : R => 0 <= t <= 1) a
    (C * (1 + M * INR (p + q)%coq_nat) ^ (r * K)%coq_nat) (r * K)%coq_nat
    ((r * K)%coq_nat + 1)%coq_nat
    (fun b => Cm * (Rabs (sqrt b - sqrt a) + Rabs (sqrt (1 - b) - sqrt (1 - a))))
    Ha H1 H2 H3 H4 H5)).
Qed.
