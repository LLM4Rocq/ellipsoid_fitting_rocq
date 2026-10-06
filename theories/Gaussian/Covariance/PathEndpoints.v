(* The Gaussian interpolation path as a function of time. Write
   Z(t, zs) = gaussian_covariance_path K p q P Q t zs for p + q coordinates
   zs, with the entries of P and Q bounded by M.
   - gaussian_covariance_coef_difference_bound and
     gaussian_covariance_segment_coef_bound: the coefficients of
     Z(b) - Z(a) are bounded by M (|sqrt b - sqrt a| + |sqrt (1-b) -
     sqrt (1-a)|), and those of the points of the segment from Z(a) to Z(b)
     by M, for a and b in [0, 1].
   - gaussian_covariance_path_difference_bound: when f has continuous,
     polynomially bounded partial derivatives Df, the difference
     f(Z(b, zs)) - f(Z(a, zs)) is bounded by a constant times
     |sqrt b - sqrt a| + |sqrt (1-b) - sqrt (1-a)| times a polynomial
     weight of zs. The proof applies the mean value theorem along the
     segment from Z(a, zs) to Z(b, zs).
   - gaussian_covariance_modulus_continuous: this modulus is continuous in
     b at every a in [0, 1].
   firstn_app_exact and skipn_app_exact split a concatenation of lists at
   the length of its first part. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Gaussian.Iterated.SuffixMarginalDefinitions Gaussian.Iterated.LastIntegration
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gaussian.Coordinate.Weights
  Gaussian.Coordinate.DerivativeDefinitions
  Gaussian.Iterated.ParameterContinuity Gaussian.Covariance.Definitions
  Analysis.FiniteSumAlgebra Gaussian.Covariance.LinearImages
  Gaussian.Covariance.InterpolationCoefficients
  Gaussian.Covariance.PathDomains.
Import ListNotations.
Open Scope R_scope.

Lemma firstn_app_exact (xs ys : list R) :
  List.firstn (List.length xs) (xs ++ ys)%list = xs.
Proof. induction xs as [|x xs IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma skipn_app_exact (xs ys : list R) :
  List.skipn (List.length xs) (xs ++ ys)%list = ys.
Proof. induction xs as [|x xs IH]; simpl; [reflexivity|exact IH]. Qed.

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
