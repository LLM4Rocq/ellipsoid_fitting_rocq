(* Linear forms and linear images of the coordinates.
   linear_form d c zs = sum_{k<d} c k * zs_k and linear_image d K c zs is the
   list of the K linear forms with coefficient rows c a. The module proves,
   with explicit constants: continuity of a linear form and of a composite
   g (linear_image d K c zs) for a continuous g; the polynomial bound
   M * d in degree 1 of a linear form whose coefficients are bounded by M;
   the polynomial bound of a composite of a polynomially bounded g, with the
   constant C * (1 + M d)^(r K) and degree r K; the coordinate derivatives of
   a linear form and of a composite; and the derivative in a parameter of a
   composite along coefficients differentiable in that parameter.
   GaussianCovariancePath applies them to the interpolation path
   sqrt t X + sqrt (1 - t) Y and its endpoints, written as linear images.

   This module loads MathComp through AnalysisBridge2, so List.nth, List.map,
   List.seq and %coq_nat are written explicitly; the arithmetic on R is
   Stdlib's, with R_scope opened last. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateBasics GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCoordinateDerivativeDefinitions GaussianFiniteSums
  GaussianCovarianceSums GaussianCovarianceChainRule.
Import ListNotations.
Open Scope R_scope.

Definition linear_form (d : nat) (c : nat -> R) (zs : list R) : R :=
  finite_sum (fun k => c k * List.nth k zs 0) (List.seq 0 d).

Definition linear_image (d K : nat) (c : nat -> nat -> R) (zs : list R) : list R :=
  List.map (fun a => linear_form d (c a) zs) (List.seq 0 K).

Lemma linear_image_length d K c zs : List.length (linear_image d K c zs) = K.
Proof. apply length_map_seq. Qed.

Lemma linear_image_nth d K c zs a :
  (a < K)%coq_nat -> List.nth a (linear_image d K c zs) 0 = linear_form d (c a) zs.
Proof. intros Ha; unfold linear_image; rewrite (nth_map_seq _ _ _ Ha); reflexivity. Qed.

Lemma linear_form_minus d c zs ws :
  linear_form d c zs - linear_form d c ws =
  finite_sum (fun k => c k * (List.nth k zs 0 - List.nth k ws 0)) (List.seq 0 d).
Proof.
  unfold linear_form; rewrite <- finite_sum_minus.
  apply finite_sum_ext; intros k _; ring.
Qed.

(* Derivatives of finite sums. *)
Lemma is_derive_finite_sum (F dF : nat -> R -> R) I (x : R) :
  (forall k, In k I -> @is_derive R R^o R^o x 1 (F k) (dF k x)) ->
  @is_derive R R^o R^o x 1 (fun s => finite_sum (fun k => F k s) I)
    (finite_sum (fun k => dF k x) I).
Proof.
  induction I as [|k I IH]; intros H.
  - simpl; apply is_derive_const.
  - simpl; apply is_derive_plus.
    + apply H; left; reflexivity.
    + apply IH; intros j Hj; apply H; right; exact Hj.
Qed.

Lemma finite_sum_delta d i (v : R) :
  (i < d)%coq_nat ->
  finite_sum (fun k => if Nat.eqb k i then v else 0) (List.seq 0 d) = v.
Proof.
  induction d as [|d IH]; intros Hi; [lia|].
  rewrite finite_sum_seq_S.
  destruct (Nat.eq_dec i d) as [->|Hne].
  - rewrite Nat.eqb_refl.
    assert (H0 : forall k, In k (List.seq 0 d) -> (if Nat.eqb k d then v else 0) = 0).
    { intros k Hk; apply in_seq_lt in Hk.
      destruct (Nat.eqb k d) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity]. }
    rewrite (finite_sum_ext _ _ _ H0) finite_sum_zero; ring.
  - rewrite (IH ltac:(lia)).
    destruct (Nat.eqb d i) eqn:E; [apply Nat.eqb_eq in E; lia|ring].
Qed.

(* Weights. *)
Lemma product_weight_zero zs : gaussian_coordinate_product_weight 0 zs = 1.
Proof.
  induction zs as [|x zs IH]; [reflexivity|].
  simpl; rewrite IH; unfold gaussian_coordinate_weight; simpl; ring.
Qed.

Lemma product_weight_pow p n zs :
  gaussian_coordinate_product_weight p zs ^ n =
  gaussian_coordinate_product_weight (p * n)%coq_nat zs.
Proof.
  induction zs as [|x zs IH]; simpl.
  - apply pow1.
  - rewrite Rpow_mult_distr IH; unfold gaussian_coordinate_weight.
    rewrite -pow_mult; reflexivity.
Qed.

Lemma product_weight_one_pow r zs :
  gaussian_coordinate_product_weight 1 zs ^ r = gaussian_coordinate_product_weight r zs.
Proof. rewrite product_weight_pow Nat.mul_1_l; reflexivity. Qed.

Lemma product_weight_map_seq_le r (h : nat -> R) K B :
  0 <= B ->
  (forall a, (a < K)%coq_nat -> gaussian_coordinate_weight r (h a) <= B) ->
  gaussian_coordinate_product_weight r (List.map h (List.seq 0 K)) <= B ^ K.
Proof.
  intros HB Hh; induction K as [|K IH].
  - simpl; lra.
  - rewrite seq_S map_app gaussian_coordinate_product_weight_append.
    simpl List.map; simpl gaussian_coordinate_product_weight.
    rewrite Rmult_1_r.
    replace (B ^ S K) with (B ^ K * B) by (simpl; ring).
    apply Rmult_le_compat.
    + apply gaussian_coordinate_product_weight_nonnegative.
    + apply gaussian_coordinate_weight_nonnegative.
    + apply IH; intros a Ha; apply Hh; lia.
    + apply Hh; lia.
Qed.

Lemma coordinate_le_weight_one zs k :
  (k < List.length zs)%coq_nat ->
  Rabs (List.nth k zs 0) <= gaussian_coordinate_product_weight 1 zs.
Proof.
  intros Hk.
  pose proof (gaussian_coordinate_product_weight_times_coordinate 0 k zs Hk) as H.
  rewrite product_weight_zero Rmult_1_r in H; exact H.
Qed.

(* Continuity. *)
Lemma linear_form_continuous d c : finite_joint_continuous d (linear_form d c).
Proof.
  unfold linear_form.
  apply finite_joint_continuous_sum; intros k Hk.
  apply finite_joint_continuous_scale.
  apply finite_joint_continuous_nth; apply in_seq_lt; exact Hk.
Qed.

Lemma linear_form_abs_bound d c M zs :
  0 <= M -> (forall k, (k < d)%coq_nat -> Rabs (c k) <= M) -> List.length zs = d ->
  Rabs (linear_form d c zs) <= M * INR d * gaussian_coordinate_product_weight 1 zs.
Proof.
  intros HM Hc Hzs; unfold linear_form.
  eapply Rle_trans.
  { apply (finite_sum_bound _ _ (M * gaussian_coordinate_product_weight 1 zs)).
    intros k Hk; apply in_seq_lt in Hk.
    rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|apply Hc; exact Hk|].
    apply coordinate_le_weight_one; rewrite Hzs; exact Hk. }
  rewrite length_seq; lra.
Qed.

Lemma linear_form_bound d c M :
  0 <= M -> (forall k, (k < d)%coq_nat -> Rabs (c k) <= M) ->
  finite_polynomial_bound d (M * INR d) 1 (linear_form d c).
Proof.
  intros HM Hc; split.
  - apply Rmult_le_pos; [exact HM|apply pos_INR].
  - intros zs Hzs; apply linear_form_abs_bound; assumption.
Qed.

Lemma ratio_lt_one X : 0 <= X -> X / (1 + X) < 1.
Proof.
  intros HX; apply Rmult_lt_reg_r with (1 + X); [lra|].
  unfold Rdiv; rewrite Rmult_assoc Rinv_l; lra.
Qed.

Lemma scaled_delta_lt X df : 0 <= X -> 0 < df -> X * (df / (2 * (1 + X))) < df.
Proof.
  intros HX Hdf.
  replace (X * (df / (2 * (1 + X)))) with ((X / (1 + X)) * (df / 2)) by (field; lra).
  pose proof (Rmult_lt_compat_r (df / 2) _ _ (Rdiv_lt_0_compat _ _ Hdf Rlt_0_2) (ratio_lt_one X HX)).
  lra.
Qed.

Lemma linear_image_continuous_comp d K c (g : list R -> R) :
  finite_joint_continuous K g ->
  finite_joint_continuous d (fun zs => g (linear_image d K c zs)).
Proof.
  intros Hg z eps.
  destruct (finite_matrix_bound c K d) as [M [HM Hc]].
  pose proof (coordinates_to_list_length d z) as Hzs0.
  destruct (Hg (coordinates_of_list K (linear_image d K c (coordinates_to_list d z))) eps)
    as [df Hdf].
  pose proof (Rmult_le_pos M (INR d) HM (pos_INR d)) as HX.
  assert (Hpos : 0 < df / (2 * (1 + M * INR d))).
  { apply Rdiv_lt_0_compat; [apply cond_pos|lra]. }
  exists (mkposreal _ Hpos).
  intros w Hw; cbv beta.
  pose proof (coordinates_to_list_length d w) as Hws.
  pose proof (proj1 (coordinates_close_iff d _ w z) Hw) as Hclose; simpl in Hclose.
  specialize (Hdf (coordinates_of_list K (linear_image d K c (coordinates_to_list d w)))).
  rewrite (coordinates_list_roundtrip _ _ (linear_image_length _ _ _ _)) in Hdf.
  rewrite (coordinates_list_roundtrip _ _ (linear_image_length _ _ _ _)) in Hdf.
  apply Hdf.
  apply (coordinates_close_lists K df _ _ (linear_image_length _ _ _ _)
    (linear_image_length _ _ _ _)).
  intros a Ha.
  rewrite (linear_image_nth _ _ _ _ _ Ha) (linear_image_nth _ _ _ _ _ Ha) linear_form_minus.
  eapply Rle_lt_trans.
  { apply (finite_sum_bound _ _ (M * (df / (2 * (1 + M * INR d))))).
    intros k Hk; apply in_seq_lt in Hk.
    rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos| |].
    - apply Hc; assumption.
    - apply Rlt_le; apply Hclose; exact Hk. }
  rewrite length_seq.
  replace (INR d * (M * (df / (2 * (1 + M * INR d)))))
    with ((M * INR d) * (df / (2 * (1 + M * INR d)))) by ring.
  apply scaled_delta_lt; [exact HX|apply cond_pos].
Qed.

Lemma linear_image_polynomial_bound_comp d K c M (g : list R -> R) C r :
  0 <= M -> (forall a k, (a < K)%coq_nat -> (k < d)%coq_nat -> Rabs (c a k) <= M) ->
  finite_polynomial_bound K C r g ->
  finite_polynomial_bound d (C * (1 + M * INR d) ^ (r * K)%coq_nat) (r * K)%coq_nat
    (fun zs => g (linear_image d K c zs)).
Proof.
  intros HM Hc [HC Hg].
  pose proof (Rmult_le_pos M (INR d) HM (pos_INR d)) as HX.
  split.
  - apply Rmult_le_pos; [exact HC|apply pow_le; lra].
  - intros zs Hzs.
    eapply Rle_trans; [apply Hg; apply linear_image_length|].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact HC|].
    unfold linear_image.
    eapply Rle_trans.
    { apply (product_weight_map_seq_le r (fun a => linear_form d (c a) zs) K
        ((1 + M * INR d) ^ r * gaussian_coordinate_product_weight r zs)).
      - apply Rmult_le_pos; [apply pow_le; lra|apply gaussian_coordinate_product_weight_nonnegative].
      - intros a Ha; unfold gaussian_coordinate_weight.
        rewrite -product_weight_one_pow -Rpow_mult_distr.
        apply pow_incr; split; [pose proof (Rabs_pos (linear_form d (c a) zs)); lra|].
        pose proof (linear_form_abs_bound d (c a) M zs HM (fun k Hk => Hc a k Ha Hk) Hzs).
        pose proof (gaussian_coordinate_product_weight_at_least_one 1 zs).
        nra. }
    rewrite Rpow_mult_distr -pow_mult product_weight_pow.
    apply Rle_refl.
Qed.

Lemma linear_form_coordinate_derivative d c i :
  (i < d)%coq_nat -> finite_coordinate_derivative d i (linear_form d c) (fun _ => c i).
Proof.
  intros Hi zs Hzs; unfold linear_form.
  assert (HiL : (i < List.length zs)%coq_nat) by (rewrite Hzs; exact Hi).
  apply (is_derive_ext (fun s => finite_sum
    (fun k => c k * (if Nat.eqb k i then s else List.nth k zs 0)) (List.seq 0 d))).
  { intros s; apply finite_sum_ext; intros k Hk; f_equal.
    destruct (Nat.eqb k i) eqn:E.
    - apply Nat.eqb_eq in E; subst k.
      rewrite (replace_coordinate_nth_same _ _ _ HiL); reflexivity.
    - apply Nat.eqb_neq in E.
      rewrite (replace_coordinate_nth_other i k _ _ (not_eq_sym E)); reflexivity. }
  rewrite -(finite_sum_delta d i (c i) Hi).
  apply (is_derive_finite_sum
    (fun k s => c k * (if Nat.eqb k i then s else List.nth k zs 0))
    (fun k _ => if Nat.eqb k i then c i else 0)).
  intros k Hk; cbv beta.
  destruct (Nat.eqb k i) eqn:E.
  - apply Nat.eqb_eq in E; subst k.
    pose proof (is_derive_scal (c i) (fun y => y) (List.nth i zs 0) 1 (is_derive_id_R _)) as H.
    rewrite Rmult_1_r in H; exact H.
  - apply is_derive_const.
Qed.

Lemma linear_image_coordinate_derivative_comp d K c i (g : list R -> R)
    (Dg : nat -> list R -> R) :
  (i < d)%coq_nat ->
  (forall a, (a < K)%coq_nat -> finite_coordinate_derivative K a g (Dg a)) ->
  (forall a, (a < K)%coq_nat -> finite_joint_continuous K (Dg a)) ->
  finite_coordinate_derivative d i (fun zs => g (linear_image d K c zs))
    (fun zs => finite_sum (fun a => Dg a (linear_image d K c zs) * c a i) (List.seq 0 K)).
Proof.
  intros Hi HD HC.
  apply (finite_coordinate_derivative_comp d K i g Dg (linear_image d K c)
    (fun a _ => c a i) HD HC).
  - intros zs _; apply linear_image_length.
  - intros a Ha zs Hzs.
    apply (is_derive_ext (fun s => linear_form d (c a) (replace_coordinate i s zs))).
    { intros s; rewrite (linear_image_nth _ _ _ _ _ Ha); reflexivity. }
    exact (linear_form_coordinate_derivative d (c a) i Hi zs Hzs).
Qed.

Lemma linear_image_parameter_derivative d K (c dc : R -> nat -> nat -> R) (t : R)
    (zs : list R) (g : list R -> R) (Dg : nat -> list R -> R) :
  (forall a, (a < K)%coq_nat -> finite_coordinate_derivative K a g (Dg a)) ->
  (forall a, (a < K)%coq_nat -> finite_joint_continuous K (Dg a)) ->
  (forall a k, (a < K)%coq_nat -> (k < d)%coq_nat ->
    @is_derive R R^o R^o t 1 (fun s => c s a k) (dc t a k)) ->
  @is_derive R R^o R^o t 1 (fun s => g (linear_image d K (c s) zs))
    (finite_sum (fun a => Dg a (linear_image d K (c t) zs) * linear_form d (dc t a) zs)
      (List.seq 0 K)).
Proof.
  intros HD HC Hc.
  apply (finite_chain_rule K g Dg (fun s => linear_image d K (c s) zs)
    (fun a => linear_form d (dc t a) zs) t HD HC).
  - intros s; apply linear_image_length.
  - intros a Ha.
    apply (is_derive_ext (fun s => linear_form d (c s a) zs)).
    { intros s; rewrite (linear_image_nth _ _ _ _ _ Ha); reflexivity. }
    unfold linear_form.
    apply (is_derive_finite_sum (fun k s => c s a k * List.nth k zs 0)
      (fun k s => dc s a k * List.nth k zs 0)).
    intros k Hk; apply in_seq_lt in Hk; cbv beta.
    apply is_derive_scal_l; exact (Hc a k Ha Hk).
Qed.
