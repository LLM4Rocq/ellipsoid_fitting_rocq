(* The Gaussian interpolation path gaussian_covariance_path as a linear image
   with coefficients that depend on t. For zs of any length, entry a of
   gaussian_covariance_path K p q P Q t zs is sum_{k<p+q} coef t a k * zs_k,
   with coef t a k = sqrt t * P a k for k < p and sqrt (1-t) * Q a (k-p) for
   k >= p (gaussian_covariance_path_linear, an equality of functions). At
   t = 1 and t = 0 the path is the image of the first p and of the last q
   coordinates. The coefficients are bounded by the entries of P and Q for t
   in [0,1], twice differentiable in t on (0,1) with explicit derivatives,
   and these derivatives are bounded on [lo, hi] when 0 < lo and hi < 1.
   gaussian_covariance_stein_coefficients: for 0 < t < 1,
     sum_k dcoef t a k * coef t b k = (1/2) ((P P^T)_ab - (Q Q^T)_ab),
   the identity that turns the Stein terms into the covariance difference. *)
From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceDefinitions
  GaussianCovarianceSums GaussianCovarianceLinear.
Import ListNotations.
Open Scope R_scope.

Definition gaussian_covariance_coef (p q : nat) (P Q : nat -> nat -> R) (t : R)
    (a k : nat) : R :=
  if Nat.ltb k p then sqrt t * P a k else sqrt (1 - t) * Q a (k - p)%coq_nat.

Definition gaussian_covariance_dcoef (p q : nat) (P Q : nat -> nat -> R) (t : R)
    (a k : nat) : R :=
  if Nat.ltb k p then P a k / (2 * sqrt t) else - Q a (k - p)%coq_nat / (2 * sqrt (1 - t)).

Definition gaussian_covariance_ddcoef (p q : nat) (P Q : nat -> nat -> R) (t : R)
    (a k : nat) : R :=
  if Nat.ltb k p then - P a k / (4 * (sqrt t * sqrt t * sqrt t))
  else - Q a (k - p)%coq_nat / (4 * (sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t))).

Lemma gaussian_covariance_image_linear K p P :
  gaussian_covariance_image K p P = linear_image p K P.
Proof. reflexivity. Qed.

Lemma gaussian_covariance_path_linear K p q P Q t :
  gaussian_covariance_path K p q P Q t =
  linear_image (p + q)%coq_nat K (gaussian_covariance_coef p q P Q t).
Proof.
  apply functional_extensionality; intros zs.
  unfold gaussian_covariance_path, linear_image.
  apply map_ext; intros a.
  unfold linear_form, gaussian_covariance_row, gaussian_covariance_coef.
  rewrite finite_sum_seq_split.
  rewrite <- (finite_sum_scale (sqrt t)), <- (finite_sum_scale (sqrt (1 - t))).
  f_equal.
  - apply finite_sum_ext; intros k Hk; apply in_seq_lt in Hk.
    destruct (Nat.ltb k p) eqn:E; [|apply Nat.ltb_ge in E; lia].
    rewrite (nth_firstn_lt _ _ _ Hk); ring.
  - apply finite_sum_ext; intros k Hk; apply in_seq_lt in Hk.
    destruct (Nat.ltb (p + k)%coq_nat p) eqn:E; [apply Nat.ltb_lt in E; lia|].
    replace ((p + k)%coq_nat - p)%coq_nat with k by lia.
    rewrite nth_skipn_add; ring.
Qed.

(* Bounds of the coefficients on [0, 1]. *)
Lemma sqrt_le_one t : 0 <= t <= 1 -> 0 <= sqrt t <= 1.
Proof.
  intros [H0 H1]; split; [apply sqrt_pos|].
  rewrite <- sqrt_1; apply sqrt_le_1_alt; exact H1.
Qed.

Lemma gaussian_covariance_coef_bound p q P Q M t a k :
  0 <= t <= 1 -> (k < (p + q)%coq_nat)%coq_nat ->
  (forall k, (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall k, (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  Rabs (gaussian_covariance_coef p q P Q t a k) <= M.
Proof.
  intros Ht Hk HP HQ; unfold gaussian_covariance_coef.
  destruct (Nat.ltb k p) eqn:E.
  - apply Nat.ltb_lt in E.
    rewrite Rabs_mult (Rabs_right (sqrt t) (Rle_ge _ _ (sqrt_pos t))).
    pose proof (sqrt_le_one t Ht); pose proof (HP k E); pose proof (Rabs_pos (P a k)); nra.
  - apply Nat.ltb_ge in E.
    rewrite Rabs_mult (Rabs_right (sqrt (1 - t)) (Rle_ge _ _ (sqrt_pos (1 - t)))).
    assert (H1t : 0 <= 1 - t <= 1) by lra.
    pose proof (sqrt_le_one (1 - t) H1t); pose proof (HQ (k - p)%coq_nat ltac:(lia)).
    pose proof (Rabs_pos (Q a (k - p)%coq_nat)); nra.
Qed.

(* Derivatives of the coefficients in t, for 0 < t < 1. *)
Lemma is_derive_sqrt_id t : 0 < t -> @is_derive R R^o R^o t 1 sqrt (1 / (2 * sqrt t)).
Proof.
  intros Ht.
  apply (is_derive_ext (fun y => sqrt ((fun y => y) y))); [reflexivity|].
  apply is_derive_sqrt; [apply is_derive_id_R|exact Ht].
Qed.

(* field, then the nonzero side conditions from strict positivity. *)
Ltac field_nz := field; repeat split; try (apply Rgt_not_eq; lra).

Lemma is_derive_sqrt_complement t :
  t < 1 -> @is_derive R R^o R^o t 1 (fun y => sqrt (1 - y)) (- 1 / (2 * sqrt (1 - t))).
Proof.
  intros Ht.
  assert (Hs : 0 < sqrt (1 - t)) by (apply sqrt_lt_R0; lra).
  pose proof (is_derive_sqrt (fun y => 1 - y) t (0 - 1)
    (is_derive_minus _ _ _ _ _ (is_derive_const 1 t) (is_derive_id_R t)) ltac:(lra)) as H.
  cbv beta in H.
  replace (- 1 / (2 * sqrt (1 - t))) with ((0 - 1) / (2 * sqrt (1 - t))); [exact H|].
  field_nz.
Qed.

Lemma gaussian_covariance_coef_derive p q P Q t a k :
  0 < t < 1 ->
  @is_derive R R^o R^o t 1 (fun s => gaussian_covariance_coef p q P Q s a k)
    (gaussian_covariance_dcoef p q P Q t a k).
Proof.
  intros Ht; unfold gaussian_covariance_coef, gaussian_covariance_dcoef.
  assert (Hst : 0 < sqrt t) by (apply sqrt_lt_R0; lra).
  assert (Hs1 : 0 < sqrt (1 - t)) by (apply sqrt_lt_R0; lra).
  destruct (Nat.ltb k p).
  - replace (P a k / (2 * sqrt t)) with (1 / (2 * sqrt t) * P a k) by field_nz.
    apply is_derive_scal_l; apply is_derive_sqrt_id; lra.
  - replace (- Q a (k - p)%coq_nat / (2 * sqrt (1 - t)))
      with (- 1 / (2 * sqrt (1 - t)) * Q a (k - p)%coq_nat) by field_nz.
    apply is_derive_scal_l; apply is_derive_sqrt_complement; lra.
Qed.

Lemma gaussian_covariance_dcoef_derive p q P Q t a k :
  0 < t < 1 ->
  @is_derive R R^o R^o t 1 (fun s => gaussian_covariance_dcoef p q P Q s a k)
    (gaussian_covariance_ddcoef p q P Q t a k).
Proof.
  intros Ht; unfold gaussian_covariance_dcoef, gaussian_covariance_ddcoef.
  assert (Hst : 0 < sqrt t) by (apply sqrt_lt_R0; lra).
  assert (Hs1 : 0 < sqrt (1 - t)) by (apply sqrt_lt_R0; lra).
  pose proof (sqrt_sqrt t ltac:(lra)) as Hsq.
  pose proof (sqrt_sqrt (1 - t) ltac:(lra)) as Hsq1.
  destruct (Nat.ltb k p).
  - apply (is_derive_ext (fun s => P a k * / (2 * sqrt s))).
    { intros s; unfold Rdiv; ring. }
    replace (- P a k / (4 * (sqrt t * sqrt t * sqrt t)))
      with (P a k * (- (2 * (1 / (2 * sqrt t))) / (2 * sqrt t) ^ 2)).
    2:{ field_nz. }
    apply is_derive_scal.
    apply (is_derive_inv (fun y => 2 * sqrt y) t (2 * (1 / (2 * sqrt t)))).
    + apply (is_derive_scal 2 sqrt t (1 / (2 * sqrt t))); apply is_derive_sqrt_id; lra.
    + apply Rgt_not_eq; lra.
  - apply (is_derive_ext (fun s => - Q a (k - p)%coq_nat * / (2 * sqrt (1 - s)))).
    { intros s; unfold Rdiv; ring. }
    replace (- Q a (k - p)%coq_nat / (4 * (sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t))))
      with (- Q a (k - p)%coq_nat * (- (2 * (- 1 / (2 * sqrt (1 - t)))) / (2 * sqrt (1 - t)) ^ 2)).
    2:{ field_nz. }
    apply is_derive_scal.
    apply (is_derive_inv (fun y => 2 * sqrt (1 - y)) t (2 * (- 1 / (2 * sqrt (1 - t))))).
    + apply (is_derive_scal 2 (fun y => sqrt (1 - y)) t (- 1 / (2 * sqrt (1 - t)))).
      apply is_derive_sqrt_complement; lra.
    + apply Rgt_not_eq; lra.
Qed.

(* Bounds of the derivatives on [lo, hi], 0 < lo, hi < 1. *)
Lemma inv_sqrt_bound lo t : 0 < lo -> lo <= t -> / sqrt t <= / sqrt lo.
Proof.
  intros Hlo Ht.
  apply Rinv_le_contravar; [apply sqrt_lt_R0; exact Hlo|apply sqrt_le_1_alt; exact Ht].
Qed.

Lemma gaussian_covariance_dcoef_bound p q P Q M lo hi t a k :
  0 <= M -> 0 < lo -> hi < 1 -> lo <= t <= hi -> (k < (p + q)%coq_nat)%coq_nat ->
  (forall k, (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall k, (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  Rabs (gaussian_covariance_dcoef p q P Q t a k) <=
  M * (/ (2 * sqrt lo) + / (2 * sqrt (1 - hi))).
Proof.
  intros HM Hlo Hhi Ht Hk HP HQ; unfold gaussian_covariance_dcoef.
  assert (Hslo : 0 < sqrt lo) by (apply sqrt_lt_R0; exact Hlo).
  assert (Hshi : 0 < sqrt (1 - hi)) by (apply sqrt_lt_R0; lra).
  assert (Hst : 0 < sqrt t) by (apply sqrt_lt_R0; lra).
  assert (Hs1 : 0 < sqrt (1 - t)) by (apply sqrt_lt_R0; lra).
  assert (Hpos1 : 0 <= / (2 * sqrt lo)) by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
  assert (Hpos2 : 0 <= / (2 * sqrt (1 - hi))) by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
  destruct (Nat.ltb k p) eqn:E.
  - apply Nat.ltb_lt in E.
    unfold Rdiv; rewrite Rabs_mult (Rabs_right (/ (2 * sqrt t))
      (Rle_ge _ _ (Rlt_le _ _ (Rinv_0_lt_compat (2 * sqrt t) ltac:(lra))))).
    assert (Hi : / (2 * sqrt t) <= / (2 * sqrt lo)).
    { rewrite (Rinv_mult 2 (sqrt t)) (Rinv_mult 2 (sqrt lo)).
      apply Rmult_le_compat_l; [apply Rlt_le; apply Rinv_0_lt_compat; lra|apply inv_sqrt_bound; lra]. }
    pose proof (HP k E); pose proof (Rabs_pos (P a k)).
    assert (Hit : 0 <= / (2 * sqrt t)) by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
    apply Rle_trans with (M * / (2 * sqrt lo)); [apply Rmult_le_compat; lra|].
    apply Rmult_le_compat_l; lra.
  - apply Nat.ltb_ge in E.
    unfold Rdiv; rewrite Rabs_mult Rabs_Ropp (Rabs_right (/ (2 * sqrt (1 - t)))
      (Rle_ge _ _ (Rlt_le _ _ (Rinv_0_lt_compat (2 * sqrt (1 - t)) ltac:(lra))))).
    assert (Hi : / (2 * sqrt (1 - t)) <= / (2 * sqrt (1 - hi))).
    { rewrite (Rinv_mult 2 (sqrt (1 - t))) (Rinv_mult 2 (sqrt (1 - hi))).
      apply Rmult_le_compat_l; [apply Rlt_le; apply Rinv_0_lt_compat; lra|apply inv_sqrt_bound; lra]. }
    pose proof (HQ (k - p)%coq_nat ltac:(lia)); pose proof (Rabs_pos (Q a (k - p)%coq_nat)).
    assert (Hit : 0 <= / (2 * sqrt (1 - t))) by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
    apply Rle_trans with (M * / (2 * sqrt (1 - hi))); [apply Rmult_le_compat; lra|].
    apply Rmult_le_compat_l; lra.
Qed.

Lemma inv_cube_sqrt_bound lo t :
  0 < lo -> lo <= t -> / (sqrt t * sqrt t * sqrt t) <= / (sqrt lo * sqrt lo * sqrt lo).
Proof.
  intros Hlo Ht.
  assert (Hslo : 0 < sqrt lo) by (apply sqrt_lt_R0; exact Hlo).
  assert (Hle : sqrt lo <= sqrt t) by (apply sqrt_le_1_alt; exact Ht).
  apply Rinv_le_contravar; [apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption|].
  apply Rmult_le_compat; [apply Rmult_le_pos; lra|lra| |exact Hle].
  apply Rmult_le_compat; lra.
Qed.

Lemma gaussian_covariance_ddcoef_bound p q P Q M lo hi t a k :
  0 <= M -> 0 < lo -> hi < 1 -> lo <= t <= hi -> (k < (p + q)%coq_nat)%coq_nat ->
  (forall k, (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall k, (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  Rabs (gaussian_covariance_ddcoef p q P Q t a k) <=
  M * (/ (4 * (sqrt lo * sqrt lo * sqrt lo)) +
       / (4 * (sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi)))).
Proof.
  intros HM Hlo Hhi Ht Hk HP HQ; unfold gaussian_covariance_ddcoef.
  assert (Hslo : 0 < sqrt lo) by (apply sqrt_lt_R0; exact Hlo).
  assert (Hshi : 0 < sqrt (1 - hi)) by (apply sqrt_lt_R0; lra).
  assert (Hst : 0 < sqrt t) by (apply sqrt_lt_R0; lra).
  assert (Hs1 : 0 < sqrt (1 - t)) by (apply sqrt_lt_R0; lra).
  assert (Hlo' : 0 < sqrt lo * sqrt lo * sqrt lo)
    by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption).
  assert (Hhi' : 0 < sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi))
    by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption).
  assert (Ht' : 0 < sqrt t * sqrt t * sqrt t)
    by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption).
  assert (Ht1' : 0 < sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t))
    by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption).
  assert (Hpos1 : 0 <= / (4 * (sqrt lo * sqrt lo * sqrt lo)))
    by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
  assert (Hpos2 : 0 <= / (4 * (sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi))))
    by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
  destruct (Nat.ltb k p) eqn:E.
  - apply Nat.ltb_lt in E.
    unfold Rdiv; rewrite Rabs_mult Rabs_Ropp (Rabs_right (/ (4 * (sqrt t * sqrt t * sqrt t)))
      (Rle_ge _ _ (Rlt_le _ _ (Rinv_0_lt_compat (4 * (sqrt t * sqrt t * sqrt t)) ltac:(lra))))).
    assert (Hi : / (4 * (sqrt t * sqrt t * sqrt t)) <= / (4 * (sqrt lo * sqrt lo * sqrt lo))).
    { rewrite (Rinv_mult 4 (sqrt t * sqrt t * sqrt t)) (Rinv_mult 4 (sqrt lo * sqrt lo * sqrt lo)).
      apply Rmult_le_compat_l; [apply Rlt_le; apply Rinv_0_lt_compat; lra|apply inv_cube_sqrt_bound; lra]. }
    pose proof (HP k E); pose proof (Rabs_pos (P a k)).
    assert (Hit : 0 <= / (4 * (sqrt t * sqrt t * sqrt t)))
      by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
    apply Rle_trans with (M * / (4 * (sqrt lo * sqrt lo * sqrt lo)));
      [apply Rmult_le_compat; lra|].
    apply Rmult_le_compat_l; lra.
  - apply Nat.ltb_ge in E.
    unfold Rdiv; rewrite Rabs_mult Rabs_Ropp
      (Rabs_right (/ (4 * (sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t))))
      (Rle_ge _ _ (Rlt_le _ _ (Rinv_0_lt_compat (4 * (sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t))) ltac:(lra))))).
    assert (Hi : / (4 * (sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t))) <=
      / (4 * (sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi)))).
    { rewrite (Rinv_mult 4 (sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t)))
        (Rinv_mult 4 (sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi))).
      apply Rmult_le_compat_l; [apply Rlt_le; apply Rinv_0_lt_compat; lra|apply inv_cube_sqrt_bound; lra]. }
    pose proof (HQ (k - p)%coq_nat ltac:(lia)); pose proof (Rabs_pos (Q a (k - p)%coq_nat)).
    assert (Hit : 0 <= / (4 * (sqrt (1 - t) * sqrt (1 - t) * sqrt (1 - t))))
      by (apply Rlt_le; apply Rinv_0_lt_compat; lra).
    apply Rle_trans with (M * / (4 * (sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi))));
      [apply Rmult_le_compat; lra|].
    apply Rmult_le_compat_l; lra.
Qed.
