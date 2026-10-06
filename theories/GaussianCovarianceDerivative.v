(* The derivative of Gaussian interpolation between two covariances. Let
   Z(t) = gaussian_covariance_path K p q P Q t zs be the interpolation
   sqrt t * P xs + sqrt (1 - t) * Q ys, where xs and ys are the first p and
   the last q coordinates of zs. Let f be a continuous function of K
   coordinates whose first and second partial derivatives Df and D2f are
   continuous and, like f, polynomially bounded. For 0 < t < 1, the
   derivative of t |-> E f(Z(t)) is one half of the pairing of
   P P^T - Q Q^T with the expectations E [D2f a b (Z(t))]
   (gaussian_covariance_derivative_clause).

   Z(t, zs) is the linear image of zs by the coefficients coef t, with
   velocity dcoef t and acceleration ddcoef t (GaussianCovariancePath). The
   derivative passes under the expectation by
   finite_gaussian_parameter_differentiation (FiniteGaussianParameter),
   whose hypotheses come from the chain rule and from polynomial bounds
   uniform on a closed subinterval of (0, 1) (gc_expectation_derive). The
   expectation of the velocity sum_c Df c (Z) * sum_k dcoef c k z_k is
   computed with the Stein identity gaussian_iterated_coordinate_first_stein:
   the derivative of Df c (Z(t, zs)) in z_k is sum_b D2f c b (Z) * coef b k,
   and sum_k dcoef c k * coef b k = (1/2) ((P P^T)_cb - (Q Q^T)_cb)
   (gc_velocity_expectation). MathComp is loaded, so %coq_nat marks
   Stdlib's arithmetic on nat. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinateDerivativeDefinitions
  GaussianCoordinateStein GaussianCoordinateSteinDomains GaussianFiniteSums
  GaussianCoordinateSuffixAlgebra JointDefinitions FiniteGaussianParameter
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCovariancePath GaussianCovarianceDomains.
Import ListNotations.
Open Scope R_scope.

(* A polynomial bound of a finite sum with one constant for every term. *)
Lemma finite_polynomial_bound_sum_uniform d I (F : nat -> list R -> R) C p :
  0 <= C ->
  (forall i, In i I -> finite_polynomial_bound d C p (F i)) ->
  finite_polynomial_bound d (INR (List.length I) * C) p
    (fun xs => finite_sum (fun i => F i xs) I).
Proof.
  intros HC HF; split.
  - apply Rmult_le_pos; [apply pos_INR|exact HC].
  - intros xs Hxs.
    rewrite Rmult_assoc.
    apply finite_sum_bound; intros i Hi.
    exact (proj2 (HF i Hi) xs Hxs).
Qed.

Section Derivative.

Variables (K p q : nat) (P Q : nat -> nat -> R) (f : list R -> R)
  (Df : nat -> list R -> R) (D2f : nat -> nat -> list R -> R) (C : R) (r : nat).

Hypothesis Hf : finite_joint_continuous K f.
Hypothesis HD : forall a, (a < K)%coq_nat -> finite_coordinate_derivative K a f (Df a).
Hypothesis HDc : forall a, (a < K)%coq_nat -> finite_joint_continuous K (Df a).
Hypothesis HD2 : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_coordinate_derivative K b (Df a) (D2f a b).
Hypothesis HD2c : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_joint_continuous K (D2f a b).
Hypothesis Hfb : finite_polynomial_bound K C r f.
Hypothesis HDb : forall a, (a < K)%coq_nat -> finite_polynomial_bound K C r (Df a).
Hypothesis HD2b : forall a b, (a < K)%coq_nat -> (b < K)%coq_nat ->
  finite_polynomial_bound K C r (D2f a b).

Let d := (p + q)%coq_nat.
Let cf (t : R) := gaussian_covariance_coef p q P Q t.
Let dcf (t : R) := gaussian_covariance_dcoef p q P Q t.
Let ddcf (t : R) := gaussian_covariance_ddcoef p q P Q t.
Let Lam (t : R) (zs : list R) := linear_image d K (cf t) zs.

Definition gc_value (t : R) (zs : list R) : R := f (Lam t zs).

Definition gc_velocity (t : R) (zs : list R) : R :=
  finite_sum (fun c => Df c (Lam t zs) * linear_form d (dcf t c) zs) (List.seq 0 K).

Definition gc_acceleration (t : R) (zs : list R) : R :=
  finite_sum (fun c =>
    finite_sum (fun b => D2f c b (Lam t zs) * linear_form d (dcf t b) zs) (List.seq 0 K)
      * linear_form d (dcf t c) zs
    + Df c (Lam t zs) * linear_form d (ddcf t c) zs) (List.seq 0 K).

Lemma gc_value_path t zs : gc_value t zs = f (gaussian_covariance_path K p q P Q t zs).
Proof. unfold gc_value, Lam, cf, d; rewrite gaussian_covariance_path_linear; reflexivity. Qed.

(* Derivatives in t. *)
Lemma gc_value_derive t zs :
  0 < t < 1 -> @is_derive R R^o R^o t 1 (fun u => gc_value u zs) (gc_velocity t zs).
Proof.
  intros Ht; unfold gc_value, gc_velocity, Lam.
  apply (linear_image_parameter_derivative d K cf dcf t zs f Df HD HDc).
  intros a k Ha Hk; unfold cf, dcf.
  apply gaussian_covariance_coef_derive; exact Ht.
Qed.

Lemma gc_velocity_derive t zs :
  0 < t < 1 -> @is_derive R R^o R^o t 1 (fun u => gc_velocity u zs) (gc_acceleration t zs).
Proof.
  intros Ht; unfold gc_velocity, gc_acceleration.
  apply (is_derive_finite_sum
    (fun c u => Df c (Lam u zs) * linear_form d (dcf u c) zs)
    (fun c u => finite_sum (fun b => D2f c b (Lam u zs) * linear_form d (dcf u b) zs)
      (List.seq 0 K) * linear_form d (dcf u c) zs
      + Df c (Lam u zs) * linear_form d (ddcf u c) zs)).
  intros c Hc; apply in_seq_lt in Hc; cbv beta.
  apply is_derive_mult.
  - unfold Lam.
    apply (linear_image_parameter_derivative d K cf dcf t zs (Df c) (D2f c)
      (fun b Hb => HD2 c b Hc Hb) (fun b Hb => HD2c c b Hc Hb)).
    intros a k Ha Hk; unfold cf, dcf.
    apply gaussian_covariance_coef_derive; exact Ht.
  - unfold linear_form.
    apply (is_derive_finite_sum (fun k u => dcf u c k * List.nth k zs 0)
      (fun k u => ddcf u c k * List.nth k zs 0)).
    intros k Hk; apply in_seq_lt in Hk; cbv beta.
    apply is_derive_scal_l; unfold dcf, ddcf.
    apply gaussian_covariance_dcoef_derive; exact Ht.
Qed.

(* Regularity. *)
Lemma gc_value_regular M t :
  0 <= t <= 1 -> 0 <= M ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  finite_joint_continuous d (gc_value t) /\
  finite_polynomial_bound d (C * (1 + M * INR d) ^ (r * K)%coq_nat) (r * K)%coq_nat (gc_value t).
Proof.
  intros Ht HM HP HQ.
  destruct (gaussian_covariance_path_regular K p q P Q M f C r t Ht HM HP HQ Hf Hfb) as [H1 H2].
  split.
  - apply (finite_joint_continuous_ext _ _ _ (fun zs _ => Logic.eq_sym (gc_value_path t zs)) H1).
  - split; [exact (proj1 H2)|].
    intros zs Hzs; rewrite gc_value_path; exact (proj2 H2 zs Hzs).
Qed.

Lemma gc_composite_regular M t (g : list R -> R) :
  0 <= t <= 1 -> 0 <= M ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  finite_joint_continuous K g -> finite_polynomial_bound K C r g ->
  finite_joint_continuous d (fun zs => g (Lam t zs)) /\
  finite_polynomial_bound d (C * (1 + M * INR d) ^ (r * K)%coq_nat) (r * K)%coq_nat
    (fun zs => g (Lam t zs)).
Proof.
  intros Ht HM HP HQ Hg Hgb; unfold Lam; split.
  - apply linear_image_continuous_comp; exact Hg.
  - apply (linear_image_polynomial_bound_comp _ _ _ M _ _ _ HM); [|exact Hgb].
    apply gaussian_covariance_path_coef_uniform; assumption.
Qed.

Lemma gc_velocity_continuous t : finite_joint_continuous d (gc_velocity t).
Proof.
  unfold gc_velocity.
  apply finite_joint_continuous_sum; intros c Hc; apply in_seq_lt in Hc.
  apply finite_joint_continuous_mult; [|apply linear_form_continuous].
  unfold Lam; apply linear_image_continuous_comp; exact (HDc c Hc).
Qed.

Lemma gc_velocity_bound M lo hi t :
  0 <= M -> 0 < lo -> hi < 1 -> lo <= t <= hi ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  finite_polynomial_bound d
    (INR (List.length (List.seq 0 K)) * (C * (1 + M * INR d) ^ (r * K)%coq_nat *
      (M * (/ (2 * sqrt lo) + / (2 * sqrt (1 - hi))) * INR d)))
    ((r * K)%coq_nat + 1)%coq_nat (gc_velocity t).
Proof.
  intros HM Hlo Hhi Ht HP HQ.
  assert (Ht01 : 0 <= t <= 1) by lra.
  assert (HL1 : 0 <= M * (/ (2 * sqrt lo) + / (2 * sqrt (1 - hi)))).
  { apply Rmult_le_pos; [exact HM|].
    assert (0 < sqrt lo) by (apply sqrt_lt_R0; exact Hlo).
    assert (0 < sqrt (1 - hi)) by (apply sqrt_lt_R0; lra).
    pose proof (Rinv_0_lt_compat (2 * sqrt lo) ltac:(lra)).
    pose proof (Rinv_0_lt_compat (2 * sqrt (1 - hi)) ltac:(lra)); lra. }
  unfold gc_velocity.
  apply finite_polynomial_bound_sum_uniform.
  { apply Rmult_le_pos; [apply Rmult_le_pos; [exact (proj1 Hfb)|apply pow_le]|
      apply Rmult_le_pos; [exact HL1|apply pos_INR]].
    pose proof (Rmult_le_pos M (INR d) HM (pos_INR d)); lra. }
  intros c Hc; apply in_seq_lt in Hc.
  apply finite_polynomial_bound_mult.
  - exact (proj2 (gc_composite_regular M t (Df c) Ht01 HM HP HQ (HDc c Hc) (HDb c Hc))).
  - apply linear_form_bound; [exact HL1|].
    intros k Hk; unfold dcf.
    apply (gaussian_covariance_dcoef_bound p q P Q M lo hi t c k HM Hlo Hhi Ht Hk
      (fun j Hj => HP c j Hc Hj) (fun j Hj => HQ c j Hc Hj)).
Qed.

Lemma gc_acceleration_bound M lo hi :
  0 <= M -> 0 < lo -> hi < 1 ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  exists Cst, forall t, lo <= t <= hi ->
    finite_polynomial_bound d Cst (((r * K)%coq_nat + 1)%coq_nat + 1)%coq_nat (gc_acceleration t).
Proof.
  intros HM Hlo Hhi HP HQ.
  assert (Hslo : 0 < sqrt lo) by (apply sqrt_lt_R0; exact Hlo).
  assert (Hshi : 0 < sqrt (1 - hi)) by (apply sqrt_lt_R0; lra).
  set (C1 := C * (1 + M * INR d) ^ (r * K)%coq_nat).
  set (M1 := M * (/ (2 * sqrt lo) + / (2 * sqrt (1 - hi)))).
  set (M2 := M * (/ (4 * (sqrt lo * sqrt lo * sqrt lo)) +
    / (4 * (sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi))))).
  assert (HC1 : 0 <= C1).
  { unfold C1; apply Rmult_le_pos; [exact (proj1 Hfb)|apply pow_le].
    pose proof (Rmult_le_pos M (INR d) HM (pos_INR d)); lra. }
  assert (HM1 : 0 <= M1).
  { unfold M1; apply Rmult_le_pos; [exact HM|].
    pose proof (Rinv_0_lt_compat (2 * sqrt lo) ltac:(lra)).
    pose proof (Rinv_0_lt_compat (2 * sqrt (1 - hi)) ltac:(lra)); lra. }
  assert (HM2 : 0 <= M2).
  { unfold M2; apply Rmult_le_pos; [exact HM|].
    assert (0 < sqrt lo * sqrt lo * sqrt lo)
      by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption).
    assert (0 < sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi))
      by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption).
    pose proof (Rinv_0_lt_compat (4 * (sqrt lo * sqrt lo * sqrt lo)) ltac:(lra)).
    pose proof (Rinv_0_lt_compat (4 * (sqrt (1 - hi) * sqrt (1 - hi) * sqrt (1 - hi)))
      ltac:(lra)); lra. }
  pose proof (pos_INR d) as Hd.
  pose proof (pos_INR (List.length (List.seq 0 K))) as HK.
  exists (INR (List.length (List.seq 0 K)) *
    (INR (List.length (List.seq 0 K)) * (C1 * (M1 * INR d)) * (M1 * INR d) + C1 * (M2 * INR d))).
  intros t Ht.
  assert (Ht01 : 0 <= t <= 1) by lra.
  unfold gc_acceleration.
  apply finite_polynomial_bound_sum_uniform.
  { apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos; [apply Rmult_le_pos; [exact HK|]|]; apply Rmult_le_pos; auto.
      apply Rmult_le_pos; auto.
    - apply Rmult_le_pos; [exact HC1|apply Rmult_le_pos; auto]. }
  intros c Hc; apply in_seq_lt in Hc.
  apply finite_polynomial_bound_add.
  - apply finite_polynomial_bound_mult.
    + apply finite_polynomial_bound_sum_uniform.
      { apply Rmult_le_pos; [exact HC1|apply Rmult_le_pos; auto]. }
      intros b Hb; apply in_seq_lt in Hb.
      apply finite_polynomial_bound_mult.
      * exact (proj2 (gc_composite_regular M t (D2f c b) Ht01 HM HP HQ (HD2c c b Hc Hb)
          (HD2b c b Hc Hb))).
      * apply linear_form_bound; [exact HM1|].
        intros k Hk; unfold dcf, M1.
        apply (gaussian_covariance_dcoef_bound p q P Q M lo hi t b k HM Hlo Hhi Ht Hk
          (fun j Hj => HP b j Hb Hj) (fun j Hj => HQ b j Hb Hj)).
    + apply linear_form_bound; [exact HM1|].
      intros k Hk; unfold dcf, M1.
      apply (gaussian_covariance_dcoef_bound p q P Q M lo hi t c k HM Hlo Hhi Ht Hk
        (fun j Hj => HP c j Hc Hj) (fun j Hj => HQ c j Hc Hj)).
  - apply (finite_polynomial_bound_degree_monotone _ _ ((r * K)%coq_nat + 1)%coq_nat); [|lia].
    apply finite_polynomial_bound_mult.
    + exact (proj2 (gc_composite_regular M t (Df c) Ht01 HM HP HQ (HDc c Hc) (HDb c Hc))).
    + apply linear_form_bound; [exact HM2|].
      intros k Hk; unfold ddcf, M2.
      apply (gaussian_covariance_ddcoef_bound p q P Q M lo hi t c k HM Hlo Hhi Ht Hk
        (fun j Hj => HP c j Hc Hj) (fun j Hj => HQ c j Hc Hj)).
Qed.

(* The derivative of t |-> E f(Z(t)) is E of the velocity. *)
Theorem gc_expectation_derive a :
  0 < a < 1 ->
  gaussian_list_domain d (gc_velocity a) /\
  @is_derive R R^o R^o a 1 (fun t => gaussian_iterated_expectation d (gc_value t))
    (gaussian_iterated_expectation d (gc_velocity a)).
Proof.
  intros Ha.
  destruct (gaussian_covariance_matrix_bound K p q P Q) as [M [HM [HP HQ]]].
  set (rho := Rmin a (1 - a) / 2).
  assert (Hrho : 0 < rho).
  { unfold rho; apply Rdiv_lt_0_compat; [apply Rmin_pos; lra|lra]. }
  assert (Hrho_a : rho <= a / 2) by (unfold rho; pose proof (Rmin_l a (1 - a)); lra).
  assert (Hrho_b : rho <= (1 - a) / 2) by (unfold rho; pose proof (Rmin_r a (1 - a)); lra).
  set (lo := a - rho). set (hi := a + rho).
  assert (Hlo : 0 < lo) by (unfold lo; lra).
  assert (Hhi : hi < 1) by (unfold hi; lra).
  destruct (gc_acceleration_bound M lo hi HM Hlo Hhi HP HQ) as [Cst HCst].
  destruct (gc_velocity_bound M lo hi a HM Hlo Hhi ltac:(unfold lo, hi; lra) HP HQ) as [HB1 HB2].
  destruct (finite_gaussian_parameter_differentiation d gc_value gc_velocity gc_acceleration
    a rho Cst (((r * K)%coq_nat + 1)%coq_nat + 1)%coq_nat
    (C * (1 + M * INR d) ^ (r * K)%coq_nat) (r * K)%coq_nat
    (INR (List.length (List.seq 0 K)) * (C * (1 + M * INR d) ^ (r * K)%coq_nat *
      (M * (/ (2 * sqrt lo) + / (2 * sqrt (1 - hi))) * INR d))) ((r * K)%coq_nat + 1)%coq_nat Hrho)
    as [_ [Hdom Hder]].
  - intros t zs Ht _; apply gc_value_derive.
    apply Rabs_le_between in Ht; unfold lo, hi in *; lra.
  - intros t zs Ht _; apply gc_velocity_derive.
    apply Rabs_le_between in Ht; unfold lo, hi in *; lra.
  - intros t Ht; apply HCst; apply Rabs_le_between in Ht; unfold lo, hi; lra.
  - intros t Ht; apply Rabs_le_between in Ht.
    exact (proj1 (gc_value_regular M t ltac:(unfold lo, hi in *; lra) HM HP HQ)).
  - apply gc_velocity_continuous.
  - intros t Ht; apply Rabs_le_between in Ht.
    exact (proj2 (gc_value_regular M t ltac:(unfold lo, hi in *; lra) HM HP HQ)).
  - split; [exact HB1|exact HB2].
  - split; [exact Hdom|exact Hder].
Qed.

(* The expectation of the velocity, by the Stein identity. *)
Lemma gc_velocity_expectation_zero a :
  d = 0%nat -> gaussian_iterated_expectation d (gc_velocity a) = 0.
Proof.
  intros Hd.
  assert (H0 : forall zs, List.length zs = d -> gc_velocity a zs = 0).
  { intros zs _; unfold gc_velocity.
    assert (Hz : forall c, In c (List.seq 0 K) ->
      Df c (Lam a zs) * linear_form d (dcf a c) zs = 0).
    { intros c _; unfold linear_form; rewrite Hd; simpl; ring. }
    rewrite (finite_sum_ext _ _ _ Hz); apply finite_sum_zero. }
  rewrite (gaussian_iterated_expectation_ext _ _ _ H0).
  exact (proj2 (gaussian_iterated_constant d 0)).
Qed.

Lemma gc_pairing_zero H : d = 0%nat -> gaussian_covariance_pairing K p q P Q H = 0.
Proof.
  intros Hd.
  assert (Hp : p = 0%nat) by (unfold d in Hd; lia).
  assert (Hq : q = 0%nat) by (unfold d in Hd; lia).
  unfold gaussian_covariance_pairing.
  assert (Hz : forall c, In c (List.seq 0 K) ->
    finite_sum (fun b => (gaussian_covariance_entry p P c b - gaussian_covariance_entry q Q c b)
      * H c b) (List.seq 0 K) = 0).
  { intros c _.
    assert (Hz' : forall b, In b (List.seq 0 K) ->
      (gaussian_covariance_entry p P c b - gaussian_covariance_entry q Q c b) * H c b = 0).
    { intros b _; unfold gaussian_covariance_entry; rewrite Hp Hq; simpl; ring. }
    rewrite (finite_sum_ext _ _ _ Hz'); apply finite_sum_zero. }
  rewrite (finite_sum_ext _ _ _ Hz); apply finite_sum_zero.
Qed.

Lemma gc_partial_regular M a c k :
  0 <= a <= 1 -> 0 <= M ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  (c < K)%coq_nat -> (k < d)%coq_nat ->
  finite_joint_continuous d
    (fun zs => finite_sum (fun b => D2f c b (Lam a zs) * cf a b k) (List.seq 0 K)) /\
  exists E, finite_polynomial_bound d E (r * K)%coq_nat
    (fun zs => finite_sum (fun b => D2f c b (Lam a zs) * cf a b k) (List.seq 0 K)).
Proof.
  intros Ha HM HP HQ Hc Hk; split.
  - apply finite_joint_continuous_sum; intros b Hb; apply in_seq_lt in Hb.
    apply (finite_joint_continuous_ext d (fun zs => cf a b k * D2f c b (Lam a zs))).
    { intros zs _; ring. }
    apply finite_joint_continuous_scale.
    exact (proj1 (gc_composite_regular M a (D2f c b) Ha HM HP HQ (HD2c c b Hc Hb) (HD2b c b Hc Hb))).
  - apply finite_polynomial_bound_sum; intros b Hb; apply in_seq_lt in Hb.
    eexists.
    apply (finite_polynomial_bound_ext d _ _ (fun zs => cf a b k * D2f c b (Lam a zs))).
    { intros zs _; ring. }
    apply finite_polynomial_bound_scale.
    exact (proj2 (gc_composite_regular M a (D2f c b) Ha HM HP HQ (HD2c c b Hc Hb) (HD2b c b Hc Hb))).
Qed.

Lemma gc_stein_term M a c k :
  0 < a < 1 -> 0 <= M ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  (forall a k, (a < K)%coq_nat -> (k < q)%coq_nat -> Rabs (Q a k) <= M) ->
  (c < K)%coq_nat -> (k < d)%coq_nat ->
  gaussian_iterated_expectation d (fun zs => List.nth k zs 0 * Df c (Lam a zs)) =
  finite_sum (fun b => cf a b k *
    gaussian_iterated_expectation d (fun zs => D2f c b (Lam a zs))) (List.seq 0 K).
Proof.
  intros Ha HM HP HQ Hc Hk.
  assert (Ha01 : 0 <= a <= 1) by lra.
  destruct (gc_composite_regular M a (Df c) Ha01 HM HP HQ (HDc c Hc) (HDb c Hc)) as [HFc HFb].
  destruct (gc_partial_regular M a c k Ha01 HM HP HQ Hc Hk) as [HDFc [E HDFb]].
  assert (Hderiv : finite_coordinate_derivative d k (fun zs => Df c (Lam a zs))
    (fun zs => finite_sum (fun b => D2f c b (Lam a zs) * cf a b k) (List.seq 0 K))).
  { unfold Lam.
    apply (linear_image_coordinate_derivative_comp d K (cf a) k (Df c) (D2f c) Hk
      (fun b Hb => HD2 c b Hc Hb) (fun b Hb => HD2c c b Hc Hb)). }
  assert (Hd : d = S (Nat.pred d)) by lia.
  transitivity (gaussian_iterated_expectation d
    (fun zs => finite_sum (fun b => D2f c b (Lam a zs) * cf a b k) (List.seq 0 K))).
  { symmetry.
    revert HFc HFb HDFc HDFb Hderiv; rewrite Hd; intros HFc HFb HDFc HDFb Hderiv.
    apply (gaussian_iterated_coordinate_first_stein (Nat.pred d) k _ _ _ _ _ _
      ltac:(lia) HFc HDFc HFb HDFb Hderiv). }
  assert (Hint : forall b, In b (List.seq 0 K) ->
    gaussian_iterated_integrable d (fun zs => cf a b k * D2f c b (Lam a zs))).
  { intros b Hb; apply in_seq_lt in Hb.
    destruct (gc_composite_regular M a (D2f c b) Ha01 HM HP HQ (HD2c c b Hc Hb) (HD2b c b Hc Hb))
      as [H1 H2].
    apply (proj1 (gaussian_iterated_scale d _ (cf a b k)
      (proj1 (gaussian_coordinate_polynomial_domain d _ _ _ H1 H2)))). }
  assert (H1 : forall zs, List.length zs = d ->
    finite_sum (fun b => D2f c b (Lam a zs) * cf a b k) (List.seq 0 K) =
    finite_sum (fun b => cf a b k * D2f c b (Lam a zs)) (List.seq 0 K)).
  { intros zs _; apply finite_sum_ext; intros b _; ring. }
  rewrite (gaussian_iterated_expectation_ext _ _ _ H1).
  rewrite (proj2 (gaussian_iterated_finite_sum d (List.seq 0 K)
    (fun b zs => cf a b k * D2f c b (Lam a zs)) Hint)).
  apply finite_sum_ext; intros b Hb; apply in_seq_lt in Hb.
  destruct (gc_composite_regular M a (D2f c b) Ha01 HM HP HQ (HD2c c b Hc Hb) (HD2b c b Hc Hb))
    as [H2 H3].
  exact (proj2 (gaussian_iterated_scale d _ (cf a b k)
    (proj1 (gaussian_coordinate_polynomial_domain d _ _ _ H2 H3)))).
Qed.

Theorem gc_velocity_expectation a :
  0 < a < 1 ->
  gaussian_iterated_expectation d (gc_velocity a) =
  / 2 * gaussian_covariance_pairing K p q P Q (fun c b =>
    gaussian_iterated_expectation d (fun zs => D2f c b (Lam a zs))).
Proof.
  intros Ha.
  destruct (gaussian_covariance_matrix_bound K p q P Q) as [M [HM [HP HQ]]].
  assert (Ha01 : 0 <= a <= 1) by lra.
  destruct (Nat.eq_dec d 0) as [Hd0|Hd0].
  { rewrite (gc_velocity_expectation_zero a Hd0) (gc_pairing_zero _ Hd0); ring. }
  (* integrability of the terms z_k * Df c (Lam a zs) *)
  assert (Hterm : forall c k, (c < K)%coq_nat -> (k < d)%coq_nat ->
    gaussian_iterated_integrable d (fun zs => dcf a c k * (List.nth k zs 0 * Df c (Lam a zs)))).
  { intros c k Hc Hk.
    destruct (gc_composite_regular M a (Df c) Ha01 HM HP HQ (HDc c Hc) (HDb c Hc)) as [H1 H2].
    apply (proj1 (gaussian_iterated_scale d _ (dcf a c k)
      (proj1 (gaussian_coordinate_polynomial_domain d _ _ _
        (finite_joint_continuous_times_coordinate d _ k H1 Hk)
        (finite_polynomial_bound_times_coordinate d _ _ _ k H2 Hk))))). }
  assert (Hsum : forall c, In c (List.seq 0 K) ->
    gaussian_iterated_integrable d
      (fun zs => finite_sum (fun k => dcf a c k * (List.nth k zs 0 * Df c (Lam a zs))) (List.seq 0 d))).
  { intros c Hc; apply in_seq_lt in Hc.
    refine (proj1 (gaussian_iterated_finite_sum d (List.seq 0 d)
      (fun k zs => dcf a c k * (List.nth k zs 0 * Df c (Lam a zs))) _)).
    intros k Hk; apply in_seq_lt in Hk; exact (Hterm c k Hc Hk). }
  assert (H1 : forall zs, List.length zs = d -> gc_velocity a zs =
    finite_sum (fun c => finite_sum (fun k => dcf a c k * (List.nth k zs 0 * Df c (Lam a zs)))
      (List.seq 0 d)) (List.seq 0 K)).
  { intros zs _; unfold gc_velocity, linear_form.
    apply finite_sum_ext; intros c _.
    rewrite <- (finite_sum_scale (Df c (Lam a zs))).
    apply finite_sum_ext; intros k _; ring. }
  rewrite (gaussian_iterated_expectation_ext _ _ _ H1).
  rewrite (proj2 (gaussian_iterated_finite_sum d (List.seq 0 K) _ Hsum)).
  unfold gaussian_covariance_pairing.
  rewrite <- finite_sum_scale.
  apply finite_sum_ext; intros c Hc; apply in_seq_lt in Hc.
  rewrite (proj2 (gaussian_iterated_finite_sum d (List.seq 0 d)
    (fun k zs => dcf a c k * (List.nth k zs 0 * Df c (Lam a zs)))
    (fun k Hk => Hterm c k Hc (in_seq_lt _ _ Hk)))).
  assert (H2 : forall k, In k (List.seq 0 d) ->
    gaussian_iterated_expectation d (fun zs => dcf a c k * (List.nth k zs 0 * Df c (Lam a zs))) =
    dcf a c k * finite_sum (fun b => cf a b k *
      gaussian_iterated_expectation d (fun zs => D2f c b (Lam a zs))) (List.seq 0 K)).
  { intros k Hk; apply in_seq_lt in Hk.
    destruct (gc_composite_regular M a (Df c) Ha01 HM HP HQ (HDc c Hc) (HDb c Hc)) as [H3 H4].
    rewrite (proj2 (gaussian_iterated_scale d _ (dcf a c k)
      (proj1 (gaussian_coordinate_polynomial_domain d _ _ _
        (finite_joint_continuous_times_coordinate d _ k H3 Hk)
        (finite_polynomial_bound_times_coordinate d _ _ _ k H4 Hk))))).
    rewrite (gc_stein_term M a c k Ha HM HP HQ Hc Hk); reflexivity. }
  rewrite (finite_sum_ext _ _ _ H2).
  (* sum_k dcf c k * sum_b cf b k * E_cb = sum_b (sum_k dcf c k * cf b k) * E_cb *)
  transitivity (finite_sum (fun b => finite_sum (fun k => dcf a c k * cf a b k) (List.seq 0 d) *
    gaussian_iterated_expectation d (fun zs => D2f c b (Lam a zs))) (List.seq 0 K)).
  { transitivity (finite_sum (fun k => finite_sum (fun b => dcf a c k * cf a b k *
      gaussian_iterated_expectation d (fun zs => D2f c b (Lam a zs))) (List.seq 0 K)) (List.seq 0 d)).
    { apply finite_sum_ext; intros k _.
      rewrite <- finite_sum_scale; apply finite_sum_ext; intros b _; ring. }
    rewrite finite_sum_swap.
    apply finite_sum_ext; intros b _.
    rewrite <- finite_sum_scale_r; apply finite_sum_ext; intros k _; ring. }
  rewrite <- finite_sum_scale.
  apply finite_sum_ext; intros b _.
  unfold dcf, cf, d.
  rewrite (gaussian_covariance_stein_coefficients p q P Q a c b Ha); ring.
Qed.

(* The main result, with Z(t) written as gaussian_covariance_path. *)
Theorem gaussian_covariance_derivative_clause :
  forall t, 0 < t < 1 ->
  @is_derive R R^o R^o t 1
    (fun u => gaussian_iterated_expectation (p + q)%coq_nat
      (fun zs => f (gaussian_covariance_path K p q P Q u zs)))
    (/ 2 * gaussian_covariance_pairing K p q P Q (fun a b =>
      gaussian_iterated_expectation (p + q)%coq_nat
        (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs)))).
Proof.
  intros t Ht.
  destruct (gc_expectation_derive t Ht) as [_ Hder].
  rewrite (gc_velocity_expectation t Ht) in Hder.
  apply (is_derive_ext (fun u => gaussian_iterated_expectation d (gc_value u))).
  { intros u; apply gaussian_iterated_expectation_ext; intros zs _; apply gc_value_path. }
  replace (gaussian_covariance_pairing K p q P Q (fun a b =>
      gaussian_iterated_expectation (p + q)%coq_nat
        (fun zs => D2f a b (gaussian_covariance_path K p q P Q t zs))))
    with (gaussian_covariance_pairing K p q P Q (fun c b =>
      gaussian_iterated_expectation d (fun zs => D2f c b (Lam t zs)))).
  { exact Hder. }
  unfold gaussian_covariance_pairing; apply finite_sum_ext; intros a _.
  apply finite_sum_ext; intros b _.
  unfold Lam, cf, d; rewrite gaussian_covariance_path_linear; reflexivity.
Qed.

End Derivative.
