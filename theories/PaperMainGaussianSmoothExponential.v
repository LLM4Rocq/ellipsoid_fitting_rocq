(* Bounded C2 exponential tests for the covariance concentration route. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity
  PaperMainGordonContinuity PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_exp_test t (f : list R -> R) xs := exp (t * f xs).
Definition paper_main_gaussian_exp_first t (f : list R -> R)
    (Df : nat -> list R -> R) a xs :=
  t * Df a xs * paper_main_gaussian_exp_test t f xs.
Definition paper_main_gaussian_exp_second t (f : list R -> R)
    (Df : nat -> list R -> R) (D2f : nat -> nat -> list R -> R) a b xs :=
  (t * D2f a b xs + t ^ 2 * Df a xs * Df b xs) * paper_main_gaussian_exp_test t f xs.
Definition paper_main_gaussian_exp_constant t M :=
  (1 + t * M + t ^ 2 * M ^ 2) * exp (t * M).

Lemma paper_main_gaussian_exp_derivative d a t f Df :
  finite_coordinate_derivative d a f (Df a) ->
  finite_coordinate_derivative d a (paper_main_gaussian_exp_test t f)
    (paper_main_gaussian_exp_first t f Df a).
Proof.
intros HD; unfold paper_main_gaussian_exp_test, paper_main_gaussian_exp_first.
apply (paper_main_coordinate_derivative_value_ext d a _ (fun xs => exp (t * f xs) * (t * Df a xs))).
- apply paper_main_coordinate_derivative_exp, paper_main_coordinate_derivative_scale; exact HD.
- intros xs Hxs; unfold paper_main_gaussian_exp_test; ring.
Qed.

Lemma paper_main_gaussian_exp_second_derivative d a b t f Df D2f :
  finite_coordinate_derivative d b f (Df b) ->
  finite_coordinate_derivative d b (Df a) (D2f a b) ->
  finite_coordinate_derivative d b (paper_main_gaussian_exp_first t f Df a)
    (paper_main_gaussian_exp_second t f Df D2f a b).
Proof.
intros HD HD2; unfold paper_main_gaussian_exp_first, paper_main_gaussian_exp_second.
apply (paper_main_coordinate_derivative_value_ext d b _
  (fun xs => (t * D2f a b xs) * paper_main_gaussian_exp_test t f xs +
    (t * Df a xs) * (t * Df b xs * paper_main_gaussian_exp_test t f xs))).
- apply paper_main_coordinate_derivative_mult.
  + apply paper_main_coordinate_derivative_scale; exact HD2.
  + apply paper_main_gaussian_exp_derivative; exact HD.
- intros xs Hxs; ring.
Qed.

Lemma paper_main_gaussian_exp_continuous d t f :
  finite_joint_continuous d f ->
  finite_joint_continuous d (paper_main_gaussian_exp_test t f).
Proof.
intros Hf; unfold paper_main_gaussian_exp_test.
apply paper_main_gordon_joint_exp, finite_joint_continuous_scale; exact Hf.
Qed.

Lemma paper_main_gaussian_exp_first_continuous d a t f Df :
  finite_joint_continuous d f -> finite_joint_continuous d (Df a) ->
  finite_joint_continuous d (paper_main_gaussian_exp_first t f Df a).
Proof.
intros Hf HD; unfold paper_main_gaussian_exp_first.
apply finite_joint_continuous_mult.
- apply finite_joint_continuous_scale; exact HD.
- apply paper_main_gaussian_exp_continuous; exact Hf.
Qed.

Lemma paper_main_gaussian_exp_second_continuous d a b t f Df D2f :
  finite_joint_continuous d f ->
  finite_joint_continuous d (Df a) -> finite_joint_continuous d (Df b) ->
  finite_joint_continuous d (D2f a b) ->
  finite_joint_continuous d (paper_main_gaussian_exp_second t f Df D2f a b).
Proof.
intros Hf HDa HDb HD2; unfold paper_main_gaussian_exp_second.
apply finite_joint_continuous_mult; [|apply paper_main_gaussian_exp_continuous; exact Hf].
apply finite_joint_continuous_add; [apply finite_joint_continuous_scale; exact HD2|].
apply finite_joint_continuous_mult; [apply finite_joint_continuous_scale; exact HDa|exact HDb].
Qed.

Lemma paper_main_gaussian_exp_scalar_bounds t M x y z w :
  0 <= t -> 0 <= M ->
  Rabs x <= M -> Rabs y <= M -> Rabs z <= M -> Rabs w <= M ->
  0 <= paper_main_gaussian_exp_constant t M /\
  Rabs (exp (t * x)) <= paper_main_gaussian_exp_constant t M /\
  Rabs (t * y * exp (t * x)) <= paper_main_gaussian_exp_constant t M /\
  Rabs ((t * w + t ^ 2 * y * z) * exp (t * x)) <= paper_main_gaussian_exp_constant t M.
Proof.
intros Ht HM Hx Hy Hz Hw.
assert (HE0 : 0 < exp (t * x)) by apply exp_pos.
assert (HEM : 0 < exp (t * M)) by apply exp_pos.
assert (HE : exp (t * x) <= exp (t * M)).
{ assert (Htx : t * x <= t * M) by (pose proof (Rle_abs x); nra).
  destruct (Rle_lt_or_eq_dec _ _ Htx) as [Hlt|Heq].
  - apply Rlt_le, exp_increasing; exact Hlt.
  - rewrite Heq; apply Rle_refl. }
assert (Hyz : Rabs y * Rabs z <= M ^ 2).
{ pose proof (Rabs_pos y); pose proof (Rabs_pos z).
  pose proof (Rmult_le_compat (Rabs y) M (Rabs z) M ltac:(lra) ltac:(lra) Hy Hz).
  nra. }
assert (Hy0 : 0 <= Rabs y) by apply Rabs_pos.
assert (Hz0 : 0 <= Rabs z) by apply Rabs_pos.
assert (Hw0 : 0 <= Rabs w) by apply Rabs_pos.
assert (HC1 : exp (t * M) <= paper_main_gaussian_exp_constant t M).
{ assert (Htm : 0 <= t * M) by (apply Rmult_le_pos; assumption).
  assert (Hsq : 0 <= t ^ 2 * M ^ 2) by (apply Rmult_le_pos; nra).
  pose proof (Rmult_le_pos _ _ Htm (Rlt_le _ _ HEM)).
  pose proof (Rmult_le_pos _ _ Hsq (Rlt_le _ _ HEM)).
  unfold paper_main_gaussian_exp_constant; nra. }
assert (HC2 : (t * M) * exp (t * M) <= paper_main_gaussian_exp_constant t M).
{ assert (Hsq : 0 <= t ^ 2 * M ^ 2) by (apply Rmult_le_pos; nra).
  pose proof (Rmult_le_pos _ _ Hsq (Rlt_le _ _ HEM)).
  unfold paper_main_gaussian_exp_constant; nra. }
assert (HC3 : (t * M + t ^ 2 * M ^ 2) * exp (t * M) <= paper_main_gaussian_exp_constant t M).
{ unfold paper_main_gaussian_exp_constant; nra. }
split; [lra|].
split.
- rewrite Rabs_pos_eq; [lra|lra].
- split.
  + rewrite !Rabs_mult (Rabs_pos_eq t Ht) (Rabs_pos_eq (exp (t * x)) ltac:(lra)).
    eapply Rle_trans; [|exact HC2].
    apply Rmult_le_compat; try nra.
  + rewrite Rabs_mult (Rabs_pos_eq (exp (t * x)) ltac:(lra)).
    eapply Rle_trans; [|exact HC3].
    apply Rmult_le_compat; [apply Rabs_pos|lra| |exact HE].
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite !Rabs_mult (Rabs_pos_eq t Ht).
    try rewrite Rabs_R1.
    pose proof (Rmult_le_compat_l (t ^ 2) (Rabs y * Rabs z) (M ^ 2) ltac:(nra) Hyz) as Hsq.
    nra.
Qed.

Theorem paper_main_gaussian_exp_smooth d t f Df D2f M :
  0 <= t -> paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  paper_main_gaussian_smooth_test d (paper_main_gaussian_exp_test t f)
    (paper_main_gaussian_exp_first t f Df)
    (paper_main_gaussian_exp_second t f Df D2f)
    (paper_main_gaussian_exp_constant t M) 0.
Proof.
intros Ht [Hf HD HDc HD2 HD2c Hfb HDb HD2b].
destruct (proj1 (paper_main_polynomial_zero_bound d M f) Hfb) as [HM HB].
assert (H0 : Rabs 0 <= M) by (rewrite Rabs_R0; exact HM).
pose proof (proj1 (paper_main_gaussian_exp_scalar_bounds t M 0 0 0 0 Ht HM H0 H0 H0 H0)) as HC.
assert (HDB : forall a, (a < d)%coq_nat -> forall xs, List.length xs = d -> Rabs (Df a xs) <= M).
{ intros a Ha; exact (proj2 (proj1 (paper_main_polynomial_zero_bound d M (Df a)) (HDb a Ha))). }
assert (HD2B : forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
  forall xs, List.length xs = d -> Rabs (D2f a b xs) <= M).
{ intros a b Ha Hb; exact (proj2 (proj1 (paper_main_polynomial_zero_bound d M (D2f a b)) (HD2b a b Ha Hb))). }
constructor.
- apply paper_main_gaussian_exp_continuous; exact Hf.
- intros a Ha; apply paper_main_gaussian_exp_derivative, HD; exact Ha.
- intros a Ha; apply paper_main_gaussian_exp_first_continuous; [exact Hf|apply HDc; exact Ha].
- intros a b Ha Hb; apply paper_main_gaussian_exp_second_derivative; [apply HD; exact Hb|apply HD2; assumption].
- intros a b Ha Hb; apply paper_main_gaussian_exp_second_continuous;
    [exact Hf|apply HDc; exact Ha|apply HDc; exact Hb|apply HD2c; assumption].
- apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs.
  exact (proj1 (proj2 (paper_main_gaussian_exp_scalar_bounds t M (f xs) 0 0 0
    Ht HM (HB xs Hxs) H0 H0 H0))).
- intros a Ha; apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs.
  exact (proj1 (proj2 (proj2 (paper_main_gaussian_exp_scalar_bounds t M (f xs) (Df a xs) 0 0
    Ht HM (HB xs Hxs) (HDB a Ha xs Hxs) H0 H0)))).
- intros a b Ha Hb; apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs.
  exact (proj2 (proj2 (proj2 (paper_main_gaussian_exp_scalar_bounds t M (f xs)
    (Df a xs) (Df b xs) (D2f a b xs) Ht HM (HB xs Hxs)
    (HDB a Ha xs Hxs) (HDB b Hb xs Hxs) (HD2B a b Ha Hb xs Hxs))))).
Qed.
