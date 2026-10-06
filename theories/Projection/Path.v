(* Differentiation of bounded C2 tests along nonlinear Gaussian features. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.IteratedExpectationDefinitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Gaussian.CoordinatePolynomialContinuity
  Gaussian.FiniteSums Gaussian.CovarianceLinearImages
  Gaussian.CovarianceDerivative Gaussian.ParameterDifferentiation
  Joint.Definitions Gaussian.SmoothCovariance Gaussian.SmoothCalculus
  Projection.Image.
Open Scope R_scope.

Definition paper_main_projection_value (K : nat) (U : nat -> R -> list R -> R)
  (F : list R -> R) (t : R) (xs : list R) :=
  F(paper_main_projection_image K (fun a => U a t) xs).
Definition paper_main_projection_velocity (K : nat) (U DU : nat -> R -> list R -> R)
  (DF : nat -> list R -> R) (t : R) (xs : list R) :=
  finite_sum (fun a => DF a (paper_main_projection_image K (fun b => U b t) xs)*DU a t xs)
    (List.seq 0 K).
Definition paper_main_projection_acceleration (K : nat) (U DU D2U : nat -> R -> list R -> R)
  (DF : nat -> list R -> R) (D2F : nat -> nat -> list R -> R) (t : R) (xs : list R) :=
  finite_sum (fun a =>
    finite_sum (fun b => D2F a b (paper_main_projection_image K (fun c => U c t) xs)*DU b t xs)
      (List.seq 0 K)*DU a t xs+
    DF a (paper_main_projection_image K (fun b => U b t) xs)*D2U a t xs) (List.seq 0 K).

Section Path.
Variables (d K : nat) (U DU D2U : nat -> R -> list R -> R)
  (F : list R -> R) (DF : nat -> list R -> R) (D2F : nat -> nat -> list R -> R) (C : R).
Hypothesis HF : paper_main_gaussian_smooth_test K F DF D2F C 0.

Lemma paper_main_projection_value_derive t xs :
  (forall a, (a<K)%coq_nat -> @is_derive R R^o R^o t 1 (fun s => U a s xs) (DU a t xs)) ->
  @is_derive R R^o R^o t 1 (fun s => paper_main_projection_value K U F s xs)
    (paper_main_projection_velocity K U DU DF t xs).
Proof.
intro HU; unfold paper_main_projection_value,paper_main_projection_velocity,paper_main_projection_image.
apply paper_main_projection_image_parameter; [exact(pmgs_derivative _ _ _ _ _ _ HF)|
  exact(pmgs_derivative_continuous _ _ _ _ _ _ HF)|exact HU].
Qed.

Lemma paper_main_projection_velocity_derive t xs :
  (forall a, (a<K)%coq_nat -> @is_derive R R^o R^o t 1 (fun s => U a s xs) (DU a t xs)) ->
  (forall a, (a<K)%coq_nat -> @is_derive R R^o R^o t 1 (fun s => DU a s xs) (D2U a t xs)) ->
  @is_derive R R^o R^o t 1 (fun s => paper_main_projection_velocity K U DU DF s xs)
    (paper_main_projection_acceleration K U DU D2U DF D2F t xs).
Proof.
intros HU HDU; unfold paper_main_projection_velocity,paper_main_projection_acceleration.
apply (is_derive_finite_sum
  (fun a s => DF a (paper_main_projection_image K (fun b => U b s) xs)*DU a s xs)
  (fun a s => finite_sum (fun b => D2F a b (paper_main_projection_image K (fun c => U c s) xs)*DU b s xs)
    (List.seq 0 K)*DU a s xs+DF a (paper_main_projection_image K (fun b => U b s) xs)*D2U a s xs)).
intros a Ha; apply in_seq in Ha.
apply is_derive_mult; [|apply HDU; lia].
unfold paper_main_projection_image; apply paper_main_projection_image_parameter.
- intros b Hb; exact(pmgs_second_derivative _ _ _ _ _ _ HF a b ltac:(lia) Hb).
- intros b Hb; exact(pmgs_second_continuous _ _ _ _ _ _ HF a b ltac:(lia) Hb).
- exact HU.
Qed.

Lemma paper_main_projection_value_continuous t :
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (U a t)) ->
  finite_joint_continuous d (paper_main_projection_value K U F t).
Proof.
intro HU; unfold paper_main_projection_value; apply paper_main_projection_image_continuous;
  [exact HU|exact(pmgs_continuous _ _ _ _ _ _ HF)].
Qed.
Lemma paper_main_projection_velocity_continuous t :
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (U a t)) ->
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (DU a t)) ->
  finite_joint_continuous d (paper_main_projection_velocity K U DU DF t).
Proof.
intros HU HDU; unfold paper_main_projection_velocity; apply finite_joint_continuous_sum.
intros a Ha; apply in_seq in Ha; apply finite_joint_continuous_mult.
- apply paper_main_projection_image_continuous; [exact HU|].
  exact(pmgs_derivative_continuous _ _ _ _ _ _ HF a ltac:(lia)).
- apply HDU; lia.
Qed.
Lemma paper_main_projection_value_bound t :
  finite_polynomial_bound d C 0 (paper_main_projection_value K U F t).
Proof. apply paper_main_projection_image_bounded; exact(pmgs_bound _ _ _ _ _ _ HF). Qed.

Lemma paper_main_projection_velocity_bound t B p : 0 <= B ->
  (forall a, (a<K)%coq_nat -> finite_polynomial_bound d B p (DU a t)) ->
  finite_polynomial_bound d (INR K*(C*B)) p (paper_main_projection_velocity K U DU DF t).
Proof.
intros HB HDU; unfold paper_main_projection_velocity.
pose proof (proj1(pmgs_bound _ _ _ _ _ _ HF)) as HC.
rewrite -{1}(List.length_seq K 0).
apply finite_polynomial_bound_sum_uniform; [nra|].
intros a Ha; apply in_seq in Ha.
apply (finite_polynomial_bound_mult d C B 0 p).
- apply paper_main_projection_image_bounded; exact(pmgs_derivative_bound _ _ _ _ _ _ HF a ltac:(lia)).
- apply HDU; lia.
Qed.

Lemma paper_main_projection_acceleration_bound t B p : 0 <= B ->
  (forall a, (a<K)%coq_nat -> finite_polynomial_bound d B p (DU a t)) ->
  (forall a, (a<K)%coq_nat -> finite_polynomial_bound d B p (D2U a t)) ->
  finite_polynomial_bound d (INR K*(INR K*(C*B)*B+C*B)) (p+p)%coq_nat
    (paper_main_projection_acceleration K U DU D2U DF D2F t).
Proof.
intros HB HDU HD2U; unfold paper_main_projection_acceleration.
pose proof (proj1(pmgs_bound _ _ _ _ _ _ HF)) as HC.
pose proof (pos_INR K) as HK.
rewrite -{1}(List.length_seq K 0).
apply finite_polynomial_bound_sum_uniform;
  [apply Rplus_le_le_0_compat; repeat apply Rmult_le_pos; assumption|].
intros a Ha; apply in_seq in Ha; apply finite_polynomial_bound_add.
- apply (finite_polynomial_bound_mult d (INR K*(C*B)) B p p); [|apply HDU; lia].
  rewrite -{1}(List.length_seq K 0).
  apply finite_polynomial_bound_sum_uniform; [nra|].
  intros b Hb; apply in_seq in Hb; apply (finite_polynomial_bound_mult d C B 0 p).
  + apply paper_main_projection_image_bounded;
      exact(pmgs_second_bound _ _ _ _ _ _ HF a b ltac:(lia) ltac:(lia)).
  + apply HDU; lia.
- apply (finite_polynomial_bound_degree_monotone d (C*B) p (p+p)%coq_nat); [|lia].
  apply (finite_polynomial_bound_mult d C B 0 p).
  + apply paper_main_projection_image_bounded;
      exact(pmgs_derivative_bound _ _ _ _ _ _ HF a ltac:(lia)).
  + apply HD2U; lia.
Qed.

Theorem paper_main_projection_expectation_derive t rho B p :
  0 < rho -> 0 <= B ->
  (forall a s, (a<K)%coq_nat -> Rabs(s-t)<=rho -> finite_joint_continuous d (U a s)) ->
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (DU a t)) ->
  (forall a s xs, (a<K)%coq_nat -> Rabs(s-t)<=rho -> List.length xs=d ->
    @is_derive R R^o R^o s 1 (fun z => U a z xs) (DU a s xs)) ->
  (forall a s xs, (a<K)%coq_nat -> Rabs(s-t)<=rho -> List.length xs=d ->
    @is_derive R R^o R^o s 1 (fun z => DU a z xs) (D2U a s xs)) ->
  (forall a s, (a<K)%coq_nat -> Rabs(s-t)<=rho -> finite_polynomial_bound d B p (DU a s)) ->
  (forall a s, (a<K)%coq_nat -> Rabs(s-t)<=rho -> finite_polynomial_bound d B p (D2U a s)) ->
  gaussian_list_domain d (paper_main_projection_velocity K U DU DF t) /\
  @is_derive R R^o R^o t 1
    (fun s => gaussian_iterated_expectation d (paper_main_projection_value K U F s))
    (gaussian_iterated_expectation d (paper_main_projection_velocity K U DU DF t)).
Proof.
intros Hr HB HUc HDUc HU HDU HUb HDUb.
assert (Htt : Rabs(t-t)<=rho) by (rewrite (Rminus_diag_eq t t ltac:(reflexivity)) Rabs_R0; lra).
pose proof (finite_gaussian_parameter_differentiation d
  (paper_main_projection_value K U F) (paper_main_projection_velocity K U DU DF)
  (paper_main_projection_acceleration K U DU D2U DF D2F) t rho
  (INR K*(INR K*(C*B)*B+C*B)) (p+p)%coq_nat C 0 (INR K*(C*B)) p Hr) as H.
refine (proj2(H _ _ _ _ _ _ _)).
- intros s xs Hs Hxs; apply paper_main_projection_value_derive; intros a Ha; exact(HU a s xs Ha Hs Hxs).
- intros s xs Hs Hxs; apply paper_main_projection_velocity_derive;
    intros a Ha; [exact(HU a s xs Ha Hs Hxs)|exact(HDU a s xs Ha Hs Hxs)].
- intros s Hs; apply paper_main_projection_acceleration_bound; [exact HB| |];
    intros a Ha; [exact(HUb a s Ha Hs)|exact(HDUb a s Ha Hs)].
- intros s Hs; apply paper_main_projection_value_continuous; intros a Ha; exact(HUc a s Ha Hs).
- apply paper_main_projection_velocity_continuous; [intros a Ha; exact(HUc a t Ha Htt)|exact HDUc].
- intros s Hs; apply paper_main_projection_value_bound.
- apply paper_main_projection_velocity_bound; [exact HB|intros a Ha; exact(HUb a t Ha Htt)].
Qed.
End Path.
