(* Continuity through the endpoints for bounded smooth nonlinear features. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  GaussianProductDefinitions GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCovarianceDefinitions GaussianCovarianceEndpoints
  GaussianExpectationContinuity GaussianCoordinatePolynomialContinuity
  PaperMainGaussianSmoothCovariance PaperMainProjectionImage PaperMainProjectionPath
  PaperMainProjectionMix.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_projection_mix_scalar_path K Q L t xs :
  paper_main_projection_image K (fun a => paper_main_projection_mix Q L a t) xs=
    gaussian_covariance_path K 1 1 (fun a _ => Q a xs) (fun a _ => L a xs) t [1;1].
Proof.
unfold paper_main_projection_image,gaussian_covariance_path; apply map_ext; intro a.
rewrite paper_main_projection_mix_formula; unfold gaussian_covariance_row; simpl; ring.
Qed.

Lemma paper_main_projection_mix_difference d K Q L F DF D2F C A p a b :
  paper_main_gaussian_smooth_test K F DF D2F C 0 -> 0<=A -> 0<=a<=1 -> 0<=b<=1 ->
  (forall k, (k<K)%coq_nat -> finite_polynomial_bound d A p (Q k)) ->
  (forall k, (k<K)%coq_nat -> finite_polynomial_bound d A p (L k)) ->
  finite_polynomial_bound d
    ((8*INR K*C*A)*(Rabs(sqrt b-sqrt a)+Rabs(sqrt(1-b)-sqrt(1-a)))) p
    (fun xs => paper_main_projection_value K (paper_main_projection_mix Q L) F b xs-
      paper_main_projection_value K (paper_main_projection_mix Q L) F a xs).
Proof.
intros HF HA Ha Hb HQ HL.
assert (HC : 0<=C) by exact(proj1(pmgs_bound _ _ _ _ _ _ HF)).
split.
- repeat apply Rmult_le_pos; try assumption; try apply pos_INR; try lra.
  pose proof(Rabs_pos(sqrt b-sqrt a)); pose proof(Rabs_pos(sqrt(1-b)-sqrt(1-a))); lra.
- intros xs Hxs.
  set (M := A*gaussian_coordinate_product_weight p xs).
  assert (HM : 0<=M) by (unfold M; apply Rmult_le_pos; [exact HA|apply gaussian_coordinate_product_weight_nonnegative]).
  pose proof(gaussian_covariance_path_difference_bound K 1 1
    (fun k _ => Q k xs) (fun k _ => L k xs) M F DF C 0 a b [1;1]
    HM ltac:(intros k j Hk Hj; exact(proj2(HQ k Hk) xs Hxs))
    ltac:(intros k j Hk Hj; exact(proj2(HL k Hk) xs Hxs))
    Ha Hb ltac:(reflexivity)
    (pmgs_derivative _ _ _ _ _ _ HF) (pmgs_derivative_continuous _ _ _ _ _ _ HF)
    (pmgs_derivative_bound _ _ _ _ _ _ HF)) as HH.
  rewrite -!paper_main_projection_mix_scalar_path in HH.
  cbn [Nat.mul Nat.add gaussian_coordinate_product_weight gaussian_coordinate_weight pow] in HH.
  rewrite Rabs_R1 in HH.
  unfold paper_main_projection_value.
  eapply Rle_trans; [exact HH|]; right; unfold M; replace (INR 2) with 2 by (simpl; ring); ring.
Qed.

Theorem paper_main_projection_mix_continuous_within d K Q L F DF D2F C A p a :
  paper_main_gaussian_smooth_test K F DF D2F C 0 -> 0<=A -> 0<=a<=1 ->
  (forall k, (k<K)%coq_nat -> finite_joint_continuous d (Q k) /\ finite_polynomial_bound d A p (Q k)) ->
  (forall k, (k<K)%coq_nat -> finite_joint_continuous d (L k) /\ finite_polynomial_bound d A p (L k)) ->
  ((fun b => gaussian_iterated_expectation d (paper_main_projection_value K (paper_main_projection_mix Q L) F b)) @
    within (fun t : R => 0<=t<=1) (nbhs a) -->
    gaussian_iterated_expectation d (paper_main_projection_value K (paper_main_projection_mix Q L) F a))%classic.
Proof.
intros HF HA Ha HQ HL.
set (Cm := 8*INR K*C*A).
assert (Hbase : finite_polynomial_bound d C 0
  (paper_main_projection_value K (paper_main_projection_mix Q L) F a)).
{ apply (paper_main_projection_value_bound d K (paper_main_projection_mix Q L) F DF D2F C HF a). }
assert (Hcont : exists eta, 0<eta /\ forall b, 0<=b<=1 -> Rabs(b-a)<eta ->
  finite_joint_continuous d (paper_main_projection_value K (paper_main_projection_mix Q L) F b)).
{ exists 1; split; [lra|]; intros b Hb Hba.
  apply (paper_main_projection_value_continuous d K (paper_main_projection_mix Q L) F DF D2F C HF b).
  intros k Hk; unfold paper_main_projection_mix; apply finite_joint_continuous_add;
    apply finite_joint_continuous_scale; [exact(proj1(HQ k Hk))|exact(proj1(HL k Hk))]. }
assert (Hc : {for a, continuous (fun b => Cm*(Rabs(sqrt b-sqrt a)+Rabs(sqrt(1-b)-sqrt(1-a))))}).
{ apply gaussian_covariance_modulus_continuous; exact Ha. }
assert (Hca : Cm*(Rabs(sqrt a-sqrt a)+Rabs(sqrt(1-a)-sqrt(1-a)))=0).
{ replace (sqrt a-sqrt a) with 0 by ring.
  replace (sqrt(1-a)-sqrt(1-a)) with 0 by ring.
  rewrite Rabs_R0; ring. }
assert (HD : exists eta, 0<eta /\ forall b, 0<=b<=1 -> Rabs(b-a)<eta ->
  finite_polynomial_bound d (Cm*(Rabs(sqrt b-sqrt a)+Rabs(sqrt(1-b)-sqrt(1-a)))) p
    (fun xs => paper_main_projection_value K (paper_main_projection_mix Q L) F b xs-
      paper_main_projection_value K (paper_main_projection_mix Q L) F a xs)).
{ exists 1; split; [lra|]; intros b Hb Hba.
  apply (paper_main_projection_mix_difference d K Q L F DF D2F C A p a b HF HA Ha Hb).
  - intros k Hk; exact(proj2(HQ k Hk)).
  - intros k Hk; exact(proj2(HL k Hk)). }
exact (proj1(gaussian_iterated_expectation_continuous_modulus_within d
  (fun b => paper_main_projection_value K (paper_main_projection_mix Q L) F b)
  (fun t : R => 0<=t<=1) a C 0 p
  (fun b => Cm*(Rabs(sqrt b-sqrt a)+Rabs(sqrt(1-b)-sqrt(1-a))))
  Ha Hbase Hcont Hc Hca HD)).
Qed.
