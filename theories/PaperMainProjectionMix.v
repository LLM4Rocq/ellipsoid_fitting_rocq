(* Actual square-root interpolation of two polynomial feature families. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge GaussianProductDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinatePolynomialContinuity
  GaussianCovariancePath JointDefinitions PaperMainGaussianSmoothCovariance PaperMainProjectionPath.
Open Scope R_scope.

Definition paper_main_projection_mixcoef t k :=
  gaussian_covariance_coef 1 1 (fun _ _ => 1) (fun _ _ => 1) t 0 k.
Definition paper_main_projection_mixcoef1 t k :=
  gaussian_covariance_dcoef 1 1 (fun _ _ => 1) (fun _ _ => 1) t 0 k.
Definition paper_main_projection_mixcoef2 t k :=
  gaussian_covariance_ddcoef 1 1 (fun _ _ => 1) (fun _ _ => 1) t 0 k.
Definition paper_main_projection_mix (Q L : nat -> list R -> R) a t xs :=
  paper_main_projection_mixcoef t 0*Q a xs+paper_main_projection_mixcoef t 1*L a xs.
Definition paper_main_projection_mix1 (Q L : nat -> list R -> R) a t xs :=
  paper_main_projection_mixcoef1 t 0*Q a xs+paper_main_projection_mixcoef1 t 1*L a xs.
Definition paper_main_projection_mix2 (Q L : nat -> list R -> R) a t xs :=
  paper_main_projection_mixcoef2 t 0*Q a xs+paper_main_projection_mixcoef2 t 1*L a xs.

Lemma paper_main_projection_mix_formula Q L a t xs :
  paper_main_projection_mix Q L a t xs=sqrt t*Q a xs+sqrt(1-t)*L a xs.
Proof. unfold paper_main_projection_mix,paper_main_projection_mixcoef,gaussian_covariance_coef; simpl; ring. Qed.
Lemma paper_main_projection_mix1_formula Q L a t xs :
  paper_main_projection_mix1 Q L a t xs=Q a xs/(2*sqrt t)-L a xs/(2*sqrt(1-t)).
Proof. unfold paper_main_projection_mix1,paper_main_projection_mixcoef1,gaussian_covariance_dcoef; simpl; unfold Rdiv; ring. Qed.
Lemma paper_main_projection_mix_derive Q L a t xs : 0<t<1 ->
  @is_derive R R^o R^o t 1 (fun s => paper_main_projection_mix Q L a s xs)
    (paper_main_projection_mix1 Q L a t xs).
Proof.
intro Ht; unfold paper_main_projection_mix,paper_main_projection_mix1.
apply is_derive_plus; apply is_derive_scal_l; apply gaussian_covariance_coef_derive; exact Ht.
Qed.
Lemma paper_main_projection_mix1_derive Q L a t xs : 0<t<1 ->
  @is_derive R R^o R^o t 1 (fun s => paper_main_projection_mix1 Q L a s xs)
    (paper_main_projection_mix2 Q L a t xs).
Proof.
intro Ht; unfold paper_main_projection_mix1,paper_main_projection_mix2.
apply is_derive_plus; apply is_derive_scal_l; apply gaussian_covariance_dcoef_derive; exact Ht.
Qed.

Lemma paper_main_projection_bound_enlarge d A B p F :
  finite_polynomial_bound d A p F -> A<=B -> finite_polynomial_bound d B p F.
Proof.
intros [HA HF] HAB; split; [lra|].
intros xs Hxs; eapply Rle_trans; [apply HF; exact Hxs|].
apply Rmult_le_compat_r; [apply gaussian_coordinate_product_weight_nonnegative|exact HAB].
Qed.
Lemma paper_main_projection_two_bound d A p Q L u v M :
  finite_polynomial_bound d A p Q -> finite_polynomial_bound d A p L ->
  Rabs u<=M -> Rabs v<=M ->
  finite_polynomial_bound d (2*M*A) p (fun xs => u*Q xs+v*L xs).
Proof.
intros HQ HL Hu Hv.
apply (paper_main_projection_bound_enlarge d (Rabs u*A+Rabs v*A)).
- apply finite_polynomial_bound_add; apply finite_polynomial_bound_scale; assumption.
- pose proof(proj1 HQ); nra.
Qed.

Lemma paper_main_projection_mix_local_coeff t : 0<t<1 ->
  exists rho M, 0<rho /\ 0<=M /\ forall s k, Rabs(s-t)<=rho -> (k<2)%coq_nat ->
    0<s<1 /\ Rabs(paper_main_projection_mixcoef1 s k)<=M /\
      Rabs(paper_main_projection_mixcoef2 s k)<=M.
Proof.
intro Ht.
set (rho := Rmin t (1-t)/2).
assert (Hr : 0<rho) by (unfold rho; apply Rdiv_lt_0_compat; [apply Rmin_pos; lra|lra]).
assert (Hrt : rho<=t/2) by (unfold rho; pose proof(Rmin_l t (1-t)); lra).
assert (Hru : rho<=(1-t)/2) by (unfold rho; pose proof(Rmin_r t (1-t)); lra).
set (lo := t-rho); set (hi := t+rho).
set (M1 := /(2*sqrt lo)+/(2*sqrt(1-hi))).
set (M2 := /(4*(sqrt lo*sqrt lo*sqrt lo))+
  /(4*(sqrt(1-hi)*sqrt(1-hi)*sqrt(1-hi)))).
exists rho,(1+Rabs M1+Rabs M2); split; [exact Hr|]; split.
- pose proof(Rabs_pos M1); pose proof(Rabs_pos M2); lra.
- intros s k Hs Hk.
  apply Rabs_le_between in Hs.
  assert (Hlo : 0<lo) by (unfold lo; lra).
  assert (Hhi : hi<1) by (unfold hi; lra).
  assert (Hrange : lo<=s<=hi) by (unfold lo,hi; lra).
  pose proof(gaussian_covariance_dcoef_bound 1 1 (fun _ _ => 1) (fun _ _ => 1)
    1 lo hi s 0 k ltac:(lra) Hlo Hhi Hrange Hk
    ltac:(intros; rewrite Rabs_R1; lra) ltac:(intros; rewrite Rabs_R1; lra)) as H1.
  pose proof(gaussian_covariance_ddcoef_bound 1 1 (fun _ _ => 1) (fun _ _ => 1)
    1 lo hi s 0 k ltac:(lra) Hlo Hhi Hrange Hk
    ltac:(intros; rewrite Rabs_R1; lra) ltac:(intros; rewrite Rabs_R1; lra)) as H2.
  fold M1 in H1; fold M2 in H2.
  fold paper_main_projection_mixcoef1 in H1; fold paper_main_projection_mixcoef2 in H2.
  pose proof(Rle_abs M1); pose proof(Rle_abs M2);
    pose proof(Rabs_pos M1); pose proof(Rabs_pos M2).
  assert (Hs01 : 0<s<1) by (unfold lo,hi in Hrange,Hlo,Hhi; lra).
  split; [exact Hs01|].
  split.
  + eapply Rle_trans; [exact H1|]; fold M1; lra.
  + eapply Rle_trans; [exact H2|]; fold M2; lra.
Qed.

Theorem paper_main_projection_mix_expectation d K Q L F DF D2F C A p t :
  paper_main_gaussian_smooth_test K F DF D2F C 0 ->
  0<=A -> 0<t<1 ->
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (Q a) /\ finite_polynomial_bound d A p (Q a)) ->
  (forall a, (a<K)%coq_nat -> finite_joint_continuous d (L a) /\ finite_polynomial_bound d A p (L a)) ->
  gaussian_list_domain d (paper_main_projection_velocity K
    (paper_main_projection_mix Q L) (paper_main_projection_mix1 Q L) DF t) /\
  @is_derive R R^o R^o t 1
    (fun s => gaussian_iterated_expectation d
      (paper_main_projection_value K (paper_main_projection_mix Q L) F s))
    (gaussian_iterated_expectation d (paper_main_projection_velocity K
      (paper_main_projection_mix Q L) (paper_main_projection_mix1 Q L) DF t)).
Proof.
intros HF HA Ht HQ HL.
destruct(paper_main_projection_mix_local_coeff t Ht) as [rho [M [Hr [HM Hbound]]]].
apply (paper_main_projection_expectation_derive d K
  (paper_main_projection_mix Q L) (paper_main_projection_mix1 Q L)
  (paper_main_projection_mix2 Q L) F DF D2F C HF t rho (2*M*A) p); try assumption.
- nra.
- intros a s Ha Hs; unfold paper_main_projection_mix.
  apply finite_joint_continuous_add; apply finite_joint_continuous_scale;
    [exact(proj1(HQ a Ha))|exact(proj1(HL a Ha))].
- intros a Ha; unfold paper_main_projection_mix1.
  apply finite_joint_continuous_add; apply finite_joint_continuous_scale;
    [exact(proj1(HQ a Ha))|exact(proj1(HL a Ha))].
- intros a s xs Ha Hs Hxs; apply paper_main_projection_mix_derive;
    exact(proj1(Hbound s 0%nat Hs ltac:(lia))).
- intros a s xs Ha Hs Hxs; apply paper_main_projection_mix1_derive;
    exact(proj1(Hbound s 0%nat Hs ltac:(lia))).
- intros a s Ha Hs; unfold paper_main_projection_mix1.
  apply paper_main_projection_two_bound; [exact(proj2(HQ a Ha))|exact(proj2(HL a Ha))| |].
  + exact(proj1(proj2(Hbound s 0%nat Hs ltac:(lia)))).
  + exact(proj1(proj2(Hbound s 1%nat Hs ltac:(lia)))).
- intros a s Ha Hs; unfold paper_main_projection_mix2.
  apply paper_main_projection_two_bound; [exact(proj2(HQ a Ha))|exact(proj2(HL a Ha))| |].
  + exact(proj2(proj2(Hbound s 0%nat Hs ltac:(lia)))).
  + exact(proj2(proj2(Hbound s 1%nat Hs ltac:(lia)))).
Qed.
