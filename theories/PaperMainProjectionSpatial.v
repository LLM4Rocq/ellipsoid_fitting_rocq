(* Spatial chain rules and actual Stein identities for mixed quadratic features. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  GaussianCovarianceLinear GaussianProductDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianCoordinateDerivativeDefinitions
  PaperMainDataFeatureMomentsCoordinates PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainProjectionStein PaperMainProjectionQuadratic
  PaperMainProjectionImage PaperMainProjectionRegular.
Open Scope R_scope.

Definition paper_main_projection_feature d (A : nat -> nat -> nat -> R)
  (c : nat -> nat -> R) u v a xs :=
  u*paper_main_projection_quadratic d (A a) xs+v*linear_form d (c a) xs.
Definition paper_main_projection_feature_gradient d (A : nat -> nat -> nat -> R)
  (c : nat -> nat -> R) u v i a xs :=
  (2*u)*linear_form d (A a i) xs+v*c a i.
Definition paper_main_projection_test_gradient K (U : nat -> list R -> R)
  (DU : nat -> nat -> list R -> R) (D2F : nat -> nat -> list R -> R) a i xs :=
  finite_sum (fun b => D2F a b (paper_main_projection_image K U xs)*DU i b xs) (List.seq 0 K).

Lemma paper_main_projection_feature_regular d A c u v a :
  pmdf_regular d (paper_main_projection_feature d A c u v a).
Proof.
unfold paper_main_projection_feature; apply pmdf_regular_add;
  apply pmdf_regular_scale; [apply paper_main_projection_regular_quadratic|apply paper_main_projection_regular_linear].
Qed.
Lemma paper_main_projection_feature_gradient_regular d A c u v i a :
  pmdf_regular d (paper_main_projection_feature_gradient d A c u v i a).
Proof.
unfold paper_main_projection_feature_gradient; apply pmdf_regular_add.
- apply pmdf_regular_scale; apply paper_main_projection_regular_linear.
- apply pmdf_regular_const.
Qed.
Lemma paper_main_projection_feature_coordinate d A c u v i a :
  (i<d)%coq_nat ->
  (forall j k, (j<d)%coq_nat -> (k<d)%coq_nat -> A a j k=A a k j) ->
  finite_coordinate_derivative d i (paper_main_projection_feature d A c u v a)
    (paper_main_projection_feature_gradient d A c u v i a).
Proof.
intros Hi HA; unfold paper_main_projection_feature,paper_main_projection_feature_gradient.
apply (paper_main_coordinate_derivative_value_ext d i _
  (fun xs => u*(2*linear_form d (A a i) xs)+v*c a i)).
- apply paper_main_coordinate_derivative_add; apply paper_main_coordinate_derivative_scale.
  + apply paper_main_projection_quadratic_symmetric_derive; assumption.
  + apply linear_form_coordinate_derivative; exact Hi.
- intros xs Hxs; ring.
Qed.

Section Test.
Variables (d K : nat) (U : nat -> list R -> R) (DU : nat -> nat -> list R -> R)
  (F : list R -> R) (DF : nat -> list R -> R) (D2F : nat -> nat -> list R -> R) (C : R).
Hypothesis HF : paper_main_gaussian_smooth_test K F DF D2F C 0.
Hypothesis HU : forall a, (a<K)%coq_nat -> pmdf_regular d (U a).
Hypothesis HDU : forall i a, (i<d)%coq_nat -> (a<K)%coq_nat -> pmdf_regular d (DU i a).

Lemma paper_main_projection_test_regular a : (a<K)%coq_nat ->
  pmdf_regular d (fun xs => DF a (paper_main_projection_image K U xs)).
Proof.
intro Ha; apply (paper_main_projection_regular_image d K U (DF a) C HU).
- exact(pmgs_derivative_continuous _ _ _ _ _ _ HF a Ha).
- exact(pmgs_derivative_bound _ _ _ _ _ _ HF a Ha).
Qed.
Lemma paper_main_projection_test_gradient_regular a i : (a<K)%coq_nat -> (i<d)%coq_nat ->
  pmdf_regular d (paper_main_projection_test_gradient K U DU D2F a i).
Proof.
intros Ha Hi; unfold paper_main_projection_test_gradient.
apply paper_main_projection_regular_sum; intros b Hb; apply in_seq in Hb.
apply pmdf_regular_mult; [|apply HDU; lia].
apply (paper_main_projection_regular_image d K U (D2F a b) C HU).
- exact(pmgs_second_continuous _ _ _ _ _ _ HF a b Ha ltac:(lia)).
- exact(pmgs_second_bound _ _ _ _ _ _ HF a b Ha ltac:(lia)).
Qed.
Lemma paper_main_projection_test_coordinate a i : (a<K)%coq_nat ->
  (forall b, (b<K)%coq_nat -> finite_coordinate_derivative d i (U b) (DU i b)) ->
  finite_coordinate_derivative d i (fun xs => DF a (paper_main_projection_image K U xs))
    (paper_main_projection_test_gradient K U DU D2F a i).
Proof.
intros Ha HD; unfold paper_main_projection_test_gradient.
apply paper_main_projection_image_coordinate; [| |exact HD].
- intros b Hb; exact(pmgs_second_derivative _ _ _ _ _ _ HF a b Ha Hb).
- intros b Hb; exact(pmgs_second_continuous _ _ _ _ _ _ HF a b Ha Hb).
Qed.
End Test.

Section MixedStein.
Variables (n K : nat) (A : nat -> nat -> nat -> R) (c : nat -> nat -> R) (u v : R)
  (F : list R -> R) (DF : nat -> list R -> R) (D2F : nat -> nat -> list R -> R) (C : R).
Hypothesis HF : paper_main_gaussian_smooth_test K F DF D2F C 0.
Hypothesis HA : forall a i j, (a<K)%coq_nat -> (i<=n)%coq_nat -> (j<=n)%coq_nat -> A a i j=A a j i.
Let U := paper_main_projection_feature (S n) A c u v.
Let DU := paper_main_projection_feature_gradient (S n) A c u v.
Let H a := fun xs => DF a (paper_main_projection_image K U xs).
Let DH a := paper_main_projection_test_gradient K U DU D2F a.

Theorem paper_main_projection_feature_quadratic_stein a : (a<K)%coq_nat ->
  gaussian_iterated_integrable (S n) (fun xs => paper_main_projection_quadratic (S n) (A a) xs*H a xs) /\
  gaussian_iterated_integrable (S n) (paper_main_projection_contraction (S n) (A a) (DH a)) /\
  gaussian_iterated_expectation (S n) (fun xs => paper_main_projection_quadratic (S n) (A a) xs*H a xs)=
    gaussian_iterated_expectation (S n) (paper_main_projection_contraction (S n) (A a) (DH a)).
Proof.
intro Ha; apply paper_main_projection_regular_quadratic_stein.
- apply (paper_main_projection_test_regular (S n) K U F DF D2F C HF); [intros; apply paper_main_projection_feature_regular|exact Ha].
- intros i Hi; apply (paper_main_projection_test_gradient_regular (S n) K U DU F DF D2F C HF);
    try assumption; try (intros; apply paper_main_projection_feature_regular);
    try (intros; apply paper_main_projection_feature_gradient_regular); lia.
- intros i Hi; apply (paper_main_projection_test_coordinate (S n) K U DU F DF D2F C HF a i Ha).
  intros b Hb; apply paper_main_projection_feature_coordinate; [lia|].
  intros j k Hj Hk; apply HA; lia.
Qed.

Theorem paper_main_projection_feature_linear_stein a : (a<K)%coq_nat ->
  gaussian_iterated_integrable (S n) (fun xs => linear_form (S n) (c a) xs*H a xs) /\
  gaussian_iterated_integrable (S n) (fun xs => finite_sum (fun i => c a i*DH a i xs) (List.seq 0 (S n))) /\
  gaussian_iterated_expectation (S n) (fun xs => linear_form (S n) (c a) xs*H a xs)=
    gaussian_iterated_expectation (S n) (fun xs => finite_sum (fun i => c a i*DH a i xs) (List.seq 0 (S n))).
Proof.
intro Ha; apply paper_main_projection_regular_linear_stein.
- apply (paper_main_projection_test_regular (S n) K U F DF D2F C HF); [intros; apply paper_main_projection_feature_regular|exact Ha].
- intros i Hi; apply (paper_main_projection_test_gradient_regular (S n) K U DU F DF D2F C HF);
    try assumption; try (intros; apply paper_main_projection_feature_regular);
    try (intros; apply paper_main_projection_feature_gradient_regular); lia.
- intros i Hi; apply (paper_main_projection_test_coordinate (S n) K U DU F DF D2F C HF a i Ha).
  intros b Hb; apply paper_main_projection_feature_coordinate; [lia|].
  intros j k Hj Hk; apply HA; lia.
Qed.
End MixedStein.
