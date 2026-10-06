(* Actual differentiation of a quadratic/Gaussian interpolation, with its error. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages
  Gaussian.IteratedExpectationDefinitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Joint.Definitions Data.FeatureMomentsCoordinates
  Gaussian.SmoothCovariance Projection.Stein Projection.Image Projection.Path
  Projection.Mix Projection.Regular Projection.Spatial Projection.Algebra
  Projection.Error.
Open Scope R_scope.

Theorem paper_main_projection_regular_mix_expectation d K Q L F DF D2F C t :
  paper_main_gaussian_smooth_test K F DF D2F C 0 -> 0<t<1 ->
  (forall a, (a<K)%coq_nat -> pmdf_regular d (Q a)) ->
  (forall a, (a<K)%coq_nat -> pmdf_regular d (L a)) ->
  gaussian_list_domain d (paper_main_projection_velocity K
    (paper_main_projection_mix Q L) (paper_main_projection_mix1 Q L) DF t) /\
  @is_derive R R^o R^o t 1
    (fun s => gaussian_iterated_expectation d
      (paper_main_projection_value K (paper_main_projection_mix Q L) F s))
    (gaussian_iterated_expectation d (paper_main_projection_velocity K
      (paper_main_projection_mix Q L) (paper_main_projection_mix1 Q L) DF t)).
Proof.
intros HF Ht HQ HL.
destruct(paper_main_projection_regular_uniform d (List.seq 0 K) Q
  ltac:(intros a Ha; apply HQ; apply in_seq in Ha; lia)) as [B [p [HB HBQ]]].
destruct(paper_main_projection_regular_uniform d (List.seq 0 K) L
  ltac:(intros a Ha; apply HL; apply in_seq in Ha; lia)) as [D [q [HD HDL]]].
apply (paper_main_projection_mix_expectation d K Q L F DF D2F C (B+D) (Nat.max p q) t HF ltac:(lra) Ht).
- intros a Ha; split; [exact(proj1(HQ a Ha))|].
  apply (paper_main_projection_bound_enlarge d B); [|lra].
  apply (finite_polynomial_bound_degree_monotone d B p); [apply HBQ; apply in_seq; lia|apply Nat.le_max_l].
- intros a Ha; split; [exact(proj1(HL a Ha))|].
  apply (paper_main_projection_bound_enlarge d D); [|lra].
  apply (finite_polynomial_bound_degree_monotone d D q); [apply HDL; apply in_seq; lia|apply Nat.le_max_r].
Qed.

Lemma paper_main_projection_feature_mix d A c t :
  (fun a => paper_main_projection_mix (fun b => paper_main_projection_quadratic d (A b))
    (fun b => linear_form d (c b)) a t)=paper_main_projection_feature d A c (sqrt t) (sqrt(1-t)).
Proof.
apply functional_extensionality; intro a; apply functional_extensionality; intro xs.
apply paper_main_projection_mix_formula.
Qed.

Theorem paper_main_projection_interpolation_derivative n K A c F DF D2F C t :
  paper_main_gaussian_smooth_test K F DF D2F C 0 -> 0<t<1 ->
  (forall a i j, (a<K)%coq_nat -> (i<=n)%coq_nat -> (j<=n)%coq_nat -> A a i j=A a j i) ->
  (forall a b xs, (a<K)%coq_nat -> (b<K)%coq_nat ->
    paper_main_projection_cross (S n) (A a) (c b) xs=0) ->
  gaussian_iterated_integrable (S n)
    (paper_main_projection_error (S n) K A c
      (paper_main_projection_feature (S n) A c (sqrt t) (sqrt(1-t))) D2F) /\
  @is_derive R R^o R^o t 1
    (fun s => gaussian_iterated_expectation (S n)
      (fun xs => F(paper_main_projection_image K
        (paper_main_projection_feature (S n) A c (sqrt s) (sqrt(1-s))) xs)))
    (gaussian_iterated_expectation (S n)
      (paper_main_projection_error (S n) K A c
        (paper_main_projection_feature (S n) A c (sqrt t) (sqrt(1-t))) D2F)).
Proof.
intros HF Ht HA HX.
pose (Q := fun a => paper_main_projection_quadratic (S n) (A a)).
pose (L := fun a => linear_form (S n) (c a)).
destruct(paper_main_projection_regular_mix_expectation (S n) K Q L F DF D2F C t HF Ht
  ltac:(intros; apply paper_main_projection_regular_quadratic)
  ltac:(intros; apply paper_main_projection_regular_linear)) as [HI HD].
assert (Hu : sqrt t<>0) by (pose proof(sqrt_lt_R0 t ltac:(lra)); lra).
assert (Hv : sqrt(1-t)<>0) by (pose proof(sqrt_lt_R0 (1-t) ltac:(lra)); lra).
destruct(paper_main_projection_mixed_error n K A c (sqrt t) (sqrt(1-t)) F DF D2F C HF HA Hu Hv HX) as [HEI HE].
split; [exact HEI|].
assert (EV : paper_main_projection_velocity K (paper_main_projection_mix Q L)
  (paper_main_projection_mix1 Q L) DF t=
  paper_main_projection_mixed_velocity (S n) K A c (sqrt t) (sqrt(1-t)) DF).
{ apply functional_extensionality; intro xs.
  unfold paper_main_projection_velocity,paper_main_projection_mixed_velocity,Q,L.
  rewrite paper_main_projection_feature_mix.
  apply finite_sum_ext; intros a Ha; rewrite paper_main_projection_mix1_formula; ring. }
rewrite EV HE in HD.
apply (is_derive_ext (fun s => gaussian_iterated_expectation (S n)
  (paper_main_projection_value K (paper_main_projection_mix Q L) F s)) _ t _); [|exact HD].
intro s; unfold paper_main_projection_value,Q,L; rewrite paper_main_projection_feature_mix; reflexivity.
Qed.
