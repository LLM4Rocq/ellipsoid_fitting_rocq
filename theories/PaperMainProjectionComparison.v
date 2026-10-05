(* Fixed-dimensional smooth comparison for orthogonal quadratic and Gaussian features. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights WeightedComparison
  GaussianCovarianceSums GaussianCovarianceLinear PaperMainDataFeatureMomentsCoordinates
  PaperMainGaussianSmoothCovariance PaperMainProjectionStein PaperMainProjectionRegular
  PaperMainProjectionImage PaperMainProjectionPath PaperMainProjectionMix PaperMainProjectionSpatial
  PaperMainProjectionAlgebra PaperMainProjectionError PaperMainProjectionInterpolation
  PaperMainProjectionVariance PaperMainProjectionProduct PaperMainProjectionErrorBound
  PaperMainProjectionEndpoints.
Open Scope R_scope.

Lemma paper_main_projection_endpoint_bound (g dg : R -> R) B :
  (g @ within (fun t : R => 0<=t<=1) (nbhs 0) --> g 0)%classic ->
  (g @ within (fun t : R => 0<=t<=1) (nbhs 1) --> g 1)%classic ->
  (forall t, 0<t<1 -> @is_derive R R^o R^o t 1 g (dg t)) ->
  (forall t, 0<t<1 -> Rabs(dg t)<=B) -> Rabs(g 1-g 0)<=B.
Proof.
intros H0 H1 HD HB.
assert (Hlinear : forall a, @is_derive R R^o R^o a 1 (fun t => B*t) B).
{ intro a; pose proof(is_derive_scal B (fun t => t) a 1 (is_derive_id_R a)) as H.
  rewrite Rmult_1_r in H; exact H. }
assert (HC : forall a, {for a, continuous (fun t => B*t)}).
{ intro a; apply (continuous_mult R (fun _ => B) (fun t => t)); [apply continuous_const|apply continuous_id]. }
assert (HP : g 1-g 0<=B).
{ pose proof(unit_interval_primitive_comparison g dg (fun t => B*t) (fun _ => B)
    H0 H1 (HC 0) (HC 1) HD (fun t _ => Hlinear t)
    ltac:(intros t Ht; pose proof(HB t Ht); pose proof(Rle_abs(dg t)); lra)) as HH; lra. }
assert (HN0 : ((fun t => -g t) @ within (fun t : R => 0<=t<=1) (nbhs 0) --> -g 0)%classic).
{ apply weighted_comparison_within_Reals; intros eps Heps.
  destruct(proj1(weighted_comparison_within_Reals g _ 0 (g 0)) H0 eps Heps) as [delta [Hd Hdel]].
  exists delta; split; [exact Hd|]; intros y Hy HDy.
  replace (-g y- -g 0) with (-(g y-g 0)) by ring; rewrite Rabs_Ropp; apply Hdel; assumption. }
assert (HN1 : ((fun t => -g t) @ within (fun t : R => 0<=t<=1) (nbhs 1) --> -g 1)%classic).
{ apply weighted_comparison_within_Reals; intros eps Heps.
  destruct(proj1(weighted_comparison_within_Reals g _ 1 (g 1)) H1 eps Heps) as [delta [Hd Hdel]].
  exists delta; split; [exact Hd|]; intros y Hy HDy.
  replace (-g y- -g 1) with (-(g y-g 1)) by ring; rewrite Rabs_Ropp; apply Hdel; assumption. }
pose proof(unit_interval_primitive_comparison (fun t => -g t) (fun t => -dg t) (fun t => B*t) (fun _ => B)
  HN0 HN1 (HC 0) (HC 1) (fun t Ht => is_derive_opp _ _ _ (HD t Ht)) (fun t _ => Hlinear t)
  ltac:(intros t Ht; pose proof(HB t Ht); pose proof(Rle_abs(-dg t)) as HH; rewrite Rabs_Ropp in HH; lra)) as HN.
apply Rabs_le; lra.
Qed.

Lemma paper_main_projection_regular_mix_continuous d K Q L F DF D2F C a :
  paper_main_gaussian_smooth_test K F DF D2F C 0 -> 0<=a<=1 ->
  (forall k, (k<K)%coq_nat -> pmdf_regular d (Q k)) ->
  (forall k, (k<K)%coq_nat -> pmdf_regular d (L k)) ->
  ((fun b => gaussian_iterated_expectation d (paper_main_projection_value K (paper_main_projection_mix Q L) F b)) @
    within (fun t : R => 0<=t<=1) (nbhs a) -->
    gaussian_iterated_expectation d (paper_main_projection_value K (paper_main_projection_mix Q L) F a))%classic.
Proof.
intros HF Ha HQ HL.
destruct(paper_main_projection_regular_uniform d (List.seq 0 K) Q
  ltac:(intros k Hk; apply HQ; apply in_seq in Hk; lia)) as [B [p [HB HBQ]]].
destruct(paper_main_projection_regular_uniform d (List.seq 0 K) L
  ltac:(intros k Hk; apply HL; apply in_seq in Hk; lia)) as [D [q [HD HDL]]].
apply (paper_main_projection_mix_continuous_within d K Q L F DF D2F C (B+D) (Nat.max p q) a HF ltac:(lra) Ha).
- intros k Hk; split; [exact(proj1(HQ k Hk))|].
  apply (paper_main_projection_bound_enlarge d B); [|lra].
  apply (finite_polynomial_bound_degree_monotone d B p); [apply HBQ; apply in_seq; lia|apply Nat.le_max_l].
- intros k Hk; split; [exact(proj1(HL k Hk))|].
  apply (paper_main_projection_bound_enlarge d D); [|lra].
  apply (finite_polynomial_bound_degree_monotone d D q); [apply HDL; apply in_seq; lia|apply Nat.le_max_r].
Qed.

Theorem paper_main_projection_smooth_comparison n K A c F DF D2F C eps S :
  paper_main_gaussian_smooth_test K F DF D2F C 0 ->
  (forall a i j, (a<K)%coq_nat -> (i<=n)%coq_nat -> (j<=n)%coq_nat -> A a i j=A a j i) ->
  (forall a b xs, (a<K)%coq_nat -> (b<K)%coq_nat ->
    paper_main_projection_cross (Datatypes.S n) (A a) (c b) xs=0) ->
  (forall a, (a<K)%coq_nat -> paper_main_projection_operator_bound (Datatypes.S n) (A a) eps) ->
  (forall a, (a<K)%coq_nat -> paper_main_projection_square_coefficients (Datatypes.S n) (A a)<=S^2) ->
  (forall a b, (a<K)%coq_nat -> (b<K)%coq_nat ->
    paper_main_projection_covariance (Datatypes.S n) (c a) (c b)=
      2*paper_main_projection_pairing (Datatypes.S n) (A a) (A b)) ->
  0<=eps -> 0<=S ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (fun xs => F(paper_main_projection_image K (fun a => paper_main_projection_quadratic (Datatypes.S n) (A a)) xs))-
    gaussian_iterated_expectation (Datatypes.S n)
    (fun xs => F(paper_main_projection_image K (fun a => linear_form (Datatypes.S n) (c a)) xs)))<=
    INR K*(INR K*(2*C*eps*S)).
Proof.
intros HF HA HX HO HN HC Heps HS.
set (Q := fun a => paper_main_projection_quadratic (Datatypes.S n) (A a)).
set (L := fun a => linear_form (Datatypes.S n) (c a)).
set (phi := fun t => gaussian_iterated_expectation (Datatypes.S n)
  (fun xs => F(paper_main_projection_image K (paper_main_projection_feature (Datatypes.S n) A c (sqrt t) (sqrt(1-t))) xs))).
set (dphi := fun t => gaussian_iterated_expectation (Datatypes.S n)
  (paper_main_projection_error (Datatypes.S n) K A c
    (paper_main_projection_feature (Datatypes.S n) A c (sqrt t) (sqrt(1-t))) D2F)).
assert (Hcont : forall a, 0<=a<=1 ->
  (phi @ within (fun t : R => 0<=t<=1) (nbhs a) --> phi a)%classic).
{ intros a Ha.
  assert (HE : (fun b => gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_projection_value K (paper_main_projection_mix Q L) F b))=phi).
  { apply functional_extensionality; intro b; unfold phi,paper_main_projection_value,Q,L.
    rewrite paper_main_projection_feature_mix; reflexivity. }
  rewrite <- HE; apply (paper_main_projection_regular_mix_continuous (Datatypes.S n) K Q L F DF D2F C a HF Ha);
    intros; [apply paper_main_projection_regular_quadratic|apply paper_main_projection_regular_linear]. }
assert (HD : forall t, 0<t<1 -> @is_derive R R^o R^o t 1 phi (dphi t)).
{ intros t Ht; exact(proj2(paper_main_projection_interpolation_derivative n K A c F DF D2F C t HF Ht HA HX)). }
assert (HB : forall t, 0<t<1 -> Rabs(dphi t)<=INR K*(INR K*(2*C*eps*S))).
{ intros t Ht; apply (proj2(paper_main_projection_error_bound n K A c
    (paper_main_projection_feature (Datatypes.S n) A c (sqrt t) (sqrt(1-t))) F DF D2F C eps S
    HF ltac:(intros; apply paper_main_projection_feature_regular) HA HO HN HC Heps HS)). }
pose proof(paper_main_projection_endpoint_bound phi dphi (INR K*(INR K*(2*C*eps*S)))
  (Hcont 0 ltac:(lra)) (Hcont 1 ltac:(lra)) HD HB) as HE.
assert (E1 : phi 1=gaussian_iterated_expectation (Datatypes.S n) (fun xs => F(paper_main_projection_image K Q xs))).
{ unfold phi; apply gaussian_iterated_expectation_ext; intros xs Hxs; f_equal.
  unfold paper_main_projection_image; apply map_ext; intro a.
  unfold paper_main_projection_feature,Q; replace (1-1) with 0 by ring; rewrite sqrt_1 sqrt_0; ring. }
assert (E0 : phi 0=gaussian_iterated_expectation (Datatypes.S n) (fun xs => F(paper_main_projection_image K L xs))).
{ unfold phi; apply gaussian_iterated_expectation_ext; intros xs Hxs; f_equal.
  unfold paper_main_projection_image; apply map_ext; intro a.
  unfold paper_main_projection_feature,L; replace (1-0) with 1 by ring; rewrite sqrt_0 sqrt_1; ring. }
rewrite E1 E0 in HE; exact HE.
Qed.
