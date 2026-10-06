(* A dimension-independent Hessian error bound from the actual quadratic moments. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianCovarianceSums
  GaussianProductDefinitions GaussianProduct GaussianFiniteSums
  PaperMainDataFeatureMomentsCoordinates PaperMainGaussianSmoothCovariance
  PaperMainGaussianSmoothCalculus PaperMainProjectionStein PaperMainProjectionRegular
  PaperMainProjectionImage PaperMainProjectionAlgebra PaperMainProjectionError
  PaperMainProjectionMomentBound PaperMainProjectionVariance PaperMainProjectionProduct.
Open Scope R_scope.

Theorem paper_main_projection_product_test_bound n A B G eps S C :
  (forall i j, (i<=n)%coq_nat -> (j<=n)%coq_nat -> A i j=A j i) ->
  paper_main_projection_operator_bound (Datatypes.S n) A eps ->
  paper_main_projection_square_coefficients (Datatypes.S n) B<=S^2 ->
  0<=eps -> 0<=S -> 0<=C -> pmdf_regular (Datatypes.S n) G ->
  (forall xs, List.length xs=Datatypes.S n -> Rabs(G xs)<=C) ->
  gaussian_iterated_integrable (Datatypes.S n) (fun xs =>
    paper_main_projection_quadratic (Datatypes.S n) (paper_main_projection_product (Datatypes.S n) A B) xs*G xs) /\
  Rabs(gaussian_iterated_expectation (Datatypes.S n) (fun xs =>
    paper_main_projection_quadratic (Datatypes.S n) (paper_main_projection_product (Datatypes.S n) A B) xs*G xs))<=2*C*eps*S.
Proof.
intros HA HO HB Heps HS HC HG HGB.
pose (Q := paper_main_projection_quadratic (Datatypes.S n) (paper_main_projection_product (Datatypes.S n) A B)).
assert (HRQ : pmdf_regular (Datatypes.S n) Q) by apply paper_main_projection_regular_quadratic.
assert (HIQG : gaussian_iterated_integrable (Datatypes.S n) (fun xs => Q xs*G xs)).
{ apply pmdf_regular_integrable; apply pmdf_regular_mult; assumption. }
assert (HIG : gaussian_iterated_integrable (Datatypes.S n) (fun xs => G xs^2)).
{ apply (gaussian_iterated_integrable_ext (Datatypes.S n) (fun xs => G xs*G xs));
    [intros; ring|apply pmdf_regular_integrable; apply pmdf_regular_mult; assumption]. }
destruct(paper_main_projection_quadratic_variance n (paper_main_projection_product (Datatypes.S n) A B)) as [HIQ HV].
pose proof(paper_main_projection_product_bound (Datatypes.S n) A B eps
  ltac:(intros; apply HA; lia) HO) as HP.
assert (HM : eps^2*paper_main_projection_square_coefficients (Datatypes.S n) B<=eps^2*S^2).
{ apply Rmult_le_compat_l; [apply pow2_ge_0|exact HB]. }
assert (HX : 0<= 2*eps*S) by nra.
assert (HV' : gaussian_iterated_expectation (Datatypes.S n) (fun xs => Q xs^2)<=(2*eps*S)^2).
{ fold Q in HV; pose proof(pow2_ge_0 eps); pose proof(pow2_ge_0 S).
  assert (HT : 0<=eps^2*S^2) by (apply Rmult_le_pos; apply pow2_ge_0).
  nra. }
pose proof(paper_main_projection_weighted_bound (Datatypes.S n) Q G ((2*eps*S)^2) C
  HIQ HIQG HIG (pow2_ge_0 _) HC HV' HGB) as HH.
assert (HE : sqrt((2*eps*S)^2)= 2*eps*S).
{ replace ((2*eps*S)^2) with ((2*eps*S)*(2*eps*S)) by ring; apply sqrt_square; exact HX. }
rewrite HE in HH; split; [exact HIQG|].
eapply Rle_trans; [exact HH|]; right; ring.
Qed.

Theorem paper_main_projection_error_bound n K A c U F DF D2F C eps S :
  paper_main_gaussian_smooth_test K F DF D2F C 0 ->
  (forall a, (a<K)%coq_nat -> pmdf_regular (Datatypes.S n) (U a)) ->
  (forall a i j, (a<K)%coq_nat -> (i<=n)%coq_nat -> (j<=n)%coq_nat -> A a i j=A a j i) ->
  (forall a, (a<K)%coq_nat -> paper_main_projection_operator_bound (Datatypes.S n) (A a) eps) ->
  (forall a, (a<K)%coq_nat -> paper_main_projection_square_coefficients (Datatypes.S n) (A a)<=S^2) ->
  (forall a b, (a<K)%coq_nat -> (b<K)%coq_nat ->
    paper_main_projection_covariance (Datatypes.S n) (c a) (c b)=
      2*paper_main_projection_pairing (Datatypes.S n) (A a) (A b)) ->
  0<=eps -> 0<=S ->
  gaussian_iterated_integrable (Datatypes.S n) (paper_main_projection_error (Datatypes.S n) K A c U D2F) /\
  Rabs(gaussian_iterated_expectation (Datatypes.S n) (paper_main_projection_error (Datatypes.S n) K A c U D2F))<=
    INR K*(INR K*(2*C*eps*S)).
Proof.
intros HF HU HA HO HN HC Heps HS.
assert (HC0 : 0<=C) by exact(proj1(pmgs_bound _ _ _ _ _ _ HF)).
set (T := fun a b xs => D2F a b (paper_main_projection_image K U xs)*
  (paper_main_projection_gram (Datatypes.S n) (A a) (A b) xs-
    paper_main_projection_covariance (Datatypes.S n) (c a) (c b)/2)).
assert (HT : forall a b, (a<K)%coq_nat -> (b<K)%coq_nat ->
  gaussian_iterated_integrable (Datatypes.S n) (T a b) /\
  Rabs(gaussian_iterated_expectation (Datatypes.S n) (T a b))<=2*C*eps*S).
{ intros a b Ha Hb.
  set (G := fun xs => D2F a b (paper_main_projection_image K U xs)).
  assert (HG : pmdf_regular (Datatypes.S n) G).
  { apply (paper_main_projection_regular_image (Datatypes.S n) K U (D2F a b) C HU).
    - exact(pmgs_second_continuous _ _ _ _ _ _ HF a b Ha Hb).
    - exact(pmgs_second_bound _ _ _ _ _ _ HF a b Ha Hb). }
  assert (HGB : forall xs, List.length xs=Datatypes.S n -> Rabs(G xs)<=C).
  { intros xs Hxs; exact(proj2(proj1(paper_main_polynomial_zero_bound K C (D2F a b))
      (pmgs_second_bound _ _ _ _ _ _ HF a b Ha Hb)) (paper_main_projection_image K U xs)
      (paper_main_projection_image_length K U xs)). }
  destruct(paper_main_projection_product_test_bound n (A a) (A b) G eps S C
    ltac:(intros i j Hi Hj; exact(HA a i j Ha Hi Hj)) (HO a Ha) (HN b Hb) Heps HS HC0 HG HGB) as [HI HB].
  assert (HE : forall xs, paper_main_projection_quadratic (Datatypes.S n)
    (paper_main_projection_product (Datatypes.S n) (A a) (A b)) xs*G xs=T a b xs).
  { intro xs; unfold T; rewrite (HC a b Ha Hb) -paper_main_projection_centered_product; unfold G; field. }
  split.
  - apply (gaussian_iterated_integrable_ext (Datatypes.S n) _ _ (fun xs _ => HE xs) HI).
  - rewrite <- (gaussian_iterated_expectation_ext (Datatypes.S n) _ _ (fun xs _ => HE xs)); exact HB. }
assert (HTI : forall a, (a<K)%coq_nat -> gaussian_iterated_integrable (Datatypes.S n)
  (fun xs => finite_sum (fun b => T a b xs) (List.seq 0 K))).
{ intros a Ha; apply (proj1(gaussian_iterated_finite_sum (Datatypes.S n) (List.seq 0 K) (T a)
    ltac:(intros b Hb; apply in_seq in Hb; exact(proj1(HT a b Ha ltac:(lia)))))). }
destruct(gaussian_iterated_finite_sum (Datatypes.S n) (List.seq 0 K)
  (fun a xs => finite_sum (fun b => T a b xs) (List.seq 0 K))
  ltac:(intros a Ha; apply HTI; apply in_seq in Ha; lia)) as [HI HE].
split; [exact HI|].
unfold paper_main_projection_error; fold T.
rewrite HE.
replace (INR K*(INR K*(2*C*eps*S))) with
  (INR(List.length(List.seq 0 K))*(INR K*(2*C*eps*S))) by (rewrite List.length_seq; reflexivity).
apply finite_sum_bound; intros a Ha; apply in_seq in Ha.
rewrite (proj2(gaussian_iterated_finite_sum (Datatypes.S n) (List.seq 0 K) (T a)
  ltac:(intros b Hb; apply in_seq in Hb; exact(proj1(HT a b ltac:(lia) ltac:(lia)))))).
replace (INR K*(2*C*eps*S)) with (INR(List.length(List.seq 0 K))*(2*C*eps*S)) by (rewrite List.length_seq; reflexivity).
apply finite_sum_bound; intros b Hb; apply in_seq in Hb.
exact(proj2(HT a b ltac:(lia) ltac:(lia))).
Qed.
