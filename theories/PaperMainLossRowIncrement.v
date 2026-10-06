(* The soft-minimum row increment of the loss, and the comparison of its
   means for centered quadratic forms and for the Gaussian linear forms of
   their GOE loadings.
   The increment (paper_main_loss_row_increment) is
     soft_min beta (fun j => f j + loss (a j + U j xs)) I - soft_min beta f I,
   with the loss 1 - exp(-t^2) of PaperMainTranslatedLoss.
   - paper_main_loss_row_increment_regular: it is continuous, and bounded
     by 1 in absolute value, when every U j is regular.
   - paper_main_loss_expected_difference: a pointwise bound B on |F - G|
     bounds the difference of the means by B.
   - paper_main_loss_row_expected_approximation: for beta, eta > 0, some
     degree k makes the mean of the increment eta-close to 1/beta times the
     mean of the row polynomial of degree k (PaperMainLossRowPolynomial),
     uniformly in d, f, I, a and U.
   - paper_main_loss_row_increment_comparison: there is C >= 0 such that,
     for symmetric T_j with cone operator norm at most eps and Frobenius
     norm at most S, the means of the increments for the centered
     quadratic forms x^T T_j x - Tr T_j (pmdf_quad) and for the linear
     forms of their GOE loadings differ by at most 2 eta + C eps S. The
     two polynomial means are compared by
     paper_main_loss_row_polynomial_comparison. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianExpectationContinuity GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainGaussianFeatureCoordinates PaperMainProjectionRegular PaperMainProjectionPublic
  GaussianCovarianceLinear PaperMainGordonContinuity PaperMainGaussianSmoothCalculus
  PaperMainTranslatedLoss PaperMainLossGibbs PaperMainLossLogPolynomial
  PaperMainLossSmoothFactor PaperMainLossReplica PaperMainLossRowPolynomial.
Open Scope R_scope.

Definition paper_main_loss_row_increment beta f I a (U : nat -> list R -> R) (xs : list R) :=
  soft_min beta (fun j => f j+paper_main_loss(a j+U j xs)) I-soft_min beta f I.

Lemma paper_main_loss_joint_continuous d a U : finite_joint_continuous d U ->
  finite_joint_continuous d (fun xs => paper_main_loss(a+U xs)).
Proof.
intro HU; unfold paper_main_loss.
apply finite_joint_continuous_minus; [apply finite_joint_continuous_constant|].
apply paper_main_gordon_joint_exp.
replace (fun xs => -(a+U xs)^2) with (fun xs => (-1)*((a+U xs)*(a+U xs)))
  by (apply functional_extensionality; intro xs; ring).
apply finite_joint_continuous_scale; apply finite_joint_continuous_mult;
  apply finite_joint_continuous_add; [apply finite_joint_continuous_constant|exact HU|
  apply finite_joint_continuous_constant|exact HU].
Qed.

Lemma paper_main_loss_row_increment_regular d beta f I a U : I<>nil -> 0<beta ->
  (forall j, In j I -> pmdf_regular d (U j)) ->
  pmdf_regular d (paper_main_loss_row_increment beta f I a U).
Proof.
intros HI Hb HU; split.
- unfold paper_main_loss_row_increment; apply finite_joint_continuous_minus;
    [|apply finite_joint_continuous_constant].
  unfold soft_min.
  replace (fun xs => -soft_max beta (fun j => -(f j+paper_main_loss(a j+U j xs))) I)
    with (fun xs => (-1)*soft_max beta (fun j => -(f j+paper_main_loss(a j+U j xs))) I)
    by (apply functional_extensionality; intro xs; ring).
  apply finite_joint_continuous_scale; apply paper_main_gordon_soft_max_continuous; [exact HI|].
  intros j Hj.
  replace (fun xs => -(f j+paper_main_loss(a j+U j xs))) with
    (fun xs => (-1)*(f j+paper_main_loss(a j+U j xs)))
    by (apply functional_extensionality; intro xs; ring).
  apply finite_joint_continuous_scale; apply finite_joint_continuous_add;
    [apply finite_joint_continuous_constant|].
  apply paper_main_loss_joint_continuous; exact(proj1(HU j Hj)).
- exists 1,0%nat; apply paper_main_polynomial_zero_bound; split; [lra|].
  intros xs Hxs; unfold paper_main_loss_row_increment.
  pose proof(paper_main_gibbs_row_increment_bounds beta f I
    (fun j => paper_main_loss(a j+U j xs)) Hb HI ltac:(intros; apply paper_main_loss_bounds)) as HH.
  apply Rabs_le; lra.
Qed.

Lemma paper_main_loss_expected_difference d F G B :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G ->
  (forall xs, List.length xs=d -> Rabs(F xs-G xs)<=B) ->
  Rabs(gaussian_iterated_expectation d F-gaussian_iterated_expectation d G)<=B.
Proof.
intros HF HG HB.
destruct(gaussian_iterated_difference d F G HF HG) as [HD HE].
assert (Hlo : -B<=gaussian_iterated_expectation d (fun xs => F xs-G xs)).
{ rewrite -(proj2(gaussian_iterated_constant d (-B))).
  apply gaussian_iterated_monotone; [exact(proj1(gaussian_iterated_constant d (-B)))|exact HD|].
  intros xs Hxs; pose proof(HB xs Hxs); pose proof(Rle_abs(F xs-G xs));
    pose proof(Rle_abs(-(F xs-G xs))) as Hneg; rewrite Rabs_Ropp in Hneg; lra. }
assert (Hhi : gaussian_iterated_expectation d (fun xs => F xs-G xs)<=B).
{ rewrite -(proj2(gaussian_iterated_constant d B)).
  apply gaussian_iterated_monotone; [exact HD|exact(proj1(gaussian_iterated_constant d B))|].
  intros xs Hxs; pose proof(HB xs Hxs); pose proof(Rle_abs(F xs-G xs)); lra. }
rewrite HE in Hlo,Hhi; apply Rabs_le; lra.
Qed.

Theorem paper_main_loss_row_expected_approximation beta eta : 0<beta -> 0<eta ->
  exists k, forall d f I a U, I<>nil ->
  (forall j, In j I -> pmdf_regular d (U j)) ->
  Rabs(gaussian_iterated_expectation d (paper_main_loss_row_increment beta f I a U)-
    /beta*gaussian_iterated_expectation d (paper_main_loss_row_polynomial beta f I k a U))<=eta.
Proof.
intros Hb He; destruct(paper_main_loss_row_poly_uniform beta eta Hb He) as [k Hk].
exists k; intros d f I a U HI HU.
assert (HP := paper_main_loss_row_polynomial_integrable d beta f I k a U HI ltac:(lra) HU).
rewrite -(proj2(gaussian_iterated_scale d _ (/beta) HP)).
apply paper_main_loss_expected_difference.
- apply pmdf_regular_integrable; apply paper_main_loss_row_increment_regular; assumption.
- exact(proj1(gaussian_iterated_scale d _ (/beta) HP)).
- intros xs Hxs.
  pose proof(Hk k ltac:(lia) f I (fun j => paper_main_loss(a j+U j xs)) HI
    ltac:(intros; apply paper_main_loss_bounds)) as HH.
  unfold paper_main_loss_row_increment,paper_main_loss_row_polynomial.
  replace (/beta*paper_main_loss_row_poly beta f I k (fun j => paper_main_loss(a j+U j xs)))
    with (paper_main_loss_row_poly beta f I k (fun j => paper_main_loss(a j+U j xs))/beta)
    by (unfold Rdiv; ring).
  lra.
Qed.

Theorem paper_main_loss_row_increment_comparison beta eta : 0<beta -> 0<eta ->
  exists C, 0<=C /\ forall n f I a (T : nat -> 'M[R]_(S n)) eps S,
  I<>nil -> 0<=eps -> 0<=S ->
  (forall j, In j I -> paper_main_symmetric (T j)) ->
  (forall j, In j I -> paper_main_cone_opnorm_le (T j) eps) ->
  (forall j, In j I -> paper_main_frobenius (T j)^2<=S^2) ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_loss_row_increment beta f I a (fun j => pmdf_quad n (T j)))-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_increment beta f I a (fun j =>
      linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j)))))<=
    2*eta+C*eps*S.
Proof.
intros Hb He.
destruct(paper_main_loss_row_expected_approximation beta eta Hb He) as [k Hk].
exists (/beta*paper_main_loss_row_constant beta k); split.
- apply Rmult_le_pos; [apply Rlt_le,Rinv_0_lt_compat; exact Hb|
    apply paper_main_loss_row_constant_nonnegative; lra].
- intros n f I a T eps S HI Heps HS HT HO HN.
  assert (HQ : forall j, In j I -> pmdf_regular (Datatypes.S n) (pmdf_quad n (T j)))
    by (intros; apply pmdf_quad_regular).
  assert (HG : forall j, In j I -> pmdf_regular (paper_main_symmetric_dimension n)
    (linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))
    by (intros; apply paper_main_projection_regular_linear).
  pose proof(Hk _ f I a _ HI HQ) as H1.
  pose proof(Hk _ f I a _ HI HG) as H2.
  pose proof(paper_main_loss_row_polynomial_comparison n beta f I k a T eps S
    HI ltac:(lra) Heps HS HT HO HN) as H3.
  set (X := gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_loss_row_increment beta f I a (fun j => pmdf_quad n (T j)))) in *.
  set (Y := gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_increment beta f I a (fun j => linear_form
      (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))) in *.
  set (P := gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_loss_row_polynomial beta f I k a (fun j => pmdf_quad n (T j)))) in *.
  set (Q := gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_polynomial beta f I k a (fun j => linear_form
      (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))) in *.
  replace (X-Y) with ((X-/beta*P)+/beta*(P-Q)- (Y-/beta*Q)) by ring.
  pose proof(Rabs_triang (X-/beta*P) (/beta*(P-Q))) as H4.
  pose proof(Rabs_triang ((X-/beta*P)+/beta*(P-Q)) (-(Y-/beta*Q))) as H5.
  rewrite Rabs_Ropp in H5.
  rewrite Rabs_mult (Rabs_pos_eq (/beta) ltac:(apply Rlt_le,Rinv_0_lt_compat; exact Hb)) in H4.
  pose proof(Rmult_le_compat_l (/beta) _ _ ltac:(apply Rlt_le,Rinv_0_lt_compat; exact Hb) H3).
  change (Rabs((X-/beta*P)+/beta*(P-Q)+ -(Y-/beta*Q))<=
    2*eta+(/beta*paper_main_loss_row_constant beta k)*eps*S); nra.
Qed.
