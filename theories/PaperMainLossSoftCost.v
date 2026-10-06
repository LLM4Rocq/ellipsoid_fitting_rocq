(* The soft minimum of the losses of one row, and its expectation.
   - paper_main_loss_soft_regular: for continuous costs F_j bounded by C,
     xs |-> soft_min beta (j |-> f_j + F_j xs) is regular (pmdf_regular).
   - paper_main_loss_row_value: the one-row value
     soft_min beta (j |-> f_j + loss(a_j + U_j xs)) over j in I.
   - paper_main_loss_row_value_integral: for regular U_j it is integrable,
     and its expectation is that of the row increment
     paper_main_loss_row_increment plus soft_min beta f.
   - paper_main_loss_row_value_comparison: for beta, eta > 0 there is C
     such that, for symmetric T_j with operator norm at most eps
     (paper_main_cone_opnorm_le) and |T_j|_F <= S, the expectations of the
     row value with the centered quadratic forms pmdf_quad n (T_j) of a
     Gaussian vector and with the linear forms of the GOE loadings
     paper_main_projection_goe_loading n (T_j) differ by at most
     2 eta + C eps S. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainGaussianFeatureCoordinates PaperMainProjectionRegular PaperMainProjectionPublic
  GaussianCovarianceLinear PaperMainGordonContinuity PaperMainGaussianSmoothCalculus PaperMainSoftLipschitz
  PaperMainTranslatedLoss PaperMainLossRowIncrement.
Open Scope R_scope.

Theorem paper_main_loss_soft_regular d beta f I (F : nat -> list R -> R) C :
  I<>nil -> 0<beta -> 0<=C ->
  (forall j, In j I -> finite_joint_continuous d (F j)) ->
  (forall j xs, In j I -> List.length xs=d -> Rabs(F j xs)<=C) ->
  pmdf_regular d (fun xs => soft_min beta (fun j => f j+F j xs) I).
Proof.
intros HI Hb Hpos HC HB; split.
- unfold soft_min.
  replace (fun xs => -soft_max beta (fun j => -(f j+F j xs)) I)
    with (fun xs => (-1)*soft_max beta (fun j => -(f j+F j xs)) I)
    by (apply functional_extensionality; intros; ring).
  apply finite_joint_continuous_scale; apply paper_main_gordon_soft_max_continuous; [exact HI|].
  intros j Hj; replace (fun xs => -(f j+F j xs))
    with (fun xs => (-1)*(f j+F j xs)) by (apply functional_extensionality; intros; ring).
  apply finite_joint_continuous_scale; apply finite_joint_continuous_add;
    [apply finite_joint_continuous_constant|apply HC; exact Hj].
- exists (Rabs(soft_min beta f I)+C),0%nat.
  apply paper_main_polynomial_zero_bound; split; [pose proof(Rabs_pos(soft_min beta f I)); lra|].
  intros xs Hxs.
  assert (Hdiff : Rabs(soft_min beta (fun j => f j+F j xs) I-soft_min beta f I)<=C).
  { apply paper_main_soft_min_lipschitz; [exact Hb|exact HI|].
    intros j Hj; replace (f j+F j xs-f j) with (F j xs) by ring; apply HB; assumption. }
  pose proof(Rabs_triang (soft_min beta (fun j => f j+F j xs) I-soft_min beta f I) (soft_min beta f I)) as HH.
  replace (soft_min beta (fun j => f j+F j xs) I-soft_min beta f I+soft_min beta f I)
    with (soft_min beta (fun j => f j+F j xs) I) in HH by ring; lra.
Qed.

Definition paper_main_loss_row_value beta f I a (U : nat -> list R -> R) xs :=
  soft_min beta (fun j => f j+paper_main_loss(a j+U j xs)) I.

Theorem paper_main_loss_row_value_integral d beta f I a U : I<>nil -> 0<beta ->
  (forall j, In j I -> pmdf_regular d (U j)) ->
  gaussian_iterated_integrable d (paper_main_loss_row_value beta f I a U) /\
  gaussian_iterated_expectation d (paper_main_loss_row_value beta f I a U)=
    gaussian_iterated_expectation d (paper_main_loss_row_increment beta f I a U)+soft_min beta f I.
Proof.
intros HI Hb HU.
assert (HR := pmdf_regular_integrable (paper_main_loss_row_increment_regular d beta f I a U HI Hb HU)).
pose proof(gaussian_iterated_add d _ (fun _ => soft_min beta f I) HR
  (proj1(gaussian_iterated_constant d (soft_min beta f I)))) as [HA HE].
assert (EE : (fun xs => paper_main_loss_row_increment beta f I a U xs+soft_min beta f I)=
  paper_main_loss_row_value beta f I a U).
{ apply functional_extensionality; intro xs; unfold paper_main_loss_row_increment,paper_main_loss_row_value; ring. }
rewrite EE in HA,HE; split; [exact HA|].
rewrite (proj2(gaussian_iterated_constant d (soft_min beta f I))) in HE; exact HE.
Qed.

Theorem paper_main_loss_row_value_comparison beta eta : 0<beta -> 0<eta ->
  exists C, 0<=C /\ forall n f I a (T : nat -> 'M[R]_(S n)) eps S,
  I<>nil -> 0<=eps -> 0<=S ->
  (forall j, In j I -> paper_main_symmetric (T j)) ->
  (forall j, In j I -> paper_main_cone_opnorm_le (T j) eps) ->
  (forall j, In j I -> paper_main_frobenius (T j)^2<=S^2) ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_loss_row_value beta f I a (fun j => pmdf_quad n (T j)))-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_value beta f I a (fun j =>
      linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j)))))<=
    2*eta+C*eps*S.
Proof.
intros Hb He; destruct(paper_main_loss_row_increment_comparison beta eta Hb He) as [C [HC HH]].
exists C; split; [exact HC|]; intros n f I a T eps S HI Heps HS HT HO HN.
assert (HQ : forall j, In j I -> pmdf_regular (Datatypes.S n) (pmdf_quad n (T j)))
  by (intros; apply pmdf_quad_regular).
assert (HG : forall j, In j I -> pmdf_regular (paper_main_symmetric_dimension n)
  (linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))
  by (intros; apply paper_main_projection_regular_linear).
rewrite (proj2(paper_main_loss_row_value_integral _ _ _ _ _ _ HI Hb HQ))
  (proj2(paper_main_loss_row_value_integral _ _ _ _ _ _ HI Hb HG)).
replace (gaussian_iterated_expectation (Datatypes.S n)
  (paper_main_loss_row_increment beta f I a (fun j => pmdf_quad n (T j)))+soft_min beta f I-
  (gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_increment beta f I a (fun j =>
      linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))+soft_min beta f I))
  with (gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_loss_row_increment beta f I a (fun j => pmdf_quad n (T j)))-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_increment beta f I a (fun j =>
      linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))) by ring.
apply HH; assumption.
Qed.
