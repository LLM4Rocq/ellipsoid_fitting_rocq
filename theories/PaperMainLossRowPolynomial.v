(* Uniform finite-prior row-polynomial comparison for actual Gaussian laws. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCovarianceLinear PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainGaussianFeatureCoordinates PaperMainProjectionRegular PaperMainProjectionPublic
  PaperMainTranslatedLoss PaperMainLossGibbs PaperMainLossLogPolynomial
  PaperMainLossSmoothFactor PaperMainLossReplica PaperMainLossReplicaIntegral PaperMainLossReplicaComparison.
Open Scope R_scope.

Definition paper_main_loss_row_polynomial beta f I k a (U : nat -> list R -> R) (xs : list R) :=
  paper_main_loss_row_poly beta f I k (fun j => paper_main_loss(a j+U j xs)).

Lemma paper_main_loss_row_polynomial_step beta f I k a U xs : I<>nil ->
  paper_main_loss_row_polynomial beta f I (S k) a U xs=
  paper_main_loss_row_polynomial beta f I k a U xs+
  /INR(S k)*paper_main_loss_replica (-beta) f I (S k)
    (fun js => paper_main_loss_product (fun j => paper_main_loss_factor beta (a j) (U j xs)) js).
Proof.
intro HI; unfold paper_main_loss_row_polynomial.
rewrite (paper_main_loss_row_poly_step _ _ _ _ _ HI).
unfold paper_main_loss_factor,Rdiv; cbv beta.
apply f_equal2; [reflexivity|].
rewrite Rmult_comm; apply f_equal2; [reflexivity|].
apply paper_main_loss_replica_ext; intros; reflexivity.
Qed.

Lemma paper_main_loss_replicated_integrable d beta c f I k a U : 0<=beta ->
  (forall j, In j I -> pmdf_regular d (U j)) ->
  gaussian_iterated_integrable d (fun xs => paper_main_loss_replica c f I k
    (fun js => paper_main_loss_product (fun j => paper_main_loss_factor beta (a j) (U j xs)) js)).
Proof.
intros Hb HU.
assert (HR : forall js, List.length js=k -> List.Forall (fun j => In j I) js ->
  gaussian_iterated_integrable d (fun xs => paper_main_loss_product
    (fun j => paper_main_loss_factor beta (a j) (U j xs)) js)).
{ intros js Hlen Hjs; apply pmdf_regular_integrable; apply paper_main_loss_product_regular; [exact Hb|].
  intros j Hj; apply HU; rewrite Forall_forall in Hjs; apply Hjs; exact Hj. }
exact(proj1(paper_main_loss_replica_integral d c f I k _ HR)).
Qed.

Theorem paper_main_loss_row_polynomial_integrable d beta f I k a U : I<>nil -> 0<=beta ->
  (forall j, In j I -> pmdf_regular d (U j)) ->
  gaussian_iterated_integrable d (paper_main_loss_row_polynomial beta f I k a U).
Proof.
intros HI Hb HU; induction k as [|k IH].
- exact(proj1(gaussian_iterated_constant d 0)).
- assert (HR := paper_main_loss_replicated_integrable d beta (-beta) f I (S k) a U Hb HU).
  eapply gaussian_iterated_integrable_ext.
  + intros xs Hxs; symmetry; apply paper_main_loss_row_polynomial_step; exact HI.
  + exact(proj1(gaussian_iterated_add d _ _ IH (proj1(gaussian_iterated_scale d _ (/INR(S k)) HR)))).
Qed.

Lemma paper_main_loss_row_polynomial_expectation d beta f I k a U : I<>nil -> 0<=beta ->
  (forall j, In j I -> pmdf_regular d (U j)) ->
  gaussian_iterated_expectation d (paper_main_loss_row_polynomial beta f I (S k) a U)=
  gaussian_iterated_expectation d (paper_main_loss_row_polynomial beta f I k a U)+
  /INR(S k)*gaussian_iterated_expectation d (fun xs => paper_main_loss_replica (-beta) f I (S k)
    (fun js => paper_main_loss_product (fun j => paper_main_loss_factor beta (a j) (U j xs)) js)).
Proof.
intros HI Hb HU.
assert (HP := paper_main_loss_row_polynomial_integrable d beta f I k a U HI Hb HU).
assert (HR := paper_main_loss_replicated_integrable d beta (-beta) f I (S k) a U Hb HU).
transitivity (gaussian_iterated_expectation d (fun xs =>
  paper_main_loss_row_polynomial beta f I k a U xs+
  /INR(S k)*paper_main_loss_replica (-beta) f I (S k)
    (fun js => paper_main_loss_product (fun j => paper_main_loss_factor beta (a j) (U j xs)) js))).
- apply gaussian_iterated_expectation_ext; intros; apply paper_main_loss_row_polynomial_step; exact HI.
- rewrite (proj2(gaussian_iterated_add _ _ _ HP (proj1(gaussian_iterated_scale _ _ _ HR)))).
  rewrite (proj2(gaussian_iterated_scale _ _ _ HR)); reflexivity.
Qed.

Fixpoint paper_main_loss_row_constant beta k :=
  match k with O => 0 | S j => paper_main_loss_row_constant beta j+
    INR(S j)*(2*(4*paper_main_loss_factor_constant beta)^(S j)) end.

Lemma paper_main_loss_row_constant_nonnegative beta k : 0<=beta ->
  0<=paper_main_loss_row_constant beta k.
Proof.
intro Hb; induction k; [simpl; lra|].
change (0<=paper_main_loss_row_constant beta k+INR(S k)*(2*(4*paper_main_loss_factor_constant beta)^(S k))).
apply Rplus_le_le_0_compat; [exact IHk|].
apply Rmult_le_pos; [apply pos_INR|].
apply Rmult_le_pos; [lra|apply pow_le; unfold paper_main_loss_factor_constant; nra].
Qed.

Theorem paper_main_loss_row_polynomial_comparison n beta f I k a (T : nat -> 'M[R]_(S n)) eps S :
  I<>nil -> 0<=beta -> 0<=eps -> 0<=S ->
  (forall j, In j I -> paper_main_symmetric (T j)) ->
  (forall j, In j I -> paper_main_cone_opnorm_le (T j) eps) ->
  (forall j, In j I -> paper_main_frobenius (T j)^2<=S^2) ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_loss_row_polynomial beta f I k a (fun j => pmdf_quad n (T j)))-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_polynomial beta f I k a (fun j =>
      linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j)))))<=
    paper_main_loss_row_constant beta k*eps*S.
Proof.
intros HI Hb Heps HS HT HO HN.
assert (HQ : forall j, In j I -> pmdf_regular (Datatypes.S n) (pmdf_quad n (T j)))
  by (intros; apply pmdf_quad_regular).
assert (HG : forall j, In j I -> pmdf_regular (paper_main_symmetric_dimension n)
  (linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))
  by (intros; apply paper_main_projection_regular_linear).
induction k as [|k IH].
- change (Rabs(gaussian_iterated_expectation (Datatypes.S n) (fun _ => 0)-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n) (fun _ => 0))<=0*eps*S).
  rewrite (proj2(gaussian_iterated_constant (Datatypes.S n) 0))
    (proj2(gaussian_iterated_constant (paper_main_symmetric_dimension n) 0)).
  replace (0-0) with 0 by ring; rewrite Rabs_R0; ring_simplify; lra.
- rewrite (paper_main_loss_row_polynomial_expectation _ _ _ _ _ _ _ HI Hb HQ)
    (paper_main_loss_row_polynomial_expectation _ _ _ _ _ _ _ HI Hb HG).
  pose proof(paper_main_loss_replicated_comparison n beta (-beta) f I (Datatypes.S k) a T eps S
    HI Hb Heps HS HT HO HN) as HR.
  set (X := gaussian_iterated_expectation (Datatypes.S n)
    (paper_main_loss_row_polynomial beta f I k a (fun j => pmdf_quad n (T j)))).
  set (Y := gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_loss_row_polynomial beta f I k a (fun j =>
      linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))).
  fold X Y in IH.
  match goal with |- Rabs(_+_ * ?P-(_+_ * ?Q))<=_ =>
    replace (X+/INR(Datatypes.S k)*P-(Y+/INR(Datatypes.S k)*Q))
      with ((X-Y)+/INR(Datatypes.S k)*(P-Q)) by ring end.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_mult (Rabs_pos_eq (/INR(Datatypes.S k)) ltac:(apply Rlt_le,Rinv_0_lt_compat; apply lt_0_INR; lia)).
  pose proof(Rmult_le_compat_l (/INR(Datatypes.S k))
    _ _ ltac:(apply Rlt_le,Rinv_0_lt_compat; apply lt_0_INR; lia) HR) as HR2.
  assert (HE : /INR(Datatypes.S k)*paper_main_loss_replica_error beta (Datatypes.S k) eps S=
    INR(Datatypes.S k)*(2*(4*paper_main_loss_factor_constant beta)^(Datatypes.S k))*eps*S).
  { unfold paper_main_loss_replica_error; field; apply not_0_INR; lia. }
  rewrite HE in HR2.
  change (paper_main_loss_row_constant beta (Datatypes.S k)) with
    (paper_main_loss_row_constant beta k+INR(Datatypes.S k)*(2*(4*paper_main_loss_factor_constant beta)^(Datatypes.S k))).
  nra.
Qed.
