(* A lower bound for the expected data soft minimax, for matrices of the
   bounded-condition cone sphere.
   - paper_main_soft_cone_error_scale: the algebra
     A (kappa / sqrt d)^3 / d = A kappa^3 / (d^2 sqrt d).
   - paper_main_data_soft_cone_margin: let B_j (j < s) be in the cone
     sphere paper_main_head_cone_sphere kappa, kappa >= 1, and let y_z
     (z < r) be unit dual vectors of length N = m + 1 with entries at most
     theta / sqrt d, d = n + 1, and ln N <= d. Then the expectation of the
     soft minimax of sum_i y_z(i) <W_i, B_j> over the features W_i of the
     sample is at least
       goe_scale n (w - sqrt N) - ln r / beta
         - (200/3) kappa^3 (beta + gamma)^2 theta / (d^2 sqrt d),
     where w is the Gordon width of the B_j in GOE coordinates. This is
     paper_main_data_soft_margin_coarse with the operator bound
     kappa / sqrt d of the cone sphere. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions
  GaussianProbabilityProductDefinitions GoeDefinitions OperatorDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGeometryHeadFeature
  PaperMainGeometryHeadWidth PaperMainMatrixTransport
  PaperMainGaussianFeatureCoordinates PaperMainGordonWidth
  PaperMainConeGaussianCoordinatesSpheres PaperMainMatrixOperatorTransport
  PaperMainSoftPublicFeatures PaperMainSoftFeatureMargin.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_soft_cone_error_scale d kappa A :
  0 < d -> A * (kappa / sqrt d)^3 / d = A * kappa^3 / (d^2 * sqrt d).
Proof.
move=> Hd.
have Hs : 0 < sqrt d by apply sqrt_lt_R0.
have Hsq := pow2_sqrt d ltac:(lra).
remember (sqrt d) as z eqn:Hz in *.
have HE : d^2 * z = z^3 * d.
{ rewrite -Hsq; ring. }
rewrite HE; field; split; lra.
Qed.

Theorem paper_main_data_soft_cone_margin n m r s beta gamma theta kappa y B :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  0 < beta -> 0 < gamma -> 0 < theta -> 1 <= kappa ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, (z < r)%coq_nat -> (i <= m)%coq_nat ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall j, (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j)) ->
  Rpower.ln (INR (Datatypes.S m)) <= INR (Datatypes.S n) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  goe_scale n *
    (paper_main_gordon_width (paper_main_symmetric_dimension n)
      (fun j => paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j)))
      (List.seq 0 s) - sqrt (INR N)) - Rpower.ln (INR r) / beta -
    (200/3) * kappa^3 * (beta+gamma)^2 * theta / (d^2 * sqrt d) <=
  fine (\int[paper_main_probability N (Datatypes.S n)]_x
    (paper_main_public_soft_minimax (Datatypes.S n) N beta gamma y B
      (List.seq 0 r) (List.seq 0 s) (paper_main_head_feature x))%:E)%E.
Proof.
move=> Hr Hs Hb Hg Htheta Hk Hy Hlow HB Hlog; cbv zeta.
have Hd : 0 < INR (Datatypes.S n) by apply lt_0_INR; lia.
have Hsqrt : 0 < sqrt (INR (Datatypes.S n)) by apply sqrt_lt_R0.
have Hop0 : 0 <= kappa / sqrt (INR (Datatypes.S n)).
{ apply Rlt_le,Rdiv_lt_0_compat; lra. }
have Hsym : forall j, (j < s)%coq_nat -> paper_main_symmetric (B j).
{ move=> j Hj; exact: paper_main_cone_condition_sphere_symmetric (HB j Hj). }
have HF : forall j, (j < s)%coq_nat -> paper_main_frobenius (B j) = 1.
{ move=> j Hj; exact: paper_main_cone_condition_sphere_unit (HB j Hj). }
have Hop : forall j, (j < s)%coq_nat ->
    matrix_operator_norm n (paper_main_matrix_from_public n (B j)) <= kappa / sqrt (INR (Datatypes.S n)).
{ move=> j Hj; exact: paper_main_matrix_operator_cone_sphere_INR Hk (HB j Hj). }
have H := paper_main_data_soft_margin_coarse n m r s beta gamma theta
  (kappa / sqrt (INR (Datatypes.S n))) y B Hr Hs Hb Hg Htheta Hop0 Hy Hlow Hsym HF Hop Hlog.
cbv zeta in H.
have E : (200/3) * (kappa / sqrt (INR (Datatypes.S n)))^3 * (beta+gamma)^2 * theta / INR (Datatypes.S n) =
  (200/3) * kappa^3 * (beta+gamma)^2 * theta / (INR (Datatypes.S n)^2 * sqrt (INR (Datatypes.S n))).
{ transitivity (((200/3)*(beta+gamma)^2*theta) * (kappa / sqrt (INR (Datatypes.S n)))^3 / INR (Datatypes.S n)).
  - field; repeat split; lra.
  - rewrite paper_main_soft_cone_error_scale //; field; repeat split; lra. }
by rewrite E in H.
Qed.
