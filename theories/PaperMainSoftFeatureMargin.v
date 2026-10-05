(* Gaussian soft expectation margin transported to quadratic sample features. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct normedtype ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianCovarianceSums GaussianProductDefinitions
  GaussianProduct GaussianProbabilityProductDefinitions GaussianCovarianceDefinitions
  MatrixDefinitions MatrixCoordinates OperatorDefinitions VectorCoordinateDefinitions VectorCoordinates
  GoeDefinitions RowCoordinateDefinitions RowCoordinates
  MultirowEndpointDefinitions PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainMatrixTransport PaperMainGaussianFeatureCoordinates
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonBilinear
  PaperMainGeometryHeadFeature PaperMainGordonWidth PaperMainGordonSoftMargin PaperMainSoftComparison PaperMainSoftPublicFeatures.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_soft_max_scale gamma c f I :
  c <> 0 -> gamma <> 0 ->
  soft_max gamma (fun i => c * f i) I = c * soft_max (c * gamma) f I.
Proof.
move=> Hc Hg; rewrite /soft_max.
have E : finite_sum (fun i => exp (gamma * (c * f i))) I =
  finite_sum (fun i => exp (c * gamma * f i)) I.
{ apply finite_sum_ext => i Hi; f_equal; ring. }
rewrite E; field; split; assumption.
Qed.

Lemma paper_main_soft_minimax_scale beta gamma c F Y S :
  c <> 0 -> beta <> 0 -> gamma <> 0 ->
  soft_minimax beta gamma (fun y s => c * F y s) Y S =
  c * soft_minimax (c * beta) (c * gamma) F Y S.
Proof.
move=> Hc Hb Hg; rewrite /soft_minimax /soft_min.
have E : (fun y => - soft_max gamma (fun s => c * F y s) S) =
  (fun y => c * (- soft_max (c * gamma) (F y) S)).
{ apply: funext => y; rewrite paper_main_soft_max_scale //; ring. }
rewrite E paper_main_soft_max_scale //; ring.
Qed.

Lemma paper_main_public_goe_feature_row n xs i :
  paper_main_public_goe_feature n xs i =
  paper_main_matrix_to_public n (paper_main_gaussian_feature_row n i xs).
Proof.
rewrite /paper_main_public_goe_feature /paper_main_gaussian_feature_row.
f_equal; f_equal; apply: (tuple_ext R^o (goe_vector_index n)) => k Hk.
rewrite /vector_of_list !tuple_entry_build // /row_chunk.
have HK : (k < Datatypes.S (goe_vector_index n))%coq_nat by lia.
rewrite (nth_firstn_lt (List.skipn (Nat.mul i (Datatypes.S (goe_vector_index n))) xs) _ k HK).
by rewrite nth_skipn_add.
Qed.

Lemma paper_main_public_goe_score_coordinates n N u (B : 'M[R]_(Datatypes.S n)) xs :
  paper_main_symmetric B ->
  finite_sum (fun i => u i * paper_main_pairing (paper_main_public_goe_feature n xs i) B)
    (List.seq 0 N) =
  goe_scale n * paper_main_gordon_matrix_value N (paper_main_symmetric_dimension n)
    u (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n B)) xs.
Proof.
move=> Hsym; rewrite -paper_main_gaussian_feature_pairing_coordinates.
apply finite_sum_ext => i Hi; f_equal.
rewrite paper_main_public_goe_feature_row.
have H := paper_main_matrix_public_pairing n (paper_main_gaussian_feature_row n i xs)
  (paper_main_matrix_from_public n B) (paper_main_matrix_internal_symmetric n B Hsym).
by rewrite paper_main_matrix_public_roundtrip in H; symmetry.
Qed.

Lemma paper_main_public_goe_soft_coordinates n m beta gamma y B Y S xs :
  beta <> 0 -> gamma <> 0 ->
  (forall s, In s S -> paper_main_symmetric (B s)) ->
  paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m)
    beta gamma y B Y S (paper_main_public_goe_feature n xs) =
  goe_scale n * soft_minimax (goe_scale n * beta) (goe_scale n * gamma)
    (fun z s => paper_main_gordon_matrix_value (Datatypes.S m) (paper_main_symmetric_dimension n)
      (y z) (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B s))) xs) Y S.
Proof.
move=> Hb Hg Hsym.
have Hc : goe_scale n <> 0.
{ have Hpos : 0 < goe_scale n.
  { rewrite /goe_scale; apply sqrt_lt_R0; apply Rdiv_lt_0_compat; first lra.
    apply lt_0_INR; lia. }
  lra. }
rewrite -paper_main_soft_minimax_scale //.
apply: paper_main_gordon_soft_minimax_ext => z s Hz Hs.
exact: paper_main_public_goe_score_coordinates (Hsym s Hs).
Qed.

Theorem paper_main_public_goe_soft_margin n m r s beta gamma y B :
  (0 < r)%coq_nat -> (0 < s)%coq_nat -> 0 < beta -> 0 < gamma ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall j, (j < s)%coq_nat -> paper_main_symmetric (B j)) ->
  (forall j, (j < s)%coq_nat -> paper_main_frobenius (B j) = 1) ->
  goe_scale n *
    (paper_main_gordon_width (paper_main_symmetric_dimension n)
      (fun j => paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j)))
      (List.seq 0 s) - sqrt (INR (Datatypes.S m))) - Rpower.ln (INR r) / beta <=
  fine (\int[gaussian_product_law (Nat.mul (Datatypes.S m) (paper_main_symmetric_dimension n))]_x
    (paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m) beta gamma y B
      (List.seq 0 r) (List.seq 0 s) (paper_main_public_goe_feature n (tval x)))%:E)%E.
Proof.
move=> Hr Hs Hb Hg Hy HB HF.
have HY : List.seq 0 r <> [].
{ move=> H; have := f_equal (@List.length nat) H; rewrite length_seq /=; lia. }
have HS : List.seq 0 s <> [].
{ move=> H; have := f_equal (@List.length nat) H; rewrite length_seq /=; lia. }
have Hsym : forall j, In j (List.seq 0 s) -> paper_main_symmetric (B j).
{ move=> j Hj; apply HB; apply List.in_seq in Hj; lia. }
have Hc : 0 < goe_scale n.
{ rewrite /goe_scale; apply sqrt_lt_R0; apply Rdiv_lt_0_compat; first lra.
  apply lt_0_INR; lia. }
have Hz : forall z, (z < r)%coq_nat ->
    paper_main_gordon_dot (Datatypes.S m) (y z) (y z) = 1.
{ move=> z Hz; have H := paper_main_gordon_euclidean_squared (Datatypes.S m) (y z).
  rewrite (Hy z Hz) in H; nra. }
have Hv : forall j, (j < s)%coq_nat ->
    paper_main_gordon_dot (paper_main_symmetric_dimension n)
      (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j)))
      (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j))) = 1.
{ move=> j Hj.
  have H := paper_main_gordon_euclidean_squared (paper_main_symmetric_dimension n)
    (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j))).
  rewrite (paper_main_symmetric_coordinate_norm n _ (paper_main_matrix_internal_symmetric n _ (HB j Hj)))
    paper_main_matrix_internal_frobenius (HF j Hj) in H; nra. }
have [HD HM] := paper_main_gordon_soft_width_margin r s (Datatypes.S m)
  (paper_main_symmetric_dimension n) y
  (fun j => paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j)))
  (goe_scale n * beta) (goe_scale n * gamma) Hr Hs ltac:(nra) ltac:(nra) Hz Hv.
pose F := fun xs => soft_minimax (goe_scale n * beta) (goe_scale n * gamma)
  (fun z j => paper_main_gordon_matrix_value (Datatypes.S m) (paper_main_symmetric_dimension n)
    (y z) (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j))) xs)
  (List.seq 0 r) (List.seq 0 s).
have [_ HE] := gaussian_iterated_scale
  (Nat.mul (Datatypes.S m) (paper_main_symmetric_dimension n)) F (goe_scale n) (proj1 HD).
have [[_ EG] _] := paper_main_soft_endpoint_laws n m beta gamma y
  (fun j => paper_main_matrix_from_public n (B j)) (List.seq 0 r) (List.seq 0 s) Hb Hg HY HS.
have Efun : (fun x : (Nat.mul (Datatypes.S m) (paper_main_symmetric_dimension n)).-tuple (measurableTypeR R) =>
  (multirow_goe_value n m beta gamma y (fun j => paper_main_matrix_from_public n (B j))
    (List.seq 0 r) (List.seq 0 s) (tval x))%:E) =
  (fun x => (paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m) beta gamma y B
    (List.seq 0 r) (List.seq 0 s) (paper_main_public_goe_feature n (tval x)))%:E).
{ by apply: funext => x; rewrite paper_main_goe_value_public. }
rewrite Efun in EG; rewrite EG.
change (goe_scale n *
    (paper_main_gordon_width (paper_main_symmetric_dimension n)
      (fun j => paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j)))
      (List.seq 0 s) - sqrt (INR (Datatypes.S m))) - Rpower.ln (INR r) / beta <= gaussian_iterated_expectation
    (Nat.mul (Datatypes.S m) (paper_main_symmetric_dimension n))
    (multirow_goe_value n m beta gamma y (fun j => paper_main_matrix_from_public n (B j))
      (List.seq 0 r) (List.seq 0 s))).
have Eiter : gaussian_iterated_expectation
    (Nat.mul (Datatypes.S m) (paper_main_symmetric_dimension n))
    (multirow_goe_value n m beta gamma y (fun j => paper_main_matrix_from_public n (B j))
      (List.seq 0 r) (List.seq 0 s)) =
  gaussian_iterated_expectation (Nat.mul (Datatypes.S m) (paper_main_symmetric_dimension n))
    (fun xs => goe_scale n * F xs).
{ apply gaussian_iterated_expectation_ext => xs Hxs.
  rewrite paper_main_goe_value_public //.
  rewrite /F; apply paper_main_public_goe_soft_coordinates; try lra; exact Hsym. }
rewrite Eiter HE.
have H := Rmult_le_compat_l _ _ _ (Rlt_le _ _ Hc) HM.
have Eentropy : goe_scale n * (Rpower.ln (INR r) / (goe_scale n * beta)) =
  Rpower.ln (INR r) / beta by field; lra.
rewrite /F; nra.
Qed.

Theorem paper_main_data_soft_margin_coarse n m r s beta gamma theta k y B :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, (z < r)%coq_nat -> (i <= m)%coq_nat ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall j, (j < s)%coq_nat -> paper_main_symmetric (B j)) ->
  (forall j, (j < s)%coq_nat -> paper_main_frobenius (B j) = 1) ->
  (forall j, (j < s)%coq_nat -> matrix_operator_norm n (paper_main_matrix_from_public n (B j)) <= k) ->
  Rpower.ln (INR (Datatypes.S m)) <= INR (Datatypes.S n) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  let err := (200/3) * k^3 * (beta+gamma)^2 * theta / d in
  goe_scale n *
    (paper_main_gordon_width (paper_main_symmetric_dimension n)
      (fun j => paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j)))
      (List.seq 0 s) - sqrt (INR N)) - Rpower.ln (INR r) / beta - err <=
  fine (\int[paper_main_probability N (Datatypes.S n)]_x
    (paper_main_public_soft_minimax (Datatypes.S n) N beta gamma y B
      (List.seq 0 r) (List.seq 0 s) (paper_main_head_feature x))%:E)%E.
Proof.
move=> Hr Hs Hb Hg Htheta Hk Hy Hlow HB HF Hop Hlog; cbv zeta.
have HY : List.seq 0 r <> [].
{ move=> H; have := f_equal (@List.length nat) H; rewrite length_seq /=; lia. }
have HS : List.seq 0 s <> [].
{ move=> H; have := f_equal (@List.length nat) H; rewrite length_seq /=; lia. }
have Hunit : forall z, In z (List.seq 0 r) ->
  euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1.
{ move=> z Hz; apply Hy; apply List.in_seq in Hz; lia. }
have Hlow' : forall z i, In z (List.seq 0 r) -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n)).
{ move=> z i Hz Hi; apply Hlow; apply List.in_seq in Hz; apply List.in_seq in Hi; lia. }
have Hsym : forall j, In j (List.seq 0 s) -> paper_main_symmetric (B j).
{ move=> j Hj; apply HB; apply List.in_seq in Hj; lia. }
have Hop' : forall j, In j (List.seq 0 s) ->
    matrix_operator_norm n (paper_main_matrix_from_public n (B j)) <= k.
{ move=> j Hj; apply Hop; apply List.in_seq in Hj; lia. }
have HC := paper_main_public_feature_soft_comparison_coarse n m beta gamma theta k y B
  (List.seq 0 r) (List.seq 0 s) Hb Hg Htheta Hk HY HS Hunit Hlow' Hsym Hop' Hlog.
have HM := paper_main_public_goe_soft_margin n m r s beta gamma y B Hr Hs Hb Hg Hy HB HF.
cbv zeta in HC.
apply Rabs_le_between in HC; destruct HC as [HC _].
unfold paper_main_symmetric_dimension in HM |- *; lra.
Qed.
