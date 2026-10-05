(* Pointwise transport of the retained soft interpolation to public features. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates VectorCoordinateDefinitions
  VectorCoordinates TensorDefinitions SoftDefinitions SoftMatrixDefinitions LowerDefinitions
  GaussianCovarianceSums SymmetricBasis JointDefinitions QuadraticDefinitions RowCoordinateDefinitions
  MultirowEndpointDefinitions PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFeature PaperMainMatrixTransport
  PaperMainSymmetricBilinear PaperMainDataFeatureMoments PaperMainDataFeatureMomentsRow
  PaperMainGordonSoftMargin GoeDefinitions GaussianProbabilityProductDefinitions
  OperatorDefinitions GaussianProductDefinitions PaperMainSoftComparison.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_public_soft_minimax d N beta gamma y
    (B : nat -> 'M[R]_d) Y S (W : nat -> 'M[R]_d) :=
  soft_minimax beta gamma
    (fun z s => finite_sum (fun i => y z i * paper_main_pairing (W i) (B s))
      (List.seq 0 N)) Y S.

Lemma paper_main_soft_matrix_public n m beta gamma y B Y S A :
  (forall s, In s S -> paper_main_symmetric (B s)) ->
  lower_block_phi n m beta gamma y (fun s => paper_main_matrix_from_public n (B s)) Y S A =
  paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m) beta gamma y B Y S
    (fun i => paper_main_matrix_to_public n (block_entry n m A i)).
Proof.
move=> Hsym.
unfold lower_block_phi, soft_matrix_phi, soft_matrix_scores, paper_main_public_soft_minimax.
apply: paper_main_gordon_soft_minimax_ext => z s Hz Hs.
apply finite_sum_ext => i Hi; f_equal.
rewrite symmetric_trace_pair_comm.
rewrite (paper_main_matrix_public_pairing _ _ _ (paper_main_matrix_internal_symmetric n _ (Hsym s Hs))).
by rewrite paper_main_matrix_public_roundtrip.
Qed.

Lemma paper_main_quadratic_input_public n xs :
  paper_main_matrix_to_public n (joint_quadratic_input n (vector_of_list n xs)) =
  paper_main_data_feature n (fun j => List.nth j xs 0).
Proof.
apply/matrixP=> i j.
have Hi : (i <= n)%coq_nat by have H := elimT ssrnat.ltP (ltn_ord i); lia.
have Hj : (j <= n)%coq_nat by have H := elimT ssrnat.ltP (ltn_ord j); lia.
rewrite paper_main_matrix_to_public_entry /joint_quadratic_input /quadratic_matrix
  matrix_entry_build // matrix_entry_zero !vector_entry_of_list //.
rewrite /paper_main_data_feature !mxE big_ord1 /paper_main_symmetric_column !mxE.
have E : Nat.eqb (nat_of_ord i) (nat_of_ord j) = (i == j).
{ apply/idP/idP.
  - move=> /eqP H; apply/eqP/val_inj; exact H.
  - move=> /eqP ->; exact: eqxx. }
rewrite E -RsqrtE -INRE -RinvE.
change (0 + /sqrt (INR (Datatypes.S n)) *
  (List.nth i xs 0 * List.nth j xs 0 - (if i == j then 1 else 0)) =
  /sqrt (INR (Datatypes.S n)) *
  (List.nth i xs 0 * List.nth j xs 0 - ((i == j)%:R)%R)).
by case: (i == j); rewrite ?mulr1n ?mulr0n -?R1E -?R0E Rplus_0_l.
Qed.

Lemma paper_main_public_soft_minimax_ext d N beta gamma y B Y S W V :
  (forall i, In i (List.seq 0 N) -> W i = V i) ->
  paper_main_public_soft_minimax d N beta gamma y B Y S W =
  paper_main_public_soft_minimax d N beta gamma y B Y S V.
Proof.
move=> H; apply: paper_main_gordon_soft_minimax_ext => z s Hz Hs.
by apply finite_sum_ext => i Hi; rewrite (H i Hi).
Qed.

Lemma paper_main_quadratic_array_public n m
    (x : paper_main_sample (Datatypes.S m) (Datatypes.S n)) i :
  (i <= m)%coq_nat ->
  paper_main_matrix_to_public n (block_entry n m (multirow_quadratic_array n m (tval x)) i) =
  paper_main_head_feature x i.
Proof.
move=> Hi; rewrite /block_entry /multirow_quadratic_array tuple_entry_build //.
rewrite paper_main_quadratic_input_public pmdf_head_feature_row.
by [].
Qed.

Theorem paper_main_quadratic_value_public n m beta gamma y B Y S
    (x : paper_main_sample (Datatypes.S m) (Datatypes.S n)) :
  (forall s, In s S -> paper_main_symmetric (B s)) ->
  multirow_quadratic_value n m beta gamma y
    (fun s => paper_main_matrix_from_public n (B s)) Y S (tval x) =
  paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m)
    beta gamma y B Y S (paper_main_head_feature x).
Proof.
move=> Hsym; rewrite /multirow_quadratic_value paper_main_soft_matrix_public //.
apply: paper_main_public_soft_minimax_ext => i Hi.
apply List.in_seq in Hi; apply paper_main_quadratic_array_public; lia.
Qed.

Definition paper_main_public_goe_feature n xs i : 'M[R]_(Datatypes.S n) :=
  paper_main_matrix_to_public n (goe_matrix n (vector_of_list (goe_vector_index n)
    (row_chunk (Datatypes.S (goe_vector_index n)) i xs))).

Lemma paper_main_goe_array_public n m xs i :
  (i <= m)%coq_nat ->
  paper_main_matrix_to_public n (block_entry n m (multirow_goe_array n m xs) i) =
  paper_main_public_goe_feature n xs i.
Proof. by move=> Hi; rewrite /block_entry /multirow_goe_array tuple_entry_build. Qed.

Theorem paper_main_goe_value_public n m beta gamma y B Y S xs :
  (forall s, In s S -> paper_main_symmetric (B s)) ->
  multirow_goe_value n m beta gamma y
    (fun s => paper_main_matrix_from_public n (B s)) Y S xs =
  paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m)
    beta gamma y B Y S (paper_main_public_goe_feature n xs).
Proof.
move=> Hsym; rewrite /multirow_goe_value paper_main_soft_matrix_public //.
apply: paper_main_public_soft_minimax_ext => i Hi.
apply List.in_seq in Hi; apply paper_main_goe_array_public; lia.
Qed.

Theorem paper_main_public_feature_soft_comparison n m beta gamma theta k y B Y S :
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k -> Y <> [] -> S <> [] ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> paper_main_symmetric (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (paper_main_matrix_from_public n (B s)) <= k) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  let EG := (\int[gaussian_product_law (Nat.mul N (Datatypes.S (goe_vector_index n)))]_x
    (paper_main_public_soft_minimax (Datatypes.S n) N beta gamma y B Y S
      (paper_main_public_goe_feature n (tval x)))%:E)%E in
  let EW := (\int[paper_main_probability N (Datatypes.S n)]_x
    (paper_main_public_soft_minimax (Datatypes.S n) N beta gamma y B Y S
      (paper_main_head_feature x))%:E)%E in
  Rabs (fine EW - fine EG) <= (40/3) * k^3 * (beta+gamma)^2 * theta *
    (d + 2*sqrt (d*Rpower.ln (INR N)) + 2*Rpower.ln (INR N)) / d^2.
Proof.
move=> Hb Hg Htheta Hk HY HS Hunit Hlow Hsym Hop; cbv zeta.
have HsymI : forall s, In s S -> symmetric_matrix n (paper_main_matrix_from_public n (B s)).
{ move=> s Hs; exact: paper_main_matrix_internal_symmetric (Hsym s Hs). }
have H := paper_main_soft_public_comparison n m beta gamma theta k y
  (fun s => paper_main_matrix_from_public n (B s)) Y S
  Hb Hg Htheta Hk HY HS Hunit Hlow HsymI Hop.
cbv zeta in H.
suff EG : (fun x : (Nat.mul (Datatypes.S m) (Datatypes.S (goe_vector_index n))).-tuple (measurableTypeR R) =>
  (multirow_goe_value n m beta gamma y (fun s => paper_main_matrix_from_public n (B s)) Y S (tval x))%:E) =
  (fun x => (paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m)
      beta gamma y B Y S (paper_main_public_goe_feature n (tval x)))%:E).
{ have EW : (fun x : paper_main_sample (Datatypes.S m) (Datatypes.S n) =>
    (multirow_quadratic_value n m beta gamma y (fun s => paper_main_matrix_from_public n (B s)) Y S (tval x))%:E) =
    (fun x => (paper_main_public_soft_minimax (Datatypes.S n) (Datatypes.S m)
        beta gamma y B Y S (paper_main_head_feature x))%:E).
  { by apply: funext => x; rewrite paper_main_quadratic_value_public. }
  by rewrite EG EW in H. }
by apply: funext => x; rewrite paper_main_goe_value_public.
Qed.

Theorem paper_main_public_feature_soft_comparison_coarse n m beta gamma theta k y B Y S :
  0 < beta -> 0 < gamma -> 0 < theta -> 0 <= k -> Y <> [] -> S <> [] ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) ->
    Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> paper_main_symmetric (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (paper_main_matrix_from_public n (B s)) <= k) ->
  Rpower.ln (INR (Datatypes.S m)) <= INR (Datatypes.S n) ->
  let d := INR (Datatypes.S n) in
  let N := Datatypes.S m in
  let EG := (\int[gaussian_product_law (Nat.mul N (Datatypes.S (goe_vector_index n)))]_x
    (paper_main_public_soft_minimax (Datatypes.S n) N beta gamma y B Y S
      (paper_main_public_goe_feature n (tval x)))%:E)%E in
  let EW := (\int[paper_main_probability N (Datatypes.S n)]_x
    (paper_main_public_soft_minimax (Datatypes.S n) N beta gamma y B Y S
      (paper_main_head_feature x))%:E)%E in
  Rabs (fine EW - fine EG) <= (200/3) * k^3 * (beta+gamma)^2 * theta / d.
Proof.
move=> Hb Hg Htheta Hk HY HS Hunit Hlow Hsym Hop Hlog; cbv zeta.
eapply Rle_trans.
- exact: (paper_main_public_feature_soft_comparison n m beta gamma theta k y B Y S
    Hb Hg Htheta Hk HY HS Hunit Hlow Hsym Hop).
- apply: paper_main_soft_comparison_coarse => //; try lra.
  + apply lt_0_INR; lia.
  + split; last exact Hlog.
    have HN : 1 <= INR (Datatypes.S m).
    { change (INR 1 <= INR (Datatypes.S m)); apply le_INR; lia. }
    case: (Rle_dec (INR (Datatypes.S m)) 1) => H.
    * have -> : INR (Datatypes.S m) = 1 by lra.
      rewrite ln_1; lra.
    * have HH := ln_increasing 1 (INR (Datatypes.S m)) ltac:(lra) ltac:(lra).
      rewrite ln_1 in HH; lra.
Qed.
