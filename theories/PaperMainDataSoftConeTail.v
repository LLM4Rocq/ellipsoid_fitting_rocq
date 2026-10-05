(* Explicit finite data soft tails on the actual bounded-condition cone. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProbabilityProductDefinitions
  GoeDefinitions OperatorDefinitions PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHeadFeature PaperMainGeometryHeadWidth PaperMainMatrixTransport
  PaperMainGaussianFeatureCoordinates PaperMainGordonWidth PaperMainConeGaussianCoordinatesSpheres
  PaperMainMatrixOperatorTransport PaperMainSoftPublicFeatures PaperMainSoftConeMargin
  PaperMainDataClippedSoft PaperMainDataClippedMoments PaperMainDataSoftConcentration.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_data_soft_cone_level n m r s beta gamma theta kappa B :=
  let d := INR (S n) in
  goe_scale n *
    (paper_main_gordon_width (paper_main_symmetric_dimension n)
      (fun j => paper_main_symmetric_coordinates n (paper_main_matrix_from_public n (B j)))
      (List.seq 0 s)-sqrt(INR (S m))) - Rpower.ln (INR r)/beta -
    (200/3)*kappa^3*(beta+gamma)^2*theta/(d^2*sqrt d).

Lemma paper_main_data_cone_soft_admissible n N r s kappa y B :
  1 <= kappa ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 N) = 1) ->
  (forall j, (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j)) ->
  paper_main_data_clipped_admissible n N (kappa/sqrt(INR (S n)))
    (fun _ q => B q) (fun z _ => y z) (List.seq 0 r) (List.seq 0 s).
Proof.
move=> Hk Hy HB z q /List.in_seq [_ Hz] /List.in_seq [_ Hq].
split; first exact: paper_main_cone_condition_sphere_symmetric (HB q Hq).
split; first exact: paper_main_matrix_operator_cone_sphere_INR Hk (HB q Hq).
rewrite (Hy z Hz); lra.
Qed.

Lemma paper_main_data_cone_soft_expectation n m r s beta gamma theta kappa y B :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  0 < beta -> 0 < gamma -> 0 < theta -> 1 <= kappa ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (S m)) = 1) ->
  (forall z i, (z < r)%coq_nat -> (i <= m)%coq_nat ->
    Rabs (y z i) <= theta/sqrt(INR (S n))) ->
  (forall j, (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j)) ->
  Rpower.ln (INR (S m)) <= INR (S n) ->
  paper_main_data_soft_cone_level n m r s beta gamma theta kappa B <=
    gaussian_iterated_expectation ((S m)*(S n))
      (paper_main_data_raw_soft n (S m) beta gamma (fun _ q => B q) (fun z _ => y z)
        (List.seq 0 r) (List.seq 0 s)).
Proof.
move=> Hr Hs Hb Hg Htheta Hk Hy Hlow HB Hlog.
have HY : List.seq 0 r <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have HQ : List.seq 0 s <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have Hsqrt : 0 < sqrt(INR (S n)) by apply sqrt_lt_R0,lt_0_INR; lia.
have HK : 0 <= kappa/sqrt(INR (S n)).
{ apply Rmult_le_pos; first lra; apply Rlt_le,Rinv_0_lt_compat; exact Hsqrt. }
have Had := paper_main_data_cone_soft_admissible n (S m) r s kappa y B Hk Hy HB.
have HM := paper_main_data_soft_cone_margin n m r s beta gamma theta kappa y B
  Hr Hs Hb Hg Htheta Hk Hy Hlow HB Hlog.
cbv zeta in HM.
have HE := paper_main_data_raw_soft_public_mean n (S m) (kappa/sqrt(INR (S n)))
  beta gamma y B (List.seq 0 r) (List.seq 0 s) HK Hb Hg HY HQ Had.
rewrite HE in HM; exact HM.
Qed.

Theorem paper_main_data_cone_soft_lower_tail U n m r s beta gamma theta kappa y B a u :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  0 < beta -> 0 < gamma -> 0 < theta -> 1 <= kappa -> 0 < U -> 0 < a -> 0 < u ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (S m)) = 1) ->
  (forall z i, (z < r)%coq_nat -> (i <= m)%coq_nat ->
    Rabs (y z i) <= theta/sqrt(INR (S n))) ->
  (forall j, (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j)) ->
  Rpower.ln (INR (S m)) <= INR (S n) ->
  let k := kappa/sqrt(INR (S n)) in
  (paper_main_probability (S m) (S n)
    [set x | Rle (paper_main_public_soft_minimax (S n) (S m) beta gamma y B
      (List.seq 0 r) (List.seq 0 s) (paper_main_head_feature x))
      (paper_main_data_soft_cone_level n m r s beta gamma theta kappa B-
       paper_main_data_soft_clipping_loss U n (S m) k beta gamma (List.seq 0 r) (List.seq 0 s) a-u)] <=
    (2*INR (S m)*INR (S n)*exp(-U^2/2)+exp(-u^2/(2*(2*k*U)^2)))%:E)%E.
Proof.
move=> Hr Hs Hb Hg Htheta Hk HU Ha Hu Hy Hlow HB Hlog; cbv zeta.
have HY : List.seq 0 r <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have HQ : List.seq 0 s <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have Hsqrt : 0 < sqrt(INR (S n)) by apply sqrt_lt_R0,lt_0_INR; lia.
have HK : 0 < kappa/sqrt(INR (S n)).
{ apply Rmult_lt_0_compat; first lra; apply Rinv_0_lt_compat; exact Hsqrt. }
have Had := paper_main_data_cone_soft_admissible n (S m) r s kappa y B Hk Hy HB.
have Hmean := paper_main_data_cone_soft_expectation n m r s beta gamma theta kappa y B
  Hr Hs Hb Hg Htheta Hk Hy Hlow HB Hlog.
exact: (paper_main_data_soft_raw_lower_margin U n (S m) (kappa/sqrt(INR (S n)))
  beta gamma (fun _ q => B q) (fun z _ => y z) (List.seq 0 r) (List.seq 0 s) a
  (paper_main_data_soft_cone_level n m r s beta gamma theta kappa B) u
  HU HK Hb Hg HY HQ Ha Hu Had Hmean).
Qed.

Theorem paper_main_data_cone_soft_clipped_lower_tail U n m r s beta gamma theta kappa y B a u :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  0 < beta -> 0 < gamma -> 0 < theta -> 1 <= kappa -> 0 < U -> 0 < a -> 0 < u ->
  (forall z, (z < r)%coq_nat -> euclidean_norm (y z) (List.seq 0 (S m)) = 1) ->
  (forall z i, (z < r)%coq_nat -> (i <= m)%coq_nat ->
    Rabs (y z i) <= theta/sqrt(INR (S n))) ->
  (forall j, (j < s)%coq_nat -> paper_main_head_cone_sphere kappa (B j)) ->
  Rpower.ln (INR (S m)) <= INR (S n) ->
  let k := kappa/sqrt(INR (S n)) in
  (paper_main_probability (S m) (S n)
    [set x | Rle (paper_main_data_clipped_soft U n (S m) beta gamma (fun _ q => B q) (fun z _ => y z)
      (List.seq 0 r) (List.seq 0 s) (tval x))
      (paper_main_data_soft_cone_level n m r s beta gamma theta kappa B-
       paper_main_data_soft_clipping_loss U n (S m) k beta gamma (List.seq 0 r) (List.seq 0 s) a-u)] <=
    (exp(-u^2/(2*(2*k*U)^2)))%:E)%E.
Proof.
move=> Hr Hs Hb Hg Htheta Hk HU Ha Hu Hy Hlow HB Hlog; cbv zeta.
have HY : List.seq 0 r <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have HQ : List.seq 0 s <> [].
{ move=> H; have HH := congr1 (@List.length nat) H; rewrite List.length_seq /= in HH; lia. }
have Hsqrt : 0 < sqrt(INR (S n)) by apply sqrt_lt_R0,lt_0_INR; lia.
have HK : 0 < kappa/sqrt(INR (S n)).
{ apply Rmult_lt_0_compat; first lra; apply Rinv_0_lt_compat; exact Hsqrt. }
have Had := paper_main_data_cone_soft_admissible n (S m) r s kappa y B Hk Hy HB.
have Hmean := paper_main_data_cone_soft_expectation n m r s beta gamma theta kappa y B
  Hr Hs Hb Hg Htheta Hk Hy Hlow HB Hlog.
exact: (paper_main_data_soft_clipped_lower_margin U n (S m) (kappa/sqrt(INR (S n)))
  beta gamma (fun _ q => B q) (fun z _ => y z) (List.seq 0 r) (List.seq 0 s) a
  (paper_main_data_soft_cone_level n m r s beta gamma theta kappa B) u
  HU HK Hb Hg HY HQ Ha Hu Had Hmean).
Qed.
