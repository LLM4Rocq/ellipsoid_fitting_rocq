(* Actual data-law lower tails via coordinate clipping. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianCoordinateDefinitions GaussianProductDefinitions GaussianProbabilityProductDefinitions
  OperatorDefinitions MultirowEndpointDefinitions PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHeadFeature PaperMainMatrixTransport
  PaperMainGordonLipschitz PaperMainGordonProcessCovariance PaperMainGordonSoftMargin
  PaperMainDataSampleTail PaperMainDataClipped PaperMainDataClippedSoft
  PaperMainSoftComparison PaperMainSoftPublicFeatures PaperMainGaussianClippingTransfer.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_data_soft_clipped U n N beta gamma y B Y Q xs :=
  soft_minimax beta gamma
    (paper_main_data_clipped_family U n N (fun _ q => B q) (fun z _ => y z) xs) Y Q.

Lemma paper_main_data_coordinate_good N n U (x : paper_main_sample N (S n)) :
  ~ paper_main_data_coordinate_event N (S n) U x ->
  forall l, (l < N * S n)%N -> Rabs (List.nth l (tval x) 0) <= U.
Proof.
move=> Hx l Hl.
have Hq : (l %/ S n < N)%N by rewrite ltn_divLR.
have Hr : (l %% S n < S n)%N := ltn_pmod l (ltn0Sn n).
have Hnot : ~ Rle U (Rabs (paper_main_point x (Ordinal Hq) (Ordinal Hr) ord0)).
{ move=> H; apply Hx; exists (Ordinal Hq), (Ordinal Hr); exact H. }
have Hlt := Rnot_le_lt _ _ Hnot.
move: Hlt; rewrite pmds_point_entry /= -divn_eq; lra.
Qed.

Theorem paper_main_data_soft_clipped_public U n N beta gamma y B Y Q
    (x : paper_main_sample N (S n)) :
  ~ paper_main_data_coordinate_event N (S n) U x ->
  paper_main_data_soft_clipped U n N beta gamma y B Y Q (tval x) =
  paper_main_public_soft_minimax (S n) N beta gamma y B Y Q (paper_main_head_feature x).
Proof.
move=> Hx; apply: paper_main_gordon_soft_minimax_ext => z q Hz Hq.
rewrite /paper_main_data_clipped_family.
exact: paper_main_data_clipped_score_head (paper_main_data_coordinate_good N n U x Hx).
Qed.

Theorem paper_main_data_soft_clipped_quadratic U n m beta gamma y B Y Q
    (x : paper_main_sample (S m) (S n)) :
  (forall q, In q Q -> paper_main_symmetric (B q)) ->
  ~ paper_main_data_coordinate_event (S m) (S n) U x ->
  multirow_quadratic_value n m beta gamma y
    (fun q => paper_main_matrix_from_public n (B q)) Y Q (tval x) =
  paper_main_data_soft_clipped U n (S m) beta gamma y B Y Q (tval x).
Proof.
move=> HB Hx.
have E := paper_main_quadratic_value_public n m beta gamma y B Y Q x HB.
have H := paper_main_data_soft_clipped_public U n (S m) beta gamma y B Y Q x Hx.
exact (Logic.eq_trans E (Logic.eq_sym H)).
Qed.

Theorem paper_main_data_soft_clipping_lower_tail U n m beta gamma y B Y Q k b u :
  0 < U -> 0 < k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  (forall q, In q Q -> paper_main_symmetric (B q)) ->
  (forall q, In q Q -> matrix_operator_norm n (paper_main_matrix_from_public n (B q)) <= k) ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (S m)) <= 1) ->
  b <= gaussian_iterated_expectation (Nat.mul (S m) (S n))
    (paper_main_data_soft_clipped U n (S m) beta gamma y B Y Q) -> 0 < u ->
  (paper_main_probability (S m) (S n)
    [set x | Rle (paper_main_public_soft_minimax (S n) (S m) beta gamma y B Y Q
      (paper_main_head_feature x)) (b-u)] <=
    (2*INR (S m)*INR (S n)*exp(-U^2/2) + exp(-u^2/(2*(2*k*U)^2)))%:E)%E.
Proof.
move=> HU Hk Hb Hg HY HQ Hsym Hop Hy Hmean Hu.
pose F := multirow_quadratic_value n m beta gamma y
  (fun q => paper_main_matrix_from_public n (B q)) Y Q.
pose G := paper_main_data_soft_clipped U n (S m) beta gamma y B Y Q.
have [_ CF] := paper_main_soft_endpoint_continuous n m beta gamma y
  (fun q => paper_main_matrix_from_public n (B q)) Y Q Hb Hg HY HQ.
have HG : forall xs ys, List.length xs = (Nat.mul (S m) (S n)) ->
    List.length ys = (Nat.mul (S m) (S n)) ->
    Rabs (G xs-G ys) <= (2*k*U)*paper_main_gordon_distance (Nat.mul (S m) (S n)) xs ys.
{ move=> xs ys _ _.
  have Had : paper_main_data_clipped_admissible n (S m) k
    (fun _ q => B q) (fun z _ => y z) Y Q.
  { move=> z q Hz Hq; split; first exact: Hsym Hq.
    split; [exact: Hop Hq | exact: Hy Hz]. }
  exact: (paper_main_data_clipped_soft_lipschitz U n (S m) k beta gamma
    (fun _ q => B q) (fun z _ => y z) Y Q xs ys
    (Rlt_le _ _ HU) (Rlt_le _ _ Hk) Hb Hg HY HQ Had). }
have [mA Hp] := paper_main_data_coordinate_tail (S m) (S n) U HU.
have Heq : forall x, ~ paper_main_data_coordinate_event (S m) (S n) U x -> F (tval x) = G (tval x).
{ move=> x Hx; exact: paper_main_data_soft_clipped_quadratic Hsym Hx. }
have HL : 0 < 2*k*U by apply Rmult_lt_0_compat => //; apply Rmult_lt_0_compat => //; lra.
have HT := paper_main_gaussian_clipping_lower_tail_bound (Nat.mul (S m) (S n)) F G
  (2*k*U) (paper_main_data_coordinate_event (S m) (S n) U)
  (2*INR (S m)*INR (S n)*exp(-U^2/2)) b u CF HL HG mA Heq Hp Hmean Hu.
have EE : [set x : paper_main_sample (S m) (S n) | Rle (F (tval x)) (b-u)] =
  [set x | Rle (paper_main_public_soft_minimax (S n) (S m) beta gamma y B Y Q
      (paper_main_head_feature x)) (b-u)].
{ apply/seteqP; split => x Hx.
  - exact (Logic.eq_ind _ (fun v : R => Rle v (b-u)) Hx _
      (paper_main_quadratic_value_public n m beta gamma y B Y Q x Hsym)).
  - exact (Logic.eq_ind _ (fun v : R => Rle v (b-u)) Hx _
      (Logic.eq_sym (paper_main_quadratic_value_public n m beta gamma y B Y Q x Hsym))). }
by rewrite EE in HT.
Qed.
