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
