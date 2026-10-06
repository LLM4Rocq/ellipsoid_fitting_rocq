(* Coordinates of a sample outside the coordinate event.
   paper_main_data_coordinate_good: if no coordinate of the sample has
   absolute value at least U (the complement of
   paper_main_data_coordinate_event), then every entry of the underlying
   tuple has absolute value at most U, so clipping at U changes nothing.
   Deterministic. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Analysis.CoordinateContinuityDefinitions Gaussian.Iterated.Definitions
  GaussianProbabilityProductDefinitions Matrix.OperatorDefinitions
  Multirow.EndpointDefinitions PaperMainDefinitions Geometry.Psd
  Geometry.HeadFeature Spectral.Transport Gordon.Lipschitz
  Gordon.ProcessCovariance Gordon.SoftMargin Data.SampleTail Data.Clipped
  Data.ClippedSoft Soft.Comparison Soft.PublicFeatures
  Gaussian.Lipschitz.ClippingTransfer.
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
