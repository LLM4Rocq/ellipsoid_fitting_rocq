(* Rows of a sample as lists, and the head feature of one row.

   For a list zs of m rows of length N, row i is
   pmdf_row N i zs = firstn N (skipn (i * N) zs), and its entry j < N is
   List.nth (i * N + j) zs 0 (pmdf_row_nth). For a sample
   x : paper_main_sample m N with N = n + 1, the head feature of point i,
   W_i = paper_main_head_feature x i = (x_i x_i^T - I) / sqrt N, is the
   data feature of Data.FeatureMoments applied to the row
   pmdf_row N i (tval x) (pmdf_head_feature_row). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral measurable_realfun.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gaussian.Coordinate.Weights
  Analysis.FiniteSumAlgebra Radius.Regularity Gaussian.Iterated.BlockExchange
  GaussianProbabilityProductDefinitions Matrix.Definitions Tensor.Definitions
  Goe.Definitions PaperMainDefinitions Geometry.Psd Geometry.Homogeneous
  Spectral.Transport Gaussian.Symmetric.Coordinates Geometry.HeadFrobenius
  Geometry.HeadFeature Spectral.SymmetricBilinear
  Data.FeatureMomentsCoordinates Data.FeatureMoments.
Import GRing.Theory Num.Theory Order.TTheory.

Section RowList.
Local Open Scope R_scope.

(* Row i of a list of m rows of length N. *)
Definition pmdf_row (N i : nat) (zs : list R) : list R :=
  firstn N (skipn (i * N)%coq_nat zs).

Lemma pmdf_row_nth N i zs j : (j < N)%coq_nat ->
  List.nth j (pmdf_row N i zs) 0 = List.nth (i * N + j) zs 0.
Proof. by move=> Hj; rewrite /pmdf_row (nth_firstn_lt _ _ _ Hj) nth_skipn_add. Qed.

End RowList.

Local Open Scope ring_scope.

Lemma pmdf_data_feature_ext n (f g : nat -> R) :
  (forall j : 'I_(S n), f j = g j) ->
  paper_main_data_feature n f = paper_main_data_feature n g.
Proof. by move=> H; apply/matrixP => a b; rewrite !paper_main_data_feature_entry !H. Qed.

Section RowMoments.
Variables (m n : nat).
Local Notation N := (S n).
Implicit Types (S T : 'M[R]_N).

(* The head feature of row i is the data feature of pmdf_row. *)
Lemma pmdf_head_feature_row (x : paper_main_sample m N) i :
  paper_main_head_feature x i =
  paper_main_data_feature n (fun j => List.nth j (pmdf_row N i (tval x)) 0).
Proof.
rewrite paper_main_data_feature_head; apply: pmdf_data_feature_ext => j.
have Hj : (j < N)%coq_nat by apply/ssrnat.ltP.
by rewrite (pmdf_row_nth N i (tval x) j Hj).
Qed.

End RowMoments.
