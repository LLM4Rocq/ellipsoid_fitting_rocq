(* The one-row law bridge for the quadratic data feature: the moments of
   PaperMainDataFeatureMoments hold for the head feature of each row of an
   m-point sample, under the actual sample law.

   The sample x : paper_main_sample m N, N = n + 1, has the law
   gaussian_product_law (m * N), the measure of paper_main_probability m N.
   For i < m, row i has the coordinates List.nth (i * N + j) (tval x) 0,
   j < N (paper_main_point x i), and its feature is
   W_i = paper_main_head_feature x i = (x_i x_i^T - I) / sqrt N. With actual
   integrability:
   - E <W_i, S> = 0 (paper_main_head_feature_mean);
   - E <W_i, S><W_i, T> = N^-1 (<S, T> + <S, T^T>), and (2/N) <S, T> for
     symmetric T (paper_main_head_feature_covariance,
     paper_main_head_feature_covariance_symmetric);
   - E |W_i|_F^2 = N + 1 (paper_main_head_feature_frobenius);
   - E c_k(W_i) = 0 and E c_k(W_i) c_l(W_i) = goe_scale n ^ 2 * delta_kl in
     the goe_basis (paper_main_head_feature_coefficient_mean,
     paper_main_head_feature_coefficient_covariance).

   Proof. On lists, row i is pmdf_row N i zs = firstn N (skipn (i * N) zs).
   For G continuous with a polynomial bound in dimension N, the iterated
   expectation of zs |-> G (pmdf_row N i zs) in dimension m * N equals that
   of G (pmdf_row_moment): the blocks before and after row i integrate out
   by gaussian_block_exchange_signed (pmdf_expectation_skipn,
   pmdf_expectation_firstn). pmdf_actual transports to the actual law. One
   row at a time: joint laws of several rows are not treated here. Nothing
   from the paper is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral measurable_realfun.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCovarianceSums MaximumRadiusRegularity GaussianBlockExchange
  GaussianProbabilityProductDefinitions MatrixDefinitions TensorDefinitions GoeDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainMatrixTransport PaperMainGaussianFeatureCoordinates
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature PaperMainSymmetricBilinear
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments.
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
