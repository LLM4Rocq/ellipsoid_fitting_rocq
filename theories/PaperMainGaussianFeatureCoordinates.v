(* Frobenius coordinates for the existing GOE construction.
   The legacy index n represents the true dimension p = S n. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  MatrixDefinitions MatrixCoordinates MatrixTrace MatrixGradient TensorDefinitions
  OperatorDefinitions NormEquivalence SymmetricDefinitions SymmetricBasis
  GoeDefinitions GoePairs GoeParseval GoeSynthesis
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonBilinear.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_symmetric_dimension n := S (goe_vector_index n).

Definition paper_main_symmetric_coordinates n (T : matrix n) k :=
  trace_pair n (goe_basis n k) T.

Definition paper_main_gaussian_feature_row n i (xs : list R) : matrix n :=
  goe_matrix n (tuple_build R^o (goe_vector_index n)
    (fun k => List.nth (i*paper_main_symmetric_dimension n+k) xs 0)).

Definition paper_main_gaussian_feature_pairing n N u (T : matrix n) xs :=
  finite_sum (fun i => u i*trace_pair n (paper_main_gaussian_feature_row n i xs) T)
    (List.seq 0 N).

Lemma paper_main_symmetric_dimension_formula n :
  paper_main_symmetric_dimension n = (S n*S(S n)/2)%nat.
Proof.
unfold paper_main_symmetric_dimension; rewrite goe_vector_dimension; apply goe_pairs_length.
Qed.

Lemma paper_main_feature_coordinate_sum n f :
  coordinate_sum n f = finite_sum f (List.seq 0 (S n)).
Proof.
rewrite goe_coordinate_sum_seq.
induction (List.seq 0 (S n)) as [|i I IH]; simpl; [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma paper_main_symmetric_coordinate_pairing n (T U : matrix n) :
  symmetric_matrix n T -> symmetric_matrix n U ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_symmetric_coordinates n T) (paper_main_symmetric_coordinates n U) = trace_pair n T U.
Proof.
intros HT HU.
unfold paper_main_gordon_dot, paper_main_symmetric_coordinates, paper_main_symmetric_dimension.
rewrite <- paper_main_feature_coordinate_sum.
rewrite (goe_basis_sum n (fun E => trace_pair n E T*trace_pair n E U)).
apply goe_symmetric_parseval; assumption.
Qed.

Lemma paper_main_symmetric_coordinate_norm n (T : matrix n) :
  symmetric_matrix n T ->
  euclidean_norm (paper_main_symmetric_coordinates n T) (List.seq 0 (paper_main_symmetric_dimension n)) = (`|T|)%R.
Proof.
intro HT.
pose proof (paper_main_gordon_euclidean_squared (paper_main_symmetric_dimension n) (paper_main_symmetric_coordinates n T)) as HE.
rewrite (paper_main_symmetric_coordinate_pairing n T T HT HT) in HE.
assert (HTT : trace_pair n T T = (`|T|)%R^2).
{ rewrite matrix_frobenius_norm_squared; unfold trace_pair.
  apply coordinate_sum_ext; intros i Hi; apply coordinate_sum_ext; intros j Hj.
  rewrite (HT j i Hj Hi); ring. }
rewrite HTT in HE.
pose proof (paper_main_gordon_euclidean_nonnegative (paper_main_symmetric_dimension n) (paper_main_symmetric_coordinates n T)).
assert (HN : 0 <= (`|T|)%R).
{ apply (ssrbool.elimT RleP); apply normr_ge0. }
nra.
Qed.

Lemma paper_main_gaussian_feature_row_symmetric n i xs :
  symmetric_matrix n (paper_main_gaussian_feature_row n i xs).
Proof.
apply goe_matrix_symmetric.
Qed.

Lemma paper_main_gaussian_feature_row_coordinate n i xs k :
  (k < paper_main_symmetric_dimension n)%nat ->
  paper_main_symmetric_coordinates n (paper_main_gaussian_feature_row n i xs) k =
  goe_scale n*List.nth (i*paper_main_symmetric_dimension n+k) xs 0.
Proof.
intro Hk.
unfold paper_main_symmetric_coordinates, paper_main_gaussian_feature_row.
rewrite symmetric_trace_pair_comm, goe_matrix_trace.
f_equal.
transitivity (coordinate_sum (goe_vector_index n) (fun j =>
 vector_entry (goe_vector_index n) (tuple_build R^o (goe_vector_index n)
  (fun k => List.nth (i*paper_main_symmetric_dimension n+k) xs 0)) j *
 (if Nat.eqb j k then 1 else 0))).
- apply coordinate_sum_ext; intros j Hj; rewrite goe_basis_orthonormal; try reflexivity;
  unfold paper_main_symmetric_dimension in Hk; lia.
- rewrite gradient_coordinate_sum_select by (unfold paper_main_symmetric_dimension in Hk; lia).
  unfold vector_entry.
  rewrite (tuple_entry_build R^o (goe_vector_index n) k
   (fun j => List.nth (i*paper_main_symmetric_dimension n+j) xs 0));
   [reflexivity|unfold paper_main_symmetric_dimension in Hk; lia].
Qed.

Theorem paper_main_gaussian_feature_pairing_coordinates n N u (T : matrix n) xs :
  paper_main_gaussian_feature_pairing n N u T xs =
  goe_scale n * paper_main_gordon_matrix_value N (paper_main_symmetric_dimension n)
    u (paper_main_symmetric_coordinates n T) xs.
Proof.
unfold paper_main_gaussian_feature_pairing, paper_main_gordon_matrix_value.
rewrite <- finite_sum_scale; apply finite_sum_ext; intros i Hi.
unfold paper_main_gaussian_feature_row; rewrite goe_matrix_trace, paper_main_feature_coordinate_sum.
rewrite <- finite_sum_scale; rewrite <- finite_sum_scale.
unfold paper_main_symmetric_dimension, paper_main_symmetric_coordinates.
rewrite <- finite_sum_scale.
apply finite_sum_ext; intros k Hk; apply List.in_seq in Hk.
unfold vector_entry.
rewrite (tuple_entry_build R^o (goe_vector_index n) k
 (fun j => List.nth (i*S(goe_vector_index n)+j) xs 0)) by lia.
ring.
Qed.

Lemma paper_main_gaussian_feature_scale n :
  sqrt (INR (S n))*goe_scale n = sqrt 2.
Proof.
unfold goe_scale.
rewrite <- sqrt_mult.
- f_equal; assert (H : INR (S n) <> 0) by (apply not_0_INR; lia); field; exact H.
- apply pos_INR.
- apply Rlt_le; apply Rdiv_lt_0_compat; [lra|apply lt_0_INR; lia].
Qed.
