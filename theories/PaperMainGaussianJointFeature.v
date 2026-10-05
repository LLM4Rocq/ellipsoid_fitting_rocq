(* Gaussian endpoint of the actual interleaved row input.
   Zero-padding the test coordinates avoids a separate marginal-law lemma. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  MatrixDefinitions MatrixCoordinates OperatorDefinitions TensorDefinitions
  VectorCoordinateDefinitions QuadraticDefinitions GoeDefinitions GoeSynthesis
  JointDefinitions RowCoordinateDefinitions RowArrayDefinitions
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonBilinear
  PaperMainGordonOperatorNet PaperMainGaussianFeatureCoordinates.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_gaussian_joint_width n := (S n+paper_main_symmetric_dimension n)%nat.

Definition paper_main_gaussian_pad p (v : nat -> R) j :=
  if Nat.ltb j p then 0 else v (j-p)%nat.

Definition paper_main_gaussian_joint_pairing n N u (T : matrix n) xs :=
  finite_sum (fun i => u i*trace_pair n (gaussian_row_matrix n 0 i xs) T) (List.seq 0 N).

Lemma paper_main_gaussian_pad_sum p d f v :
  finite_sum (fun j => f j*paper_main_gaussian_pad p v j) (List.seq 0 (p+d)) =
  finite_sum (fun k => f (p+k)%nat*v k) (List.seq 0 d).
Proof.
rewrite finite_sum_seq_split.
assert (Hz : finite_sum (fun j => f j*paper_main_gaussian_pad p v j) (List.seq 0 p) = 0).
{ transitivity (finite_sum (fun _ => 0) (List.seq 0 p)); [|apply finite_sum_zero].
  apply finite_sum_ext; intros j Hj; apply List.in_seq in Hj.
  unfold paper_main_gaussian_pad; rewrite (proj2 (Nat.ltb_lt j p) ltac:(lia)); ring. }
rewrite Hz, Rplus_0_l.
apply finite_sum_ext; intros k Hk; unfold paper_main_gaussian_pad.
rewrite (proj2 (Nat.ltb_ge (p+k) p) ltac:(lia)).
replace (p+k-p)%nat with k by lia; reflexivity.
Qed.

Lemma paper_main_gaussian_pad_norm p d v :
  euclidean_norm (paper_main_gaussian_pad p v) (List.seq 0 (p+d)) =
  euclidean_norm v (List.seq 0 d).
Proof.
pose proof (paper_main_gordon_euclidean_squared (p+d) (paper_main_gaussian_pad p v)) as H1.
pose proof (paper_main_gordon_euclidean_squared d v) as H2.
unfold paper_main_gordon_dot in H1, H2.
rewrite paper_main_gaussian_pad_sum in H1.
assert (He : finite_sum (fun k => paper_main_gaussian_pad p v (p+k)*v k) (List.seq 0 d) = finite_sum (fun k => v k*v k) (List.seq 0 d)).
{ apply finite_sum_ext; intros k Hk; unfold paper_main_gaussian_pad.
  rewrite (proj2 (Nat.ltb_ge (p+k) p) ltac:(lia)); replace (p+k-p)%nat with k by lia; reflexivity. }
rewrite He in H1.
pose proof (paper_main_gordon_euclidean_nonnegative (p+d) (paper_main_gaussian_pad p v)).
pose proof (paper_main_gordon_euclidean_nonnegative d v); nra.
Qed.

Lemma paper_main_gaussian_joint_row n i xs :
  gaussian_row_matrix n 0 i xs =
  goe_matrix n (tuple_build R^o (goe_vector_index n)
    (fun k => List.nth (i*paper_main_gaussian_joint_width n+S n+k) xs 0)).
Proof.
assert (Hz : snd (gaussian_row_pair n i xs) = tuple_build R^o (goe_vector_index n)
 (fun k => List.nth (i*paper_main_gaussian_joint_width n+S n+k) xs 0)).
{ apply (tuple_ext R^o (goe_vector_index n)); intros k Hk.
  unfold gaussian_row_pair, joint_vector_of_list; simpl snd.
  unfold vector_of_list; rewrite !tuple_entry_build by exact Hk.
  change (List.nth k (List.skipn (S n) (row_chunk (S n+S(goe_vector_index n)) i xs)) 0 = List.nth (i*paper_main_gaussian_joint_width n+S n+k) xs 0).
  rewrite nth_skipn_add; unfold row_chunk.
  rewrite nth_firstn_lt by lia; rewrite nth_skipn_add.
  unfold paper_main_gaussian_joint_width, paper_main_symmetric_dimension.
  f_equal; lia. }
unfold gaussian_row_matrix; rewrite Hz; unfold joint_matrix.
replace (0/INR(S n)) with 0 by (unfold Rdiv; ring).
replace (1-0) with 1 by ring.
rewrite sqrt_0, sqrt_1.
apply matrix_ext; intros a b Ha Hb.
rewrite matrix_entry_add, matrix_entry_scale; unfold quadratic_matrix.
rewrite matrix_entry_build by assumption; rewrite matrix_entry_zero; ring.
Qed.

Lemma paper_main_gaussian_joint_pairing_coordinates n N u (T : matrix n) xs :
  paper_main_gaussian_joint_pairing n N u T xs =
  goe_scale n*paper_main_gordon_matrix_value N (paper_main_gaussian_joint_width n)
    u (paper_main_gaussian_pad (S n) (paper_main_symmetric_coordinates n T)) xs.
Proof.
unfold paper_main_gaussian_joint_pairing, paper_main_gordon_matrix_value.
rewrite <- finite_sum_scale; apply finite_sum_ext; intros i Hi.
rewrite paper_main_gaussian_joint_row, goe_matrix_trace, paper_main_feature_coordinate_sum.
unfold paper_main_gaussian_joint_width at 2.
fold (paper_main_gaussian_joint_width n).
assert (HP : finite_sum (fun j => u i*paper_main_gaussian_pad (S n) (paper_main_symmetric_coordinates n T) j*List.nth (i*paper_main_gaussian_joint_width n+j) xs 0) (List.seq 0 (paper_main_gaussian_joint_width n)) = finite_sum (fun k => u i*List.nth (i*paper_main_gaussian_joint_width n+(S n+k)) xs 0*paper_main_symmetric_coordinates n T k) (List.seq 0 (paper_main_symmetric_dimension n))).
{ transitivity (finite_sum (fun j => (u i*List.nth (i*paper_main_gaussian_joint_width n+j) xs 0)*paper_main_gaussian_pad (S n) (paper_main_symmetric_coordinates n T) j) (List.seq 0 (paper_main_gaussian_joint_width n))).
  - apply finite_sum_ext; intros; ring.
  - apply paper_main_gaussian_pad_sum. }
rewrite HP.
rewrite <- finite_sum_scale; rewrite <- finite_sum_scale; rewrite <- finite_sum_scale.
unfold paper_main_symmetric_dimension, paper_main_symmetric_coordinates.
apply finite_sum_ext; intros k Hk; apply List.in_seq in Hk.
unfold vector_entry.
rewrite (tuple_entry_build R^o (goe_vector_index n) k (fun l=>List.nth (i*paper_main_gaussian_joint_width n+S n+l) xs 0)) by lia.
replace (i*paper_main_gaussian_joint_width n+(S n+k))%nat with (i*paper_main_gaussian_joint_width n+S n+k)%nat by lia.
ring.
Qed.

Theorem paper_main_gaussian_joint_normalized_bound n N u (T : matrix n) xs :
  List.length xs = (N*paper_main_gaussian_joint_width n)%nat ->
  symmetric_matrix n T ->
  Rabs (sqrt(INR(S n))*paper_main_gaussian_joint_pairing n N u T xs) <=
  sqrt 2*paper_main_gordon_operator_norm N (paper_main_gaussian_joint_width n) xs *
    euclidean_norm u (List.seq 0 N)*(`|T|)%R.
Proof.
intros Hxs HT.
pose proof (proj2 (paper_main_gordon_operator_norm_bound N (paper_main_gaussian_joint_width n) xs Hxs) u (paper_main_gaussian_pad (S n) (paper_main_symmetric_coordinates n T))) as H.
unfold paper_main_gaussian_joint_width in H.
rewrite paper_main_gaussian_pad_norm, (paper_main_symmetric_coordinate_norm n T HT) in H.
rewrite paper_main_gaussian_joint_pairing_coordinates.
rewrite <- Rmult_assoc, paper_main_gaussian_feature_scale.
rewrite Rabs_mult, (Rabs_right (sqrt 2)) by (pose proof (sqrt_pos 2); lra).
eapply Rle_trans; [apply Rmult_le_compat_l; [apply sqrt_pos|exact H]|].
unfold paper_main_gaussian_joint_width; right; ring.
Qed.
