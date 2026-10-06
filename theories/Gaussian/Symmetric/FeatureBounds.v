(* Gaussian symmetric-feature bounds via the existing orthonormal basis.
   The true matrix dimension is p = S n. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype.
From EllipsoidFitting Require Import Soft.Definitions Matrix.Definitions
  Tensor.Definitions Goe.Definitions Goe.MatrixBasis Gordon.ProcessCovariance
  Gordon.Scalar Gordon.Bilinear Gordon.OperatorNet
  Gaussian.Symmetric.Coordinates.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Theorem paper_main_gaussian_feature_bound n N u (T : matrix n) xs :
  List.length xs = (N*paper_main_symmetric_dimension n)%nat ->
  symmetric_matrix n T ->
  Rabs (paper_main_gaussian_feature_pairing n N u T xs) <=
  goe_scale n * paper_main_gordon_operator_norm N (paper_main_symmetric_dimension n) xs *
    euclidean_norm u (List.seq 0 N) * (`|T|)%R.
Proof.
intros Hxs HT.
pose proof (proj2 (paper_main_gordon_operator_norm_bound N (paper_main_symmetric_dimension n) xs Hxs) u (paper_main_symmetric_coordinates n T)) as H.
rewrite (paper_main_symmetric_coordinate_norm n T HT) in H.
rewrite paper_main_gaussian_feature_pairing_coordinates, Rabs_mult.
rewrite (Rabs_right (goe_scale n)) by (pose proof (goe_scale_positive n); lra).
eapply Rle_trans; [apply Rmult_le_compat_l; [pose proof (goe_scale_positive n); lra|exact H]|].
right; ring.
Qed.

Theorem paper_main_gaussian_feature_normalized_bound n N u (T : matrix n) xs :
  List.length xs = (N*paper_main_symmetric_dimension n)%nat ->
  symmetric_matrix n T ->
  Rabs (sqrt(INR(S n))*paper_main_gaussian_feature_pairing n N u T xs) <=
  sqrt 2 * paper_main_gordon_operator_norm N (paper_main_symmetric_dimension n) xs *
    euclidean_norm u (List.seq 0 N) * (`|T|)%R.
Proof.
intros Hxs HT.
rewrite Rabs_mult, (Rabs_right (sqrt (INR (S n)))) by (pose proof (sqrt_pos (INR (S n))); lra).
eapply Rle_trans.
- apply Rmult_le_compat_l; [apply sqrt_pos|apply paper_main_gaussian_feature_bound; assumption].
- right; rewrite <- (paper_main_gaussian_feature_scale n); ring.
Qed.

Corollary paper_main_gaussian_feature_normalized_good n N xs B :
  List.length xs = (N*paper_main_symmetric_dimension n)%nat ->
  paper_main_gordon_operator_norm N (paper_main_symmetric_dimension n) xs <= 2*B ->
  forall u (T : matrix n), symmetric_matrix n T ->
  Rabs (sqrt(INR(S n))*paper_main_gaussian_feature_pairing n N u T xs) <=
  (2*sqrt 2*B) * euclidean_norm u (List.seq 0 N) * (`|T|)%R.
Proof.
intros Hxs HL u T HT.
eapply Rle_trans; [apply paper_main_gaussian_feature_normalized_bound; assumption|].
replace (2*sqrt 2*B) with (sqrt 2*(2*B)) by ring.
apply Rmult_le_compat_r.
- apply (ssrbool.elimT RleP); apply normr_ge0.
- apply Rmult_le_compat_r; [apply paper_main_gordon_euclidean_nonnegative|].
  apply Rmult_le_compat_l; [apply sqrt_pos|exact HL].
Qed.
