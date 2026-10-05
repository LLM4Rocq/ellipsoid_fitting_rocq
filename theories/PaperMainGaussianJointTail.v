(* An unconditional exceptional-event bound for the actual Gaussian endpoint,
   stated on the public matrices and the full interleaved input law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure lebesgue_measure.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums MatrixDefinitions
  TensorDefinitions GaussianProbabilityProductDefinitions RowArrayDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainMatrixTransport PaperMainGordonBilinear PaperMainGordonOperatorNet
  PaperMainGaussianOperatorTail PaperMainGaussianFeatureCoordinates
  PaperMainGaussianFeatureTail PaperMainGaussianJointFeature.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_public_joint_pairing n N u (T : 'M[R]_(S n)) xs :=
  finite_sum (fun i => u i*paper_main_pairing
    (paper_main_matrix_to_public n (gaussian_row_matrix n 0 i xs)) T) (List.seq 0 N).

Lemma paper_main_public_joint_pairing_transport n N u (T : 'M[R]_(S n)) xs :
  paper_main_symmetric T ->
  paper_main_public_joint_pairing n N u T xs =
  paper_main_gaussian_joint_pairing n N u (paper_main_matrix_from_public n T) xs.
Proof.
intro HT.
unfold paper_main_public_joint_pairing, paper_main_gaussian_joint_pairing.
apply finite_sum_ext; intros i Hi.
rewrite paper_main_matrix_public_pairing; [apply paper_main_matrix_internal_symmetric; exact HT|].
by rewrite paper_main_matrix_public_roundtrip.
Qed.

Theorem paper_main_public_joint_feature_bound n N u (T : 'M[R]_(S n)) xs :
  List.length xs = Nat.mul N (paper_main_gaussian_joint_width n) ->
  paper_main_symmetric T ->
  Rabs (sqrt(INR(S n))*paper_main_public_joint_pairing n N u T xs) <=
  sqrt 2*paper_main_gordon_operator_norm N (paper_main_gaussian_joint_width n) xs *
    euclidean_norm u (List.seq 0 N)*paper_main_frobenius T.
Proof.
intros Hxs HT.
rewrite (paper_main_public_joint_pairing_transport n N u T xs HT).
rewrite <- (paper_main_matrix_internal_frobenius n T).
apply paper_main_gaussian_joint_normalized_bound; [exact Hxs|].
apply paper_main_matrix_internal_symmetric; exact HT.
Qed.

Theorem paper_main_public_joint_feature_exceptional_event n N t :
  Nat.lt 0 N -> 0 < t ->
  exists E : set ((N*paper_main_gaussian_joint_width n).-tuple (measurableTypeR R)),
    measurable E /\
    (gaussian_product_law (N*paper_main_gaussian_joint_width n) E <= (2*exp(-t))%:E)%E /\
    forall x, ~ E x -> forall u (T : 'M[R]_(S n)), paper_main_symmetric T ->
    Rabs (sqrt(INR(S n))*paper_main_public_joint_pairing n N u T (tval x)) <=
    (2*sqrt 2*paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) t)*
      euclidean_norm u (List.seq 0 N)*paper_main_frobenius T.
Proof.
intros HN Ht.
exists [set x | Rlt (2*paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) t)
 (paper_main_gaussian_operator_random N (paper_main_gaussian_joint_width n) x)].
split; [apply paper_main_gaussian_operator_tail_measurable|].
split.
- apply paper_main_gaussian_operator_exponential_tail; [exact HN|unfold paper_main_gaussian_joint_width; lia|exact Ht].
- intros x Hx u T HT.
  have HL : paper_main_gordon_operator_norm N (paper_main_gaussian_joint_width n) (tval x) <= 2*paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) t by apply Rnot_lt_le; exact Hx.
  eapply Rle_trans; [apply paper_main_public_joint_feature_bound; [exact: size_tuple|exact HT]|].
  replace (2*sqrt 2*paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) t) with (sqrt 2*(2*paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) t)) by ring.
  apply Rmult_le_compat_r.
  + apply/RleP; apply sqrtr_ge0.
  + apply Rmult_le_compat_r; [apply paper_main_gordon_euclidean_nonnegative|].
    apply Rmult_le_compat_l; [apply sqrt_pos|exact HL].
Qed.
