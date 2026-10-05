(* The Gaussian forward-map clause, uniform in a lower density bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure lebesgue_measure.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianProbabilityProductDefinitions RowArrayDefinitions PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainMatrixTransport
  PaperMainMatrixDuality PaperMainGordonProcessCovariance PaperMainGordonBilinear
  PaperMainGordonEntropy PaperMainGaussianFeatureTail PaperMainGaussianJointFeature
  PaperMainGaussianJointTail PaperMainGaussianDimensionBounds.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_forward n (T : 'M[R]_(S n)) xs i :=
  sqrt(INR(S n))*paper_main_pairing (paper_main_matrix_to_public n (gaussian_row_matrix n 0 i xs)) T.

Definition paper_main_gaussian_forward_constant rho :=
  4*sqrt(paper_main_gordon_entropy_constant (1/4)*(1+2/rho)+1).

Lemma paper_main_euclidean_duality N v L :
  0 <= L ->
  (forall u, Rabs(finite_sum (fun i => u i*v i) (List.seq 0 N)) <= L*euclidean_norm u (List.seq 0 N)) ->
  euclidean_norm v (List.seq 0 N) <= L.
Proof.
intros HL H.
have HH := H v.
have HE := paper_main_gordon_euclidean_squared N v.
have HP := paper_main_gordon_euclidean_nonnegative N v.
unfold paper_main_gordon_dot in HE.
have HA := Rle_abs (finite_sum (fun i=>v i*v i) (List.seq 0 N)).
nra.
Qed.

Lemma paper_main_gaussian_forward_pairing n N u T xs :
  finite_sum (fun i => u i*paper_main_gaussian_forward n T xs i) (List.seq 0 N) =
  sqrt(INR(S n))*paper_main_public_joint_pairing n N u T xs.
Proof.
unfold paper_main_gaussian_forward, paper_main_public_joint_pairing.
rewrite <- finite_sum_scale; apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gaussian_forward_constant_positive rho :
  0 < rho -> 0 < paper_main_gaussian_forward_constant rho.
Proof.
intro Hr.
have Hdiv : 0 < 2/rho by apply Rdiv_lt_0_compat; lra.
have HC := paper_main_gaussian_entropy_positive.
have HS : 0 < sqrt(paper_main_gordon_entropy_constant (1/4)*(1+2/rho)+1) by apply sqrt_lt_R0; nra.
unfold paper_main_gaussian_forward_constant; lra.
Qed.

Lemma paper_main_gaussian_forward_threshold n N rho :
  0 < rho -> Nat.lt 0 N -> rho*(INR(S n))^2 <= INR N ->
  2*sqrt 2*paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) (INR N/2) <=
  paper_main_gaussian_forward_constant rho*sqrt(INR N).
Proof.
intros Hr HN Hratio.
have HNR : 0 < INR N by apply lt_0_INR; exact HN.
have HK := paper_main_gaussian_joint_width_upper n.
have HC := paper_main_gaussian_entropy_positive.
have Hdiv : 0 < 2/rho by apply Rdiv_lt_0_compat; lra.
have Hmul : (2/rho)*rho = 2 by field; lra.
have HK' : INR(paper_main_gaussian_joint_width n) <= (2/rho)*INR N.
{ have H := Rmult_le_compat_l (2/rho) (rho*(INR(S n))^2) (INR N) (Rlt_le _ _ Hdiv) Hratio.
  rewrite <- Rmult_assoc, Hmul in H; lra. }
have HB := paper_main_gaussian_operator_threshold_square N (paper_main_gaussian_joint_width n) (INR N/2) ltac:(lra).
have HBpos := paper_main_gaussian_operator_threshold_positive N (paper_main_gaussian_joint_width n) (INR N/2) ltac:(lra).
have HNroot := sqrt_sqrt (INR N) (Rlt_le _ _ HNR).
have HNpos := sqrt_pos (INR N).
have H2 := sqrt_sqrt 2 ltac:(lra).
have H2pos := sqrt_pos 2.
have HR : sqrt(paper_main_gordon_entropy_constant (1/4)*(1+2/rho)+1)*sqrt(paper_main_gordon_entropy_constant (1/4)*(1+2/rho)+1) = paper_main_gordon_entropy_constant (1/4)*(1+2/rho)+1 by apply sqrt_sqrt; nra.
have HRpos := sqrt_pos (paper_main_gordon_entropy_constant (1/4)*(1+2/rho)+1).
unfold paper_main_gaussian_forward_constant.
apply Rsqr_incr_0.
- rewrite !Rsqr_mult; unfold Rsqr; rewrite H2 HR HNroot; nra.
- apply Rmult_le_pos; [nra|lra].
- apply Rmult_le_pos; [nra|exact HNpos].
Qed.

Theorem paper_main_gaussian_forward_exceptional_event rho n N :
  0 < rho -> Nat.lt 0 N -> rho*(INR(S n))^2 <= INR N ->
  exists E : set ((N*paper_main_gaussian_joint_width n).-tuple (measurableTypeR R)),
    measurable E /\
    (gaussian_product_law (N*paper_main_gaussian_joint_width n) E <= (2*exp(-INR N/2))%:E)%E /\
    forall x, ~ E x -> forall (T : 'M[R]_(S n)), paper_main_symmetric T ->
    euclidean_norm (paper_main_gaussian_forward n T (tval x)) (List.seq 0 N) <=
      paper_main_gaussian_forward_constant rho*sqrt(INR N)*paper_main_frobenius T.
Proof.
intros Hr HN Hratio.
have HNR : 0 < INR N by apply lt_0_INR; exact HN.
destruct (paper_main_public_joint_feature_exceptional_event n N (INR N/2) HN ltac:(lra)) as [E [HE [HP HB]]].
exists E; split; [exact HE|]; split.
- replace (-INR N/2) with (-(INR N/2)) by field; exact HP.
- intros x Hx T HT.
  apply paper_main_euclidean_duality.
  + apply Rmult_le_pos; [apply Rmult_le_pos; [have HC := paper_main_gaussian_forward_constant_positive rho Hr; lra|apply sqrt_pos]|apply paper_main_frobenius_nonnegative].
  + intros u; rewrite paper_main_gaussian_forward_pairing.
    eapply Rle_trans; [apply HB; [exact Hx|exact HT]|].
    replace (paper_main_gaussian_forward_constant rho*sqrt(INR N)*paper_main_frobenius T*euclidean_norm u (List.seq 0 N)) with (paper_main_gaussian_forward_constant rho*sqrt(INR N)*euclidean_norm u (List.seq 0 N)*paper_main_frobenius T) by ring.
    apply Rmult_le_compat_r; [apply paper_main_frobenius_nonnegative|].
    apply Rmult_le_compat_r; [apply paper_main_gordon_euclidean_nonnegative|].
    apply paper_main_gaussian_forward_threshold; assumption.
Qed.
