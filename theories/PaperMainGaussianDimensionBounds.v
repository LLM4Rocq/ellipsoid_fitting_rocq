(* Explicit dimension-uniform constants for the coarse Gaussian estimate. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GoeDefinitions GoePairs PaperMainGordonEntropy
  PaperMainGaussianFeatureCoordinates PaperMainGaussianFeatureTail PaperMainGaussianJointFeature.
Open Scope R_scope.

Definition paper_main_gaussian_adjoint_constant kappa :=
  4*sqrt(paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1).

Lemma paper_main_symmetric_dimension_upper n :
  (paper_main_symmetric_dimension n <= S n*S n)%nat.
Proof.
unfold paper_main_symmetric_dimension; rewrite goe_vector_dimension.
pose proof (goe_pairs_length_twice n); nia.
Qed.

Lemma paper_main_gaussian_joint_width_upper n :
  INR(paper_main_gaussian_joint_width n) <= 2*(INR(S n))^2.
Proof.
pose proof (le_INR _ _ (paper_main_symmetric_dimension_upper n)) as HD.
rewrite mult_INR in HD.
unfold paper_main_gaussian_joint_width; rewrite plus_INR.
assert (Hp : 1 <= INR(S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
nra.
Qed.

Lemma paper_main_gaussian_adjoint_constant_positive kappa :
  0 <= kappa -> 0 < paper_main_gaussian_adjoint_constant kappa.
Proof.
intro Hk.
unfold paper_main_gaussian_adjoint_constant.
assert (H : 0 < sqrt(paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1)).
{ apply sqrt_lt_R0; pose proof paper_main_gaussian_entropy_positive; nra. }
lra.
Qed.

Lemma paper_main_gaussian_joint_threshold_bound n N kappa :
  0 <= kappa -> INR N <= kappa*(INR(S n))^2 ->
  2*sqrt 2*paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) ((INR(S n))^2) <=
  paper_main_gaussian_adjoint_constant kappa*INR(S n).
Proof.
intros Hk HN.
assert (Hp : 0 < INR(S n)) by (apply lt_0_INR; lia).
assert (Ht : 0 < (INR(S n))^2) by nra.
pose proof (paper_main_gaussian_operator_threshold_square N (paper_main_gaussian_joint_width n) ((INR(S n))^2) Ht) as HB.
pose proof (paper_main_gaussian_operator_threshold_positive N (paper_main_gaussian_joint_width n) ((INR(S n))^2) Ht) as HBpos.
pose proof (paper_main_gaussian_joint_width_upper n) as HK.
pose proof paper_main_gaussian_entropy_positive as HC.
pose proof (pow2_sqrt 2 ltac:(lra)) as H2.
pose proof (sqrt_pos 2) as H2pos.
assert (HR : (sqrt(paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1))^2 = paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1) by (apply pow2_sqrt; nra).
pose proof (sqrt_pos (paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1)) as HRpos.
unfold paper_main_gaussian_adjoint_constant.
assert (HBbound : (paper_main_gaussian_operator_threshold N (paper_main_gaussian_joint_width n) ((INR(S n))^2))^2 <= 2*(paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1)*(INR(S n))^2) by nra.
apply Rsqr_incr_0.
- rewrite !Rsqr_mult; unfold Rsqr.
  assert (H2' : sqrt 2*sqrt 2=2) by nra.
  assert (HR' : sqrt(paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1)*sqrt(paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1)=paper_main_gordon_entropy_constant (1/4)*(kappa+2)+1) by nra.
  rewrite H2', HR'; nra.
- apply Rmult_le_pos; [nra|lra].
- apply Rmult_le_pos; [nra|lra].
Qed.

Lemma paper_main_gaussian_remove_dimension_scale p a b :
  0 < p -> Rabs(sqrt p*a) <= p*b -> Rabs a <= sqrt p*b.
Proof.
intros Hp H.
rewrite Rabs_mult, (Rabs_right (sqrt p)) in H by (pose proof (sqrt_pos p); lra).
apply (Rmult_le_reg_l (sqrt p)); [apply sqrt_lt_R0; exact Hp|].
rewrite <- Rmult_assoc, sqrt_sqrt; [exact H|lra].
Qed.
