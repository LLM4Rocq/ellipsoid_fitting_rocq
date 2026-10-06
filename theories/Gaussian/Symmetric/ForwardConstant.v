(* The Gaussian forward-map clause, uniform in a lower density bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure lebesgue_measure.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  GaussianProbabilityProductDefinitions Row.ArrayDefinitions
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Spectral.Transport
  Spectral.Duality Gordon.ProcessCovariance Gordon.Bilinear Gordon.Entropy
  Gaussian.Symmetric.FeatureTail Gaussian.Symmetric.JointWidth
  Gaussian.Symmetric.DimensionBounds.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_forward_constant rho :=
  4*sqrt(paper_main_gordon_entropy_constant (1/4)*(1+2/rho)+1).

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
