(* Dimension-free normalized finite-prior entropy and feature constants. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import PaperMainGaussianFeatureCoordinates PaperMainGordonEntropy
  PaperMainGordonEntropyMargin PaperMainUnsatParameters.
Open Scope R_scope.

Lemma paper_main_loss_joint_dimension n :
  INR(S(S(paper_main_symmetric_dimension n))) <= 3*(INR(S n))^2.
Proof.
rewrite paper_main_symmetric_dimension_formula.
assert (H : (2*(S n*S(S n)/2)<=S n*S(S n))%nat) by (apply Nat.mul_div_le; lia).
pose proof(le_INR _ _ H) as HR.
rewrite !mult_INR, !S_INR in HR.
rewrite !S_INR.
change (INR 0) with 0 in HR.
pose proof(pos_INR n). Stdlib.micromega.Lra.nra.
Qed.

Theorem paper_main_loss_feature_constant c : 0<c ->
  exists L, 0<L /\ c*L^2=109 /\
    forall N d, c*(INR d)^2<=INR N -> 109*(INR d)^2<=INR N*L^2.
Proof.
intro Hc; exists(sqrt(109/c)).
assert (Hq : 0<109/c) by (apply Rdiv_lt_0_compat; Stdlib.micromega.Lra.lra).
assert (Hs : 0<sqrt(109/c)) by (apply sqrt_lt_R0; exact Hq).
assert (HE : c*(sqrt(109/c))^2=109).
{ rewrite pow2_sqrt by Stdlib.micromega.Lra.lra; field; Stdlib.micromega.Lra.lra. }
split; [exact Hs|]; split; [exact HE|].
intros N d HN; pose proof(Rmult_le_compat_r ((sqrt(109/c))^2) _ _
  (pow2_ge_0 _) HN) as H; Stdlib.micromega.Lra.nra.
Qed.

Lemma paper_main_loss_joint_radius L q b :
  0<=L -> q<=4 -> Rabs b<=L -> 2*q+b^2<=(L+3)^2.
Proof.
intros HL Hq Hb; pose proof(Rle_abs b); pose proof(Rle_abs(-b)) as Hneg.
rewrite Rabs_Ropp in Hneg; Stdlib.micromega.Lra.nra.
Qed.
