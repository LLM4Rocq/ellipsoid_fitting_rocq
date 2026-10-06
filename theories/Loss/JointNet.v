(* Internal finite nets for bounded symmetric matrices together with a scalar offset. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra PaperMainDefinitions Geometry.Homogeneous
  Geometry.HeadFrobenius Gaussian.Symmetric.Coordinates
  Gordon.ProcessCovariance Gordon.Nets Gordon.Entropy Loss.BallNet
  Head.SmallBallNet.
Open Scope R_scope.

Definition paper_main_loss_joint_code n (A : 'M[R]_(S n)) b radius k :=
  paper_main_head_small_ball_pcode n A b k/radius.

Lemma paper_main_loss_joint_sigma d (A : 'M[R]_d) b :
  paper_main_head_small_ball_sigma2 A b = 2*paper_main_frobenius A^2+b^2.
Proof. by rewrite /paper_main_head_small_ball_sigma2 -(pmh_frobenius_sqr d A) -RpowE. Qed.

Lemma paper_main_loss_joint_code_norm n A b radius : paper_main_symmetric A ->
  paper_main_gordon_dot (S(paper_main_symmetric_dimension n))
    (paper_main_loss_joint_code n A b radius) (paper_main_loss_joint_code n A b radius)=
    (2*paper_main_frobenius A^2+b^2)/(radius^2).
Proof.
intro HA; rewrite <-(paper_main_loss_joint_sigma _ A b), <-(paper_main_head_small_ball_pcode_norm n A b HA).
unfold paper_main_gordon_dot,paper_main_loss_joint_code,Rdiv.
transitivity ((/radius*/radius)*finite_sum (fun i =>
  paper_main_head_small_ball_pcode n A b i*paper_main_head_small_ball_pcode n A b i)
  (List.seq 0 (S(paper_main_symmetric_dimension n)))).
- rewrite <-finite_sum_scale; apply finite_sum_ext; intros; ring.
- rewrite <-Rinv_mult; simpl; rewrite Rmult_1_r; ring.
Qed.

Lemma paper_main_loss_joint_code_distance n A B b c radius :
  paper_main_symmetric A -> paper_main_symmetric B ->
  paper_main_gordon_dot (S(paper_main_symmetric_dimension n))
    (fun i => paper_main_loss_joint_code n A b radius i-paper_main_loss_joint_code n B c radius i)
    (fun i => paper_main_loss_joint_code n A b radius i-paper_main_loss_joint_code n B c radius i)=
    (2*paper_main_frobenius (A-B)%R^2+(b-c)^2)/(radius^2).
Proof.
intros HA HB; rewrite <-(paper_main_loss_joint_sigma _ (A-B)%R (b-c)),
  <-(paper_main_head_small_ball_pcode_dist n A B b c HA HB).
unfold paper_main_gordon_dot,paper_main_loss_joint_code,Rdiv.
transitivity ((/radius*/radius)*finite_sum (fun i =>
  (paper_main_head_small_ball_pcode n A b i-paper_main_head_small_ball_pcode n B c i)*
  (paper_main_head_small_ball_pcode n A b i-paper_main_head_small_ball_pcode n B c i))
  (List.seq 0 (S(paper_main_symmetric_dimension n)))).
- rewrite <-finite_sum_scale; apply finite_sum_ext; intros; ring.
- rewrite <-Rinv_mult; simpl; rewrite Rmult_1_r; ring.
Qed.

Theorem paper_main_loss_joint_net n (T : 'M[R]_(S n) -> R -> Prop) radius delta :
  0<radius -> 0<delta -> (exists A b, T A b) ->
  (forall A b, T A b -> paper_main_symmetric A /\ 2*paper_main_frobenius A^2+b^2<=radius^2) ->
  exists s (A : nat -> 'M[R]_(S n)) (b : nat -> R), (0<s)%coq_nat /\
    (forall j, (j<s)%coq_nat -> T (A j) (b j)) /\
    (forall B c, T B c -> exists j, (j<s)%coq_nat /\
      2*paper_main_frobenius (B-A j)%R^2+(c-b j)^2<=delta^2) /\
    Rpower.ln(INR s)<=paper_main_gordon_entropy_constant (delta/radius)*INR(S(S(paper_main_symmetric_dimension n))).
Proof.
intros Hr Hd [A0 [b0 H0]] HT.
set (Y := fun u : nat -> R => exists A b, T A b /\ u=paper_main_loss_joint_code n A b radius).
assert (HY : exists u, Y u) by (exists(paper_main_loss_joint_code n A0 b0 radius); exists A0,b0; auto).
assert (HN : forall u, Y u -> paper_main_gordon_dot (S(paper_main_symmetric_dimension n)) u u<=1).
{ intros u [A [b [HAb ->]]]; destruct(HT A b HAb) as [HS HB].
  rewrite (paper_main_loss_joint_code_norm n A b radius HS).
  apply (Rmult_le_reg_r (radius^2)); [nra|].
  replace ((2*paper_main_frobenius A^2+b^2)/radius^2*radius^2) with
    (2*paper_main_frobenius A^2+b^2) by (field; lra).
  nra. }
assert (Hdel : 0<delta/radius) by (apply Rdiv_lt_0_compat; assumption).
destruct(paper_main_loss_ball_net (S(paper_main_symmetric_dimension n)) Y (delta/radius) Hdel HY HN)
  as [s [v [Hs [[Hin Hcover] Hcard]]]].
set (pick := fun j => epsilon (inhabits (A0,b0))
  (fun p => T (fst p) (snd p) /\ v j=paper_main_loss_joint_code n (fst p) (snd p) radius)).
assert (HP : forall j, (j<s)%coq_nat -> T (fst(pick j)) (snd(pick j)) /\
  v j=paper_main_loss_joint_code n (fst(pick j)) (snd(pick j)) radius).
{ intros j Hj; unfold pick; apply epsilon_spec.
  destruct(Hin j ltac:(apply in_seq; lia)) as [A [b [HTab HE]]].
  exists(A,b); split; assumption. }
exists s,(fun j => fst(pick j)),(fun j => snd(pick j)); split; [exact Hs|].
split; [intros j Hj; exact(proj1(HP j Hj))|]; split; [|exact Hcard].
intros B c HBC; destruct(Hcover (paper_main_loss_joint_code n B c radius)
  ltac:(exists B,c; auto)) as [j [Hj Hdist]].
apply in_seq in Hj; assert (Hjs : (j<s)%coq_nat) by lia.
exists j; split; [exact Hjs|].
rewrite (proj2(HP j Hjs)) in Hdist.
rewrite (paper_main_loss_joint_code_distance n B (fst(pick j)) c (snd(pick j)) radius
  (proj1(HT B c HBC)) (proj1(HT _ _ (proj1(HP j Hjs))))) in Hdist.
pose proof(Rmult_le_compat_r (radius^2) _ _ (pow2_ge_0 radius) Hdist) as HB.
replace ((2*paper_main_frobenius (B-fst(pick j))%R^2+(c-snd(pick j))^2)/radius^2*radius^2)
  with (2*paper_main_frobenius (B-fst(pick j))%R^2+(c-snd(pick j))^2) in HB by (field; lra).
replace ((delta/radius)^2*radius^2) with (delta^2) in HB by (field; lra).
exact HB.
Qed.

Corollary paper_main_loss_joint_distance n (A B : 'M[R]_(S n)) b c delta : 0<=delta ->
  2*paper_main_frobenius (A-B)%R^2+(b-c)^2<=delta^2 ->
  paper_main_frobenius (A-B)%R<=delta /\ Rabs(b-c)<=delta.
Proof.
intros Hd HH; assert (HN : 0<=paper_main_frobenius (A-B)%R) by (apply/RleP; apply pmh_frobenius_ge0).
pose proof (pow2_ge_0 (b-c)).
pose proof (pow2_ge_0 (paper_main_frobenius (A-B)%R)).
split; [nra|apply Rabs_le; nra].
Qed.
