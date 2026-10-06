(* Lipschitz bounds for the joint empirical risk
     paper_main_loss_joint_risk n N F A b
       = (1/N) sum_(i < N) loss(F_i(A) - b),
   loss(t) = 1 - exp(-t^2) (paper_main_loss), in the matrix A and the
   scalar b.
   - paper_main_loss_shift_lipschitz: changing the shift b to c changes the
     empirical loss by at most 4 |b - c|.
   - paper_main_loss_joint_risk_lipschitz: if
     sum_i (F_i(A) - F_i(B))^2 <= N (L |A - B|_F)^2, the risks at (A, b)
     and (B, c) differ by at most 4 L |A - B|_F + 4 |b - c|. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra PaperMainDefinitions Geometry.Homogeneous
  Geometry.HeadFrobenius Gaussian.Symmetric.Coordinates Gordon.Entropy
  Loss.Empirical Loss.JointNet.
Open Scope R_scope.

Definition paper_main_loss_joint_risk n N (F : nat -> 'M[R]_(S n) -> R) A b :=
  paper_main_loss_empirical N (fun i => F i A-b).

Lemma paper_main_loss_shift_lipschitz N u b c : (0<N)%coq_nat ->
  Rabs(paper_main_loss_empirical N (fun i => u i-b)-
    paper_main_loss_empirical N (fun i => u i-c))<=4*Rabs(b-c).
Proof.
intro HN; replace (4*Rabs(b-c)) with (4*1*Rabs(b-c)) by ring.
apply paper_main_loss_empirical_lipschitz; [exact HN|lra|apply Rabs_pos|].
assert (HE : finite_sum (fun i => (u i-b-(u i-c))^2) (List.seq 0 N)=INR N*(b-c)^2).
{ transitivity(finite_sum (fun _ => (b-c)^2) (List.seq 0 N));
    [apply finite_sum_ext; intros; ring|rewrite finite_sum_const List.length_seq; ring]. }
rewrite HE.
assert (HA : Rabs(b-c)^2=(b-c)^2).
{ pose proof (Rsqr_abs (b-c)) as HX; unfold Rsqr in HX; nra. }
rewrite Rmult_1_l HA; lra.
Qed.

Theorem paper_main_loss_joint_risk_lipschitz n N F (A B : 'M[R]_(S n)) b c L :
  (0<N)%coq_nat -> 0<=L ->
  finite_sum (fun i => (F i A-F i B)^2) (List.seq 0 N)<=
    INR N*(L*paper_main_frobenius (A-B)%R)^2 ->
  Rabs(paper_main_loss_joint_risk n N F A b-paper_main_loss_joint_risk n N F B c)<=
    4*L*paper_main_frobenius (A-B)%R+4*Rabs(b-c).
Proof.
intros HN HL HF.
assert (HAB : Rabs(paper_main_loss_joint_risk n N F A b-paper_main_loss_joint_risk n N F B b)<=
  4*L*paper_main_frobenius (A-B)%R).
{ apply paper_main_loss_empirical_lipschitz; [exact HN|exact HL|apply/RleP; apply pmh_frobenius_ge0|].
  assert (HE : finite_sum (fun i => (F i A-b-(F i B-b))^2) (List.seq 0 N)=
    finite_sum (fun i => (F i A-F i B)^2) (List.seq 0 N)) by (apply finite_sum_ext; intros; f_equal; ring).
  rewrite HE; exact HF. }
pose proof(paper_main_loss_shift_lipschitz N (fun i => F i B) b c HN) as Hbc.
change (Rabs(paper_main_loss_joint_risk n N F B b-paper_main_loss_joint_risk n N F B c)<=4*Rabs(b-c)) in Hbc.
replace (paper_main_loss_joint_risk n N F A b-paper_main_loss_joint_risk n N F B c) with
  ((paper_main_loss_joint_risk n N F A b-paper_main_loss_joint_risk n N F B b)+
   (paper_main_loss_joint_risk n N F B b-paper_main_loss_joint_risk n N F B c)) by ring.
eapply Rle_trans; [apply Rabs_triang|lra].
Qed.
