(* Joint matrix/scalar finite nets transfer a positive empirical loss gap. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGaussianFeatureCoordinates PaperMainGordonEntropy PaperMainLossEmpirical PaperMainLossJointNet.
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

Theorem paper_main_loss_joint_net_risk n N (T : 'M[R]_(S n) -> R -> Prop) radius delta F L :
  (0<N)%coq_nat -> 0<radius -> 0<delta -> 0<=L ->
  (exists A b, T A b) ->
  (forall A b, T A b -> paper_main_symmetric A /\ 2*paper_main_frobenius A^2+b^2<=radius^2) ->
  (forall A B b c, T A b -> T B c ->
    finite_sum (fun i => (F i A-F i B)^2) (List.seq 0 N)<=INR N*(L*paper_main_frobenius (A-B)%R)^2) ->
  exists s (A : nat -> 'M[R]_(S n)) (b : nat -> R), (0<s)%coq_nat /\
    (forall j, (j<s)%coq_nat -> T(A j)(b j)) /\
    Rpower.ln(INR s)<=paper_main_gordon_entropy_constant (delta/radius)*INR(S(S(paper_main_symmetric_dimension n))) /\
    (forall B c, T B c -> exists j, (j<s)%coq_nat /\
      Rabs(paper_main_loss_joint_risk n N F B c-paper_main_loss_joint_risk n N F (A j)(b j))<=4*(L+1)*delta).
Proof.
intros HN Hr Hd HL HT HB HF.
destruct(paper_main_loss_joint_net n T radius delta Hr Hd HT HB) as [s [A [b [Hs [Hin [Hcover Hcard]]]]]].
exists s,A,b; split; [exact Hs|]; split; [exact Hin|]; split; [exact Hcard|].
intros B c HBC; destruct(Hcover B c HBC) as [j [Hj Hdist]].
exists j; split; [exact Hj|].
destruct(paper_main_loss_joint_distance n B (A j) c (b j) delta ltac:(lra) Hdist) as [HM Hscl].
eapply Rle_trans.
- apply paper_main_loss_joint_risk_lipschitz; [exact HN|exact HL|apply (HF B (A j) c (b j)); [exact HBC|apply Hin; exact Hj]].
- nra.
Qed.

Theorem paper_main_loss_joint_net_gap n N (T : 'M[R]_(S n) -> R -> Prop) F s A b e err :
  (forall B c, T B c -> exists j, (j<s)%coq_nat /\
    Rabs(paper_main_loss_joint_risk n N F B c-paper_main_loss_joint_risk n N F (A j)(b j))<=err) ->
  (forall j, (j<s)%coq_nat -> e<=paper_main_loss_joint_risk n N F (A j)(b j)) ->
  forall B c, T B c -> e-err<=paper_main_loss_joint_risk n N F B c.
Proof.
intros HC HG B c HBC; destruct(HC B c HBC) as [j [Hj Hdist]].
pose proof(HG j Hj).
pose proof(Rle_abs(paper_main_loss_joint_risk n N F (A j)(b j)-paper_main_loss_joint_risk n N F B c)) as HH.
rewrite Rabs_minus_sym in HH; lra.
Qed.
