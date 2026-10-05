(* Finite entropy nets for arbitrary subsets of a Euclidean ball. *)
From Stdlib Require Import Reals List Arith Lia Lra Psatz Epsilon.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  PaperMainGordonProcessCovariance PaperMainGordonNets PaperMainGordonEntropy.
Open Scope R_scope.

Definition paper_main_loss_ball_lift d (u : nat -> R) (i : nat) :=
  if lt_dec i d then u i else sqrt(1-paper_main_gordon_dot d u u).

Lemma paper_main_loss_ball_lift_inside d u i : (i<d)%nat ->
  paper_main_loss_ball_lift d u i=u i.
Proof. intro Hi; unfold paper_main_loss_ball_lift; destruct(lt_dec i d); [reflexivity|lia]. Qed.
Lemma paper_main_loss_ball_lift_last d u :
  paper_main_loss_ball_lift d u d=sqrt(1-paper_main_gordon_dot d u u).
Proof. unfold paper_main_loss_ball_lift; destruct(lt_dec d d); [lia|reflexivity]. Qed.

Lemma paper_main_loss_ball_lift_unit d u : paper_main_gordon_dot d u u<=1 ->
  paper_main_gordon_dot (S d) (paper_main_loss_ball_lift d u) (paper_main_loss_ball_lift d u)=1.
Proof.
intro HU; unfold paper_main_gordon_dot at 1; rewrite finite_sum_seq_S, paper_main_loss_ball_lift_last.
assert (HE : finite_sum (fun i => paper_main_loss_ball_lift d u i*paper_main_loss_ball_lift d u i)
  (List.seq 0 d)=paper_main_gordon_dot d u u).
{ unfold paper_main_gordon_dot; apply finite_sum_ext; intros i Hi.
  apply in_seq in Hi; rewrite paper_main_loss_ball_lift_inside by lia; reflexivity. }
rewrite HE.
pose proof(pow2_sqrt (1-paper_main_gordon_dot d u u) ltac:(lra)); nra.
Qed.

Lemma paper_main_loss_ball_lift_distance d u v :
  paper_main_gordon_dot d (fun i => u i-v i) (fun i => u i-v i)<=
  paper_main_gordon_dot (S d)
    (fun i => paper_main_loss_ball_lift d u i-paper_main_loss_ball_lift d v i)
    (fun i => paper_main_loss_ball_lift d u i-paper_main_loss_ball_lift d v i).
Proof.
unfold paper_main_gordon_dot at 2; rewrite finite_sum_seq_S.
assert (HE : finite_sum (fun i =>
  (paper_main_loss_ball_lift d u i-paper_main_loss_ball_lift d v i)*
  (paper_main_loss_ball_lift d u i-paper_main_loss_ball_lift d v i)) (List.seq 0 d)=
  paper_main_gordon_dot d (fun i => u i-v i) (fun i => u i-v i)).
{ unfold paper_main_gordon_dot; apply finite_sum_ext; intros i Hi.
  apply in_seq in Hi; rewrite !paper_main_loss_ball_lift_inside by lia; reflexivity. }
rewrite HE; pose proof(pow2_ge_0(paper_main_loss_ball_lift d u d-paper_main_loss_ball_lift d v d)); nra.
Qed.

Theorem paper_main_loss_ball_net d (T : (nat -> R) -> Prop) eps : 0<eps ->
  (exists u, T u) -> (forall u, T u -> paper_main_gordon_dot d u u<=1) ->
  exists s v, (0<s)%nat /\ paper_main_gordon_finite_net d T v (List.seq 0 s) eps /\
    ln(INR s)<=paper_main_gordon_entropy_constant eps*INR(S d).
Proof.
intros He [u0 Hu0] HT.
set (A := fun w : nat -> R => exists u, T u /\ w=paper_main_loss_ball_lift d u).
assert (HA : exists w, A w) by (exists(paper_main_loss_ball_lift d u0); exists u0; auto).
assert (HU : forall w, A w -> paper_main_gordon_dot (S d) w w=1).
{ intros w [u [Hu ->]]; apply paper_main_loss_ball_lift_unit; apply HT; exact Hu. }
destruct(paper_main_gordon_entropy_net (S d) A eps He HA HU) as [s [v [Hs [[Hin Hcover] Hcard]]]].
set (pick := fun j => epsilon (inhabits u0) (fun u => T u /\ v j=paper_main_loss_ball_lift d u)).
assert (HP : forall j, In j (List.seq 0 s) -> T(pick j) /\ v j=paper_main_loss_ball_lift d (pick j)).
{ intros j Hj; unfold pick; apply epsilon_spec; exact(Hin j Hj). }
exists s,pick; split; [exact Hs|]; split; [|exact Hcard]; split.
- intros j Hj; exact(proj1(HP j Hj)).
- intros u Hu; destruct(Hcover (paper_main_loss_ball_lift d u) ltac:(exists u; auto)) as [j [Hj HD]].
  exists j; split; [exact Hj|].
  rewrite (proj2(HP j Hj)) in HD.
  eapply Rle_trans; [apply paper_main_loss_ball_lift_distance|exact HD].
Qed.
