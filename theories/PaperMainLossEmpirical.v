(* Bounded empirical loss and its deterministic Euclidean continuity estimate. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  PaperMainGordonLipschitz PaperMainTranslatedLoss.
Open Scope R_scope.

Definition paper_main_loss_empirical N u :=
  /INR N*finite_sum (fun i => paper_main_loss(u i)) (List.seq 0 N).

Lemma paper_main_loss_empirical_bounds N u : 0<=paper_main_loss_empirical N u<=1.
Proof.
destruct N as [|N]; [unfold paper_main_loss_empirical; simpl; rewrite Rinv_0; lra|].
assert (HN : 0<INR(S N)) by (apply lt_0_INR; lia).
assert (HL : 0<=finite_sum (fun i => paper_main_loss(u i)) (List.seq 0 (S N))).
{ apply finite_sum_nonneg; intros; apply paper_main_loss_bounds. }
assert (HU : finite_sum (fun i => paper_main_loss(u i)) (List.seq 0 (S N))<=INR(S N)).
{ replace (INR(S N)) with (finite_sum (fun _ => 1) (List.seq 0 (S N)))
    by (rewrite finite_sum_const,List.length_seq; ring).
  apply finite_sum_le; intros; apply paper_main_loss_bounds. }
unfold paper_main_loss_empirical.
pose proof(Rinv_0_lt_compat _ HN).
assert (HE : /INR(S N)*INR(S N)=1) by (field; lra).
split; [apply Rmult_le_pos; lra|].
pose proof(Rmult_le_compat_l (/INR(S N)) _ _ ltac:(lra) HU); lra.
Qed.

Lemma paper_main_loss_empirical_zero N u :
  (forall i, (i<N)%nat -> u i=0) -> paper_main_loss_empirical N u=0.
Proof.
intro HU; unfold paper_main_loss_empirical.
assert (HE : finite_sum (fun i => paper_main_loss(u i)) (List.seq 0 N)=0).
{ rewrite <-(finite_sum_zero (List.seq 0 N)); apply finite_sum_ext; intros i Hi.
  apply in_seq in Hi; rewrite (HU i ltac:(lia)); apply paper_main_loss_zero; reflexivity. }
rewrite HE; ring.
Qed.

Lemma paper_main_loss_sum_absolute_bound N w L D : 0<=L -> 0<=D ->
  finite_sum (fun i => w i^2) (List.seq 0 N)<=INR N*(L*D)^2 ->
  finite_sum (fun i => Rabs(w i)) (List.seq 0 N)<=INR N*L*D.
Proof.
intros HL HD HB.
pose proof(paper_main_gordon_sum_cauchy (fun _ => 1) (fun i => Rabs(w i)) (List.seq 0 N)) as HC.
cbv beta in HC.
assert (Hleft : finite_sum (fun i => 1*Rabs(w i)) (List.seq 0 N)=
  finite_sum (fun i => Rabs(w i)) (List.seq 0 N)).
{ apply finite_sum_ext; intros; ring. }
assert (Hone : finite_sum (fun _ => 1^2) (List.seq 0 N)=INR N).
{ transitivity (finite_sum (fun _ => 1) (List.seq 0 N));
    [apply finite_sum_ext; intros; ring|rewrite finite_sum_const,List.length_seq; ring]. }
assert (Hright : finite_sum (fun i => Rabs(w i)^2) (List.seq 0 N)=finite_sum (fun i => w i^2) (List.seq 0 N)).
{ apply finite_sum_ext; intros i Hi.
  destruct(Rcase_abs(w i)) as [Hneg|Hpos];
    [rewrite Rabs_left by exact Hneg|rewrite Rabs_pos_eq by lra]; ring. }
rewrite Hleft,Hone,Hright in HC.
pose proof(pos_INR N) as HN.
pose proof(Rmult_le_compat_l (INR N) _ _ HN HB) as HH.
assert (HT : 0<=INR N*L*D) by (repeat apply Rmult_le_pos; assumption).
nra.
Qed.

Theorem paper_main_loss_empirical_lipschitz N u v L D : (0<N)%nat -> 0<=L -> 0<=D ->
  finite_sum (fun i => (u i-v i)^2) (List.seq 0 N)<=INR N*(L*D)^2 ->
  Rabs(paper_main_loss_empirical N u-paper_main_loss_empirical N v)<=4*L*D.
Proof.
intros HN HL HD HB; pose proof(paper_main_loss_sum_absolute_bound N (fun i => u i-v i) L D HL HD HB) as HH.
assert (Hpos : 0<INR N) by (apply lt_0_INR; exact HN).
assert (HE : finite_sum (fun i => Rabs(paper_main_loss(u i)-paper_main_loss(v i))) (List.seq 0 N)<=
  4*finite_sum (fun i => Rabs(u i-v i)) (List.seq 0 N)).
{ rewrite <-finite_sum_scale; apply finite_sum_le; intros; apply paper_main_loss_lipschitz. }
unfold paper_main_loss_empirical.
replace (/INR N*finite_sum (fun i => paper_main_loss(u i)) (List.seq 0 N)-
  /INR N*finite_sum (fun i => paper_main_loss(v i)) (List.seq 0 N)) with
  (/INR N*(finite_sum (fun i => paper_main_loss(u i)) (List.seq 0 N)-
  finite_sum (fun i => paper_main_loss(v i)) (List.seq 0 N))) by ring.
rewrite Rabs_mult, (Rabs_pos_eq (/INR N) ltac:(apply Rlt_le,Rinv_0_lt_compat; exact Hpos)).
rewrite <-finite_sum_minus.
pose proof(finite_sum_abs_le (fun i => paper_main_loss(u i)-paper_main_loss(v i)) (List.seq 0 N)) as Habs.
assert (HB2 : Rabs(finite_sum (fun i => paper_main_loss(u i)-paper_main_loss(v i)) (List.seq 0 N))<=4*(INR N*L*D)) by lra.
pose proof(Rmult_le_compat_l (/INR N) _ _ ltac:(apply Rlt_le,Rinv_0_lt_compat; exact Hpos) HB2) as HH2.
replace (/INR N*(4*(INR N*L*D))) with (4*L*D) in HH2 by (field; lra); exact HH2.
Qed.
