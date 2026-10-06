(* Joint continuity of the finite Gibbs functions used in Gaussian comparison. *)
From Stdlib Require Import Reals List Lra.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GibbsDefinitions
  GibbsWeights GibbsDerivatives GaussianCoordinateDefinitions GaussianCoordinateBasics
  GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity GaussianFiniteSums
  PaperMainGordonCovariance PaperMainGordonCalculus.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_joint_comp d (F : list R -> R) (g : R -> R) :
  finite_joint_continuous d F ->
  (forall xs, List.length xs = d -> {for F xs, continuous g}) ->
  finite_joint_continuous d (fun xs => g (F xs)).
Proof.
intros HF Hg z eps.
destruct (proj1 (continuous_Reals g (F (coordinates_to_list d z)))
  (Hg _ (coordinates_to_list_length d z)) eps (cond_pos eps)) as [r [Hr Hrg]].
destruct (HF z (mkposreal r Hr)) as [delta Hd].
exists delta; intros w Hw; apply Hrg; exact (Hd w Hw).
Qed.

Lemma paper_main_gordon_joint_exp d F :
  finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => exp (F xs)).
Proof.
intros HF.
apply (paper_main_gordon_joint_comp d F exp); [exact HF|].
intros xs Hxs; apply continuous_Rexp.
Qed.

Lemma paper_main_gordon_joint_inv d F :
  finite_joint_continuous d F ->
  (forall xs, List.length xs = d -> F xs <> 0) ->
  finite_joint_continuous d (fun xs => / F xs).
Proof.
intros HF Hne.
apply (paper_main_gordon_joint_comp d F Rinv); [exact HF|].
intros xs Hxs; apply continuous_Rinv; apply Hne; exact Hxs.
Qed.

Lemma paper_main_gordon_joint_ln d F :
  finite_joint_continuous d F ->
  (forall xs, List.length xs = d -> 0 < F xs) ->
  finite_joint_continuous d (fun xs => Rpower.ln (F xs)).
Proof.
intros HF Hpos.
apply (paper_main_gordon_joint_comp d F Rpower.ln); [exact HF|].
intros xs Hxs; apply continuous_Rln; apply Hpos; exact Hxs.
Qed.

Lemma paper_main_gordon_partition_continuous d c (F : list R -> nat -> R) I :
  (forall i, In i I -> finite_joint_continuous d (fun xs => F xs i)) ->
  finite_joint_continuous d (fun xs => partition c (F xs) I).
Proof.
intros HF.
unfold partition; apply finite_joint_continuous_sum; intros i Hi.
apply paper_main_gordon_joint_exp; apply finite_joint_continuous_scale.
apply HF; exact Hi.
Qed.

Lemma paper_main_gordon_weight_continuous d c (F : list R -> nat -> R) I i :
  I <> [] -> In i I ->
  (forall j, In j I -> finite_joint_continuous d (fun xs => F xs j)) ->
  finite_joint_continuous d (fun xs => gibbs_weight c (F xs) I i).
Proof.
intros HI Hi HF.
unfold gibbs_weight, Rdiv; apply finite_joint_continuous_mult.
- apply paper_main_gordon_joint_exp; apply finite_joint_continuous_scale; apply HF; exact Hi.
- apply paper_main_gordon_joint_inv.
  + apply paper_main_gordon_partition_continuous; exact HF.
  + intros xs Hxs; pose proof (partition_positive c (F xs) I HI); lra.
Qed.

Lemma paper_main_gordon_average_continuous d c (F U : list R -> nat -> R) I :
  I <> [] ->
  (forall i, In i I -> finite_joint_continuous d (fun xs => F xs i)) ->
  (forall i, In i I -> finite_joint_continuous d (fun xs => U xs i)) ->
  finite_joint_continuous d (fun xs => gibbs_average c (F xs) I (U xs)).
Proof.
intros HI HF HU.
unfold gibbs_average; apply finite_joint_continuous_sum; intros i Hi.
apply finite_joint_continuous_mult.
- apply paper_main_gordon_weight_continuous; assumption.
- apply HU; exact Hi.
Qed.

Lemma paper_main_gordon_covariance_continuous d c
    (F U V : list R -> nat -> R) I :
  I <> [] ->
  (forall i, In i I -> finite_joint_continuous d (fun xs => F xs i)) ->
  (forall i, In i I -> finite_joint_continuous d (fun xs => U xs i)) ->
  (forall i, In i I -> finite_joint_continuous d (fun xs => V xs i)) ->
  finite_joint_continuous d (fun xs => gibbs_covariance c (F xs) I (U xs) (V xs)).
Proof.
intros HI HF HU HV.
unfold gibbs_covariance; apply finite_joint_continuous_minus.
- apply paper_main_gordon_average_continuous; try assumption.
  intros i Hi; apply finite_joint_continuous_mult; [apply HU|apply HV]; exact Hi.
- apply finite_joint_continuous_mult; apply paper_main_gordon_average_continuous; assumption.
Qed.

Lemma paper_main_gordon_soft_max_continuous d c (F : list R -> nat -> R) I :
  I <> [] ->
  (forall i, In i I -> finite_joint_continuous d (fun xs => F xs i)) ->
  finite_joint_continuous d (fun xs => soft_max c (F xs) I).
Proof.
intros HI HF.
unfold soft_max, Rdiv; apply finite_joint_continuous_mult.
- apply paper_main_gordon_joint_ln.
  + apply paper_main_gordon_partition_continuous; exact HF.
  + intros xs Hxs; apply partition_positive; exact HI.
- apply finite_joint_continuous_constant.
Qed.

Lemma paper_main_gordon_soft_minimax_continuous d beta gamma
    (F : list R -> nat -> nat -> R) Y S :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> finite_joint_continuous d (fun xs => F xs y s)) ->
  finite_joint_continuous d (fun xs => soft_minimax beta gamma (F xs) Y S).
Proof.
intros HY HS HF.
unfold soft_minimax, soft_min.
apply (paper_main_gordon_joint_comp d _ Ropp).
- apply paper_main_gordon_soft_max_continuous; [exact HY|]; intros y Hy.
  apply (paper_main_gordon_joint_comp d _ Ropp).
  + apply paper_main_gordon_soft_max_continuous; [exact HS|]; intros s Hs; apply HF; assumption.
  + intros xs Hxs; apply continuous_opp; apply continuous_id.
- intros xs Hxs; apply continuous_opp; apply continuous_id.
Qed.

Lemma paper_main_gordon_mean_continuous d beta gamma
    (F U : list R -> nat -> nat -> R) Y S :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> finite_joint_continuous d (fun xs => F xs y s)) ->
  (forall y s, In y Y -> In s S -> finite_joint_continuous d (fun xs => U xs y s)) ->
  finite_joint_continuous d (fun xs => paper_main_gordon_mean beta gamma (F xs) (U xs) Y S).
Proof.
intros HY HS HF HU.
unfold paper_main_gordon_mean, paper_main_gordon_outer, paper_main_gordon_inner.
apply paper_main_gordon_average_continuous; [exact HY| |].
- intros y Hy; apply paper_main_gordon_soft_max_continuous; [exact HS|].
  intros s Hs; apply HF; assumption.
- intros y Hy; apply paper_main_gordon_average_continuous; [exact HS| |].
  + intros s Hs; apply HF; assumption.
  + intros s Hs; apply HU; assumption.
Qed.

Lemma paper_main_gordon_hessian_continuous d beta gamma
    (F U V : list R -> nat -> nat -> R) Y S :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> finite_joint_continuous d (fun xs => F xs y s)) ->
  (forall y s, In y Y -> In s S -> finite_joint_continuous d (fun xs => U xs y s)) ->
  (forall y s, In y Y -> In s S -> finite_joint_continuous d (fun xs => V xs y s)) ->
  finite_joint_continuous d (fun xs => paper_main_gordon_hessian beta gamma (F xs) (U xs) (V xs) Y S).
Proof.
intros HY HS HF HU HV.
unfold paper_main_gordon_hessian, paper_main_gordon_outer, paper_main_gordon_inner.
apply finite_joint_continuous_minus; apply finite_joint_continuous_scale.
- apply paper_main_gordon_average_continuous; [exact HY| |].
  + intros y Hy; apply paper_main_gordon_soft_max_continuous; [exact HS|].
    intros s Hs; apply HF; assumption.
  + intros y Hy; apply paper_main_gordon_covariance_continuous; [exact HS| | |].
    * intros s Hs; apply HF; assumption.
    * intros s Hs; apply HU; assumption.
    * intros s Hs; apply HV; assumption.
- apply paper_main_gordon_covariance_continuous; [exact HY| | |].
  + intros y Hy; apply paper_main_gordon_soft_max_continuous; [exact HS|].
    intros s Hs; apply HF; assumption.
  + intros y Hy; apply paper_main_gordon_average_continuous; [exact HS| |].
    * intros s Hs; apply HF; assumption.
    * intros s Hs; apply HU; assumption.
  + intros y Hy; apply paper_main_gordon_average_continuous; [exact HS| |].
    * intros s Hs; apply HF; assumption.
    * intros s Hs; apply HV; assumption.
Qed.
