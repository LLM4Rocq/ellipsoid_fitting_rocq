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
