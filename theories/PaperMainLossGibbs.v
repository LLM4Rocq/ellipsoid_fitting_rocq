(* Finite Gibbs row replacement for bounded losses, uniformly in translations. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GibbsDefinitions GibbsWeights
  GibbsMomentBounds GibbsDerivatives PaperMainTranslatedLoss.
Open Scope R_scope.

Definition paper_main_gibbs_row_factor beta f I ell :=
  gibbs_average (-beta) f I (fun s => exp(-beta*ell s)).

Lemma paper_main_gibbs_row_bounds beta f I ell :
  0 <= beta -> I <> nil -> (forall s, In s I -> 0 <= ell s <= 1) ->
  exp(-beta) <= paper_main_gibbs_row_factor beta f I ell <= 1.
Proof.
intros Hb HI Hell; unfold paper_main_gibbs_row_factor; split.
- rewrite <- (gibbs_average_const (-beta) f I (exp(-beta)) HI).
  apply gibbs_average_monotone; [exact HI|].
  intros s Hs; apply exp_monotone; pose proof (Hell s Hs); nra.
- rewrite <- (gibbs_average_const (-beta) f I 1 HI).
  apply gibbs_average_monotone; [exact HI|].
  intros s Hs; rewrite <- exp_0; apply exp_monotone; pose proof (Hell s Hs); nra.
Qed.

Lemma paper_main_gibbs_row_partition beta f I ell :
  I <> nil -> partition (-beta) (fun s => f s+ell s) I =
    partition (-beta) f I * paper_main_gibbs_row_factor beta f I ell.
Proof.
intro HI; unfold paper_main_gibbs_row_factor; rewrite gibbs_average_ratio.
assert (HE : finite_sum (fun s => exp(-beta*f s)*exp(-beta*ell s)) I =
  partition (-beta) (fun s => f s+ell s) I).
{ unfold partition; apply gibbs_sum_ext; intros s Hs.
  rewrite <- exp_plus; f_equal; ring. }
rewrite HE.
pose proof (partition_positive (-beta) f I HI) as HP.
field; lra.
Qed.

Lemma paper_main_gibbs_row_increment beta f I ell :
  0 < beta -> I <> nil -> (forall s, In s I -> 0 <= ell s <= 1) ->
  soft_min beta (fun s => f s+ell s) I - soft_min beta f I =
    -Rpower.ln(paper_main_gibbs_row_factor beta f I ell)/beta.
Proof.
intros Hb HI Hell.
pose proof (paper_main_gibbs_row_bounds beta f I ell (Rlt_le _ _ Hb) HI Hell) as [HL HU].
pose proof (exp_pos(-beta)) as HE.
pose proof (partition_positive (-beta) f I HI) as HP.
rewrite !soft_min_signed_identity; try lra.
change (Rpower.ln(partition (-beta) (fun s => f s+ell s) I)/(-beta) -
  Rpower.ln(partition (-beta) f I)/(-beta) =
  -Rpower.ln(paper_main_gibbs_row_factor beta f I ell)/beta).
rewrite (paper_main_gibbs_row_partition beta f I ell HI).
assert (HF : 0 < paper_main_gibbs_row_factor beta f I ell) by lra.
rewrite (ln_mult (partition (-beta) f I) (paper_main_gibbs_row_factor beta f I ell) HP HF); field; lra.
Qed.

Theorem paper_main_gibbs_row_increment_bounds beta f I ell :
  0 < beta -> I <> nil -> (forall s, In s I -> 0 <= ell s <= 1) ->
  0 <= soft_min beta (fun s => f s+ell s) I-soft_min beta f I <= 1.
Proof.
intros Hb HI Hell.
rewrite (paper_main_gibbs_row_increment beta f I ell Hb HI Hell).
pose proof (paper_main_gibbs_row_bounds beta f I ell (Rlt_le _ _ Hb) HI Hell) as [HL HU].
pose proof (exp_pos(-beta)) as HE.
pose proof (ln_monotone _ _ HE HL) as HlogL.
assert (HF : 0 < paper_main_gibbs_row_factor beta f I ell) by lra.
pose proof (ln_monotone (paper_main_gibbs_row_factor beta f I ell) 1 HF HU) as HlogU.
rewrite ln_exp in HlogL; rewrite ln_1 in HlogU.
assert (HC : (-Rpower.ln(paper_main_gibbs_row_factor beta f I ell)/beta)*beta =
  -Rpower.ln(paper_main_gibbs_row_factor beta f I ell)) by (field; lra).
split; nra.
Qed.

Corollary paper_main_gibbs_row_change beta f I ell ell' :
  0 < beta -> I <> nil ->
  (forall s, In s I -> 0 <= ell s <= 1) ->
  (forall s, In s I -> 0 <= ell' s <= 1) ->
  Rabs(soft_min beta (fun s => f s+ell s) I-
    soft_min beta (fun s => f s+ell' s) I) <= 1.
Proof.
intros Hb HI H1 H2.
pose proof (paper_main_gibbs_row_increment_bounds beta f I ell Hb HI H1).
pose proof (paper_main_gibbs_row_increment_bounds beta f I ell' Hb HI H2).
apply Rabs_le; lra.
Qed.
