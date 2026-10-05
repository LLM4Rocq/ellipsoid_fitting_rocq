(* Dimension-free score perturbation bounds for finite soft extrema. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums
  GaussianCoordinateDefinitions GaussianProductDefinitions GaussianProbabilityProductDefinitions
  PaperMainGordonLipschitz PaperMainGaussianLipschitzClip
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianLipschitzConcentration
  PaperMainGaussianGordonTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_soft_partition_positive gamma f I :
  I <> [] -> 0 < finite_sum (fun i => exp (gamma * f i)) I.
Proof.
intros HI; destruct I as [|i I]; [contradiction|].
simpl.
pose proof (finite_sum_nonnegative (fun j => exp (gamma * f j)) I
  ltac:(intros; left; apply exp_pos)).
pose proof (exp_pos (gamma * f i)); lra.
Qed.

Lemma paper_main_soft_max_monotone gamma f g I :
  0 < gamma -> I <> [] -> (forall i, In i I -> f i <= g i) ->
  soft_max gamma f I <= soft_max gamma g I.
Proof.
intros Hg HI Hfg; unfold soft_max, Rdiv.
apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hg|].
apply ln_monotone; [apply paper_main_soft_partition_positive; exact HI|].
apply finite_sum_le; intros i Hi; apply exp_monotone.
apply Rmult_le_compat_l; [lra|apply Hfg; exact Hi].
Qed.

Lemma paper_main_soft_max_shift gamma f I c :
  gamma <> 0 -> I <> [] ->
  soft_max gamma (fun i => f i + c) I = soft_max gamma f I + c.
Proof.
intros Hg HI; unfold soft_max.
assert (E : finite_sum (fun i => exp (gamma * (f i + c))) I =
  exp (gamma*c) * finite_sum (fun i => exp (gamma*f i)) I).
{ rewrite <- finite_sum_scale; apply finite_sum_ext; intros i Hi.
  replace (gamma * (f i+c)) with (gamma*c+gamma*f i) by ring.
  apply exp_plus. }
rewrite E ln_mult; try apply exp_pos; try (apply paper_main_soft_partition_positive; exact HI).
rewrite ln_exp; field; exact Hg.
Qed.

Lemma paper_main_soft_max_lipschitz gamma f g I b :
  0 < gamma -> I <> [] -> (forall i, In i I -> Rabs (f i-g i) <= b) ->
  Rabs (soft_max gamma f I-soft_max gamma g I) <= b.
Proof.
intros Hg HI Hfg.
assert (Hf : forall i, In i I -> f i <= g i+b).
{ intros i Hi; pose proof (Hfg i Hi); pose proof (Rle_abs (f i-g i)); lra. }
assert (Hg' : forall i, In i I -> g i <= f i+b).
{ intros i Hi; pose proof (Hfg i Hi); pose proof (Rle_abs (g i-f i)) as Hrev.
  rewrite Rabs_minus_sym in Hrev; lra. }
pose proof (paper_main_soft_max_monotone gamma f (fun i => g i+b) I Hg HI Hf) as H1.
pose proof (paper_main_soft_max_monotone gamma g (fun i => f i+b) I Hg HI Hg') as H2.
rewrite (paper_main_soft_max_shift gamma g I b ltac:(lra) HI) in H1.
rewrite (paper_main_soft_max_shift gamma f I b ltac:(lra) HI) in H2.
apply Rabs_le; split; lra.
Qed.

Lemma paper_main_soft_min_lipschitz beta f g I b :
  0 < beta -> I <> [] -> (forall i, In i I -> Rabs (f i-g i) <= b) ->
  Rabs (soft_min beta f I-soft_min beta g I) <= b.
Proof.
intros Hb HI Hfg; unfold soft_min.
replace (-soft_max beta (fun i => -f i) I - -soft_max beta (fun i => -g i) I)
 with (-(soft_max beta (fun i => -f i) I-soft_max beta (fun i => -g i) I)) by ring.
rewrite Rabs_Ropp; apply paper_main_soft_max_lipschitz; try assumption.
intros i Hi; replace (-f i - -g i) with (-(f i-g i)) by ring.
rewrite Rabs_Ropp; apply Hfg; exact Hi.
Qed.

Theorem paper_main_soft_minimax_lipschitz beta gamma F G Y S b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> Rabs (F y s-G y s) <= b) ->
  Rabs (soft_minimax beta gamma F Y S-soft_minimax beta gamma G Y S) <= b.
Proof.
intros Hb Hg HY HS HFG; unfold soft_minimax.
apply paper_main_soft_min_lipschitz; try assumption.
intros y Hy; apply paper_main_soft_max_lipschitz; try assumption.
intros s Hs; apply HFG; assumption.
Qed.

Lemma paper_main_soft_sample_lipschitz d beta gamma F Y S L :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall xs ys z s, List.length xs = d -> List.length ys = d ->
    In z Y -> In s S -> Rabs (F xs z s-F ys z s) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (soft_minimax beta gamma (F xs) Y S-soft_minimax beta gamma (F ys) Y S) <=
      L * paper_main_gordon_distance d xs ys.
Proof.
intros Hb Hg HY HS HF xs ys Hx Hy.
apply paper_main_soft_minimax_lipschitz; try assumption.
intros z s Hz Hs; apply HF; assumption.
Qed.

Theorem paper_main_soft_gaussian_le_measurable d beta gamma F Y S L c :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= L ->
  (forall xs ys z s, List.length xs = d -> List.length ys = d ->
    In z Y -> In s S -> Rabs (F xs z s-F ys z s) <= L * paper_main_gordon_distance d xs ys) ->
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle (soft_minimax beta gamma (F (tval x)) Y S) c].
Proof.
intros Hb Hg HY HS HL HF; apply (paper_main_gaussian_continuous_le_measurable d (fun xs => soft_minimax beta gamma (F xs) Y S) c).
apply (paper_main_gaussian_lipschitz_continuous d (fun xs => soft_minimax beta gamma (F xs) Y S) L); first exact HL.
exact (paper_main_soft_sample_lipschitz d beta gamma F Y S L Hb Hg HY HS HF).
Qed.
