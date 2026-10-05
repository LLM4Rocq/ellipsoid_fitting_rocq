(* The entropy-shifted normalized soft minimum
     Z = (soft_min beta f I + ln |I| / beta) / N
   (paper_main_loss_soft_normalized), for beta > 0, N > 0 and a nonempty
   list I. Deterministic.
   - paper_main_loss_soft_min_monotone: soft_min is monotone in f.
     paper_main_loss_soft_min_constant: the soft minimum of a constant c is
     c - ln |I| / beta.
   - paper_main_loss_soft_normalized_bounds: if 0 <= f j <= N on I, then
     0 <= Z <= 1.
   - paper_main_loss_soft_normalized_minimum:
     min f / N <= Z <= min f / N + ln |I| / (beta N).
   - paper_main_loss_soft_normalized_gap: if f j >= N e on I, then
     Z >= e. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums PaperMainSoftLipschitz
  PaperMainLossArray PaperMainDataFeatureMomentsCoordinates.
Open Scope R_scope.

Lemma paper_main_loss_soft_min_monotone beta f g I : 0<beta -> I<>nil ->
  (forall j, In j I -> f j<=g j) -> soft_min beta f I<=soft_min beta g I.
Proof.
intros Hb HI Hfg.
pose proof(paper_main_soft_max_monotone beta (fun j => -g j) (fun j => -f j) I Hb HI
  ltac:(intros j Hj; pose proof(Hfg j Hj); lra)) as H.
unfold soft_min; lra.
Qed.

Lemma paper_main_loss_soft_min_constant beta c I : 0<beta -> I<>nil ->
  soft_min beta (fun _ => c) I=c-Rpower.ln(INR(List.length I))/beta.
Proof.
intros Hb HI.
assert (HL : 0<INR(List.length I)) by (apply lt_0_INR; destruct I; [contradiction|simpl; lia]).
unfold soft_min,soft_max.
rewrite finite_sum_const.
rewrite (ln_mult (INR(List.length I)) (exp(beta*(-c))) HL (exp_pos _)), ln_exp.
field; lra.
Qed.

Definition paper_main_loss_soft_normalized N beta f I :=
  /INR N*(soft_min beta f I+Rpower.ln(INR(List.length I))/beta).

Theorem paper_main_loss_soft_normalized_bounds N beta f I : Nat.lt 0 N -> 0<beta -> I<>nil ->
  (forall j, In j I -> 0<=f j<=INR N) -> 0<=paper_main_loss_soft_normalized N beta f I<=1.
Proof.
intros HN Hb HI HF.
pose proof(paper_main_loss_soft_min_monotone beta (fun _ => 0) f I Hb HI
  ltac:(intros j Hj; apply HF; exact Hj)) as HL.
pose proof(paper_main_loss_soft_min_monotone beta f (fun _ => INR N) I Hb HI
  ltac:(intros j Hj; apply HF; exact Hj)) as HU.
rewrite (paper_main_loss_soft_min_constant beta 0 I Hb HI) in HL.
rewrite (paper_main_loss_soft_min_constant beta (INR N) I Hb HI) in HU.
assert (HNpos : 0<INR N) by (apply lt_0_INR; exact HN).
pose proof(Rinv_0_lt_compat _ HNpos) as Hinv.
assert (HE : /INR N*INR N=1) by (field; lra).
unfold paper_main_loss_soft_normalized; split.
- apply Rmult_le_pos; lra.
- pose proof(Rmult_le_compat_l (/INR N) _ _ ltac:(lra) HU); nra.
Qed.

Theorem paper_main_loss_soft_normalized_minimum N beta f I : Nat.lt 0 N -> 0<beta -> I<>nil ->
  /INR N*finite_min f I<=paper_main_loss_soft_normalized N beta f I /\
  paper_main_loss_soft_normalized N beta f I<=/INR N*finite_min f I+
    Rpower.ln(INR(List.length I))/(beta*INR N).
Proof.
intros HN Hb HI; pose proof(soft_min_bounds beta f I Hb HI) as [HL HU].
assert (HNpos : 0<INR N) by (apply lt_0_INR; exact HN).
pose proof(Rinv_0_lt_compat _ HNpos) as Hinv.
pose proof(Rmult_le_compat_l (/INR N) _ _ ltac:(lra) HL) as H1.
pose proof(Rmult_le_compat_l (/INR N) _ _ ltac:(lra) HU) as H2.
assert (HE : /INR N*(Rpower.ln(INR(List.length I))/beta)=Rpower.ln(INR(List.length I))/(beta*INR N))
  by (field; lra).
unfold paper_main_loss_soft_normalized; split; nra.
Qed.

Theorem paper_main_loss_soft_normalized_gap N beta f I e : Nat.lt 0 N -> 0<beta -> I<>nil ->
  (forall j, In j I -> INR N*e<=f j) -> e<=paper_main_loss_soft_normalized N beta f I.
Proof.
intros HN Hb HI Hf.
pose proof(finite_min_lower f I (INR N*e) HI Hf) as HL.
pose proof(proj1(paper_main_loss_soft_normalized_minimum N beta f I HN Hb HI)) as HZ.
assert (HNpos : 0<INR N) by (apply lt_0_INR; exact HN).
pose proof(Rmult_le_compat_l (/INR N) _ _ ltac:(apply Rlt_le,Rinv_0_lt_compat; exact HNpos) HL) as HH.
replace (/INR N*(INR N*e)) with e in HH by (field; lra); lra.
Qed.
