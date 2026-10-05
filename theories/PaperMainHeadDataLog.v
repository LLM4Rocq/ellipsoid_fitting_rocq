(* Actual simultaneous logarithmic raw head-data Gram control. *)
From Stdlib Require Import Reals Lia Lra Psatz Epsilon.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadCorrection PaperMainGeometryHeadFeature
  PaperMainDataHeadOperatorUniform PaperMainGaussianFeatureTail
  PaperMainGordonEntropy PaperMainGordonQuantization PaperMainHeadDataRates
  PaperMainClippingLimits.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_head_data_log_event C K :
  0 <= C -> 0 <= K -> exists L, 0 < L /\ forall N d,
    1 <= INR d -> 1 <= Rpower.ln(INR d) -> INR N <= C*(INR d)^2 ->
    exists E : set (paper_main_sample N d), measurable E /\
      (paper_main_probability N d E <= (2/INR d)%Rcoq%:E)%E /\
      forall x, ~ E x -> forall m (s : 'I_m -> 'I_N),
        INR m <= K*INR d*Rpower.ln(INR d) -> injective s ->
        paper_main_loewner_le (paper_main_head_data_gram x s)
          ((L*INR d*(Rpower.ln(INR d))^2)%Rcoq *: 1%:M)%R.
Proof.
move=> HC HK.
pose G := paper_main_gordon_entropy_constant (1/4).
pose L := 8*(G*(1+(K+1))+(K+1)+(K+1)*(Rpower.ln(C+1)+2)+1).
have HG : 0 < G by exact: paper_main_gaussian_entropy_positive.
have Hlc := paper_main_log_successor_bound C HC.
have HL : 0 < L by unfold L; nra.
exists L; split; first exact HL.
move=> N d Hd Hlog HN.
pose b := paper_main_gordon_ceiling (K*INR d*Rpower.ln(INR d)).
have [Hblo Hbhi] := paper_main_head_data_budget K (INR d) HK Hd Hlog.
fold b in Hblo, Hbhi.
have [E [mE [HE Hgood]]] := paper_main_data_head_operator_uniform N d b (Rpower.ln(INR d)) ltac:(lra).
exists E; split; first exact mE.
split.
- have [Hrate _] := paper_main_head_data_tail_rate (INR d) Hd.
  apply: le_trans HE _; rewrite lee_fin; apply/RleP.
  rewrite -RmultE.
  change (2*exp(-Rpower.ln(INR d)) <= 2/INR d).
  rewrite Hrate; exact: Rle_refl.
- move=> x Hx m s Hm Hs.
  have HmbN : Nat.le m b.
  { apply INR_le; lra. }
  have Hmb : (m <= b)%N by exact/ssrnat.leP.
  have HS := Hgood x Hx m s Hmb Hs.
  have HR := paper_main_head_data_operator_rate C G (K+1) (INR N) (INR b) (INR d)
    HC ltac:(lra) ltac:(lra) (pos_INR N) (pos_INR b) Hd Hlog HN Hbhi.
  eapply pmh_loewner_trans; first exact HS.
  apply: pmh_loewner_scalar; apply/RleP.
  rewrite -?RmultE -?RplusE.
  change (8*(G*(INR d+INR b)+(Rpower.ln(INR b+1)+INR b*Rpower.ln(INR N+1)+Rpower.ln(INR d))) <=
    L*INR d*(Rpower.ln(INR d))^2).
  unfold L; nra.
Qed.

Definition paper_main_head_data_log_good N d K L (x : paper_main_sample N d) : Prop :=
  forall m (s : 'I_m -> 'I_N), INR m <= K*INR d*Rpower.ln(INR d) -> injective s ->
    paper_main_loewner_le (paper_main_head_data_gram x s)
      ((L*INR d*(Rpower.ln(INR d))^2)%Rcoq *: 1%:M)%R.

Theorem paper_main_head_data_log_probability (N : nat -> nat) C K :
  0 <= C -> 0 <= K ->
  (exists D, forall d, Nat.le D d -> INR (N d) <= C*(INR d)^2) ->
  exists L, 0 < L /\ exists E : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
    exists D, forall d, Nat.le D d -> forall x, ~ E d x ->
      paper_main_head_data_log_good (N d) d K L x.
Proof.
move=> HC HK [DN HN].
have [L [HL HE]] := paper_main_head_data_log_event C K HC HK.
have [DL HDL] := INR_unbounded (exp 1).
pose D := Nat.max DN DL.
pose good d (E : set (paper_main_sample (N d) d)) := measurable E /\
  (paper_main_probability (N d) d E <= (2/sqrt(INR d))%Rcoq%:E)%E /\
  forall x, ~ E x -> paper_main_head_data_log_good (N d) d K L x.
have Hex d : Nat.le D d -> exists E, good d E.
{ move=> Hdd.
  have Hlarge : exp 1 < INR d by have := le_INR DL d ltac:(unfold D in Hdd; lia); lra.
  have Hexp := exp_ineq1_le 1.
  have Hd : 1 <= INR d by lra.
  have Hlog : 1 <= Rpower.ln(INR d).
  { rewrite -(ln_exp 1); apply Rlt_le,ln_increasing; first exact: exp_pos; exact Hlarge. }
  have [E [mE [HB HG]]] := HE (N d) d Hd Hlog (HN d ltac:(unfold D in Hdd; lia)).
  exists E; split; first exact mE; split; last exact HG.
  apply: le_trans HB _; rewrite lee_fin; apply/RleP.
  exact: (proj2 (paper_main_head_data_tail_rate (INR d) Hd)). }
pose pick d := epsilon (inhabits (@set0 (paper_main_sample (N d) d))) (good d).
have Hpick d : Nat.le D d -> good d (pick d).
{ move=> Hdd; apply: epsilon_spec; exact: Hex. }
pose E d := if (D <= d)%N then pick d else set0.
exists L; split; first exact HL.
exists E; split.
- move=> d; rewrite /E; case Hdd: (D <= d)%N; last exact: measurable0.
  have HddN : Nat.le D d by exact: (elimT ssrnat.leP Hdd).
  exact: (proj1 (Hpick d HddN)).
split.
- apply: (paper_main_sqrt_rate_tends_to_zero _ 2); first lra.
  + move=> d; exact: measure_ge0.
  + exists D => d Hdd.
    have HddN : (D <= d)%N by exact/ssrnat.leP.
    rewrite /E HddN; exact: (proj1 (proj2 (Hpick d Hdd))).
- exists D => d Hdd x Hx.
  have HddN : (D <= d)%N by exact/ssrnat.leP.
  rewrite /E HddN in Hx.
  exact: (proj2 (proj2 (Hpick d Hdd)) x Hx).
Qed.
