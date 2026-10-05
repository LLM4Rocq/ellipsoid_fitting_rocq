(* All nonspectral subcritical exceptions, with original conditioned fits outside them. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity Definitions HeadTail SoftDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadFeature
  PaperMainHeadSectionApprox PaperMainHeadSectionWidthLaw
  PaperMainHeadRegularProbability PaperMainDataSampleTail PaperMainClippingLimits
  PaperMainHeadTailSupportSplit PaperMainHeadTailSupportAll PaperMainConeHeadTailFit
  PaperMainSoftParameterChoice PaperMainHeadSubcriticalFixed PaperMainHeadSubcriticalProbability.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_head_subcritical_fit_exception alpha :
  0 <= alpha -> alpha < 1/4 ->
  exists kappa, 1 <= kappa /\ forall L c, 0 <= L -> 0 < c -> forall N : nat -> nat,
    (exists DN, forall d, Nat.le DN d -> INR (N d) <= alpha*(INR d)^2) ->
    exists E : forall d, set (paper_main_sample (N d) d),
      (forall d, measurable (E d)) /\
      paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
      exists D, forall n, Nat.le D n -> forall x, ~ E (S n) x ->
        paper_main_head_coercive
          (paper_main_head_gram (fun i : 'I_(N (S n)) => paper_main_head_feature x i))
          (c*INR (S n)) ->
        paper_main_head_section_operator_bound (N (S n)) (fun i => paper_main_head_feature x i)
          (L*sqrt(INR (S n))) ->
        paper_main_conditioned_event (N (S n)) (S n)
          (((kappa+1/2)/(1-1/2))^-1)%R (((kappa+1/2)/(1-1/2)))%R x.
Proof.
move=> Ha Hab.
have Hgap := paper_main_soft_subcritical_gap alpha Ha Hab.
have Heps : 0 < (1/2-sqrt alpha)/16 by lra.
have [kappa [Hk HK]] := paper_main_head_width_coercive_probability_uniform
  ((1/2-sqrt alpha)/16) Heps.
exists kappa; split; first exact Hk.
move=> L c HL Hc N HN.
have [theta [Ht Htheta]] := paper_main_head_subcritical_probability alpha kappa L Ha Hab Hk HL.
pose K := head_tail_constant theta.
have HK0 : 0 <= K by apply Rlt_le,head_tail_constant_positive.
have [A [mA [HA [DA HDA]]]] := HK N alpha K c Ha HK0 Hc HN.
have [B [mB [HB [DB HDB]]]] := Htheta K HK0 N HN.
pose C d := paper_main_data_coordinate_event (N d) d (sqrt(sqrt(INR d))).
have mC d : measurable (C d).
{ case: d => [|n].
  - have HC : C 0%N = set0.
    { apply/seteqP; split=> x; last by case.
      move=> [i [a _]]; by have := ltn_ord a; rewrite ltn0. }
    rewrite HC; exact: measurable0.
  - apply: (proj1 (paper_main_data_coordinate_tail (N (S n)) (S n) _ _)).
    apply sqrt_lt_R0,sqrt_lt_R0,lt_0_INR; lia. }
have HC := paper_main_coordinate_clipping_tends_to_zero N alpha Ha HN.
pose E d := A d `|` (B d `|` C d).
have mBC d : measurable (B d `|` C d).
{ apply: measurableU; [exact: mB|exact: mC]. }
have HBC := paper_main_head_exception_union_limit N B C mB mC HB HC.
exists E; split.
- move=> d; apply: measurableU; [exact: mA|exact: mBC].
split.
- exact: paper_main_head_exception_union_limit N A (fun d => B d `|` C d) mA mBC HA HBC.
- have [DS HDS] := paper_main_cone_head_tail_small_large kappa L c Hk HL Hc.
  exists (Nat.max 1 (Nat.max DA (Nat.max DB DS))) => n Hn x Hx HG Hop.
  have Hna : ~ A (S n) x by move=> H; apply Hx; left.
  have Hnb : ~ B (S n) x by move=> H; apply Hx; right; left.
  have Hnc : ~ C (S n) x by move=> H; apply Hx; right; right.
  have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
  have Hmu : 0 < c*INR (S n) by nra.
  have HG' : paper_main_head_coercive
    (paper_main_head_gram (fun i : 'I_(N (S n)) => paper_main_head_feature x i))
    (c*(S n)%:R)%R.
  { rewrite -INRE; exact HG. }
  have Hwidth : forall J : list nat, INR (List.length J) <= K*INR (S n)*Rpower.ln(INR (S n)) ->
    paper_main_head_size_width n (N (S n)) (List.length J) kappa
      ((1/2-(1/2-sqrt alpha)/16)*INR (S n)) x.
  { move=> J Hlen h s Hs HW.
    exact (HDA n ltac:(lia) x Hna HG' (List.length J) h s Hs Hlen HW). }
  have Hpositive : forall J, List.NoDup J -> List.incl J (List.seq 0 (N (S n))) ->
    INR (List.length J) <= paper_main_head_budget (S n) theta ->
    paper_main_head_list_positive n (N (S n)) J kappa theta x.
  { move=> J HJu HJa Hlen.
    exact: HDB n ltac:(lia) x Hnb Hnc Hop J HJu HJa Hlen (Hwidth J Hlen). }
  apply: (paper_main_cone_head_tail_conditioned_fit (N (S n)) (S n) x theta kappa
    (c*INR (S n)) (L*sqrt(INR (S n))) ltac:(lia) Ht Hk Hmu HG _ _ _ (HDS (S n) ltac:(lia))).
  + move=> J HJu HJa Hlen; exact: (proj1 (Hpositive J HJu HJa Hlen)).
  + move=> y; apply/RleP; exact: (proj2 Hop y).
  + move=> J HJu HJa Hlen; exact: (proj2 (Hpositive J HJu HJa Hlen)).
Qed.
