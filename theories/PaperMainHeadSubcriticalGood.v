(* Outside the actual compact bad event, capped tails have positive cone support. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology ereal measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral measurable_realfun probability.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductContinuity
  SoftDefinitions PaperMainGeometryPsd GaussianProbabilityProductDefinitions PaperMainDefinitions
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection PaperMainGeometryHeadFeature
  PaperMainHeadTailSupportSplit PaperMainHeadSelectionLaw PaperMainHeadSectionWidthLaw
  PaperMainHeadSectionApprox PaperMainDataClipped PaperMainDataSampleTail PaperMainSoftParameterChoice
  PaperMainHeadCompactEvent PaperMainHeadCompactEventOperator PaperMainHeadCompactEventClipped
  PaperMainHeadCompactEventSelection PaperMainHeadSubcriticalEvent.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_head_subcritical_selected_good n m q alpha kappa theta L
    (J : seq nat) (pi : 'S_(m+q)) (x : paper_main_sample (m+q) (S n)) :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  uniq J -> size J = m -> all (fun i => i < m+q)%N J ->
  (forall t : 'I_m, nat_of_ord (pi (lshift q t)) = nth 0%N J t) ->
  (forall u : 'I_q,
    nat_of_ord (pi (rshift m u)) = nth 0%N (paper_main_head_complement (m+q) J) u) ->
  (1/2-(1/2-sqrt alpha)/16)*INR (S n) <=
    fine (paper_main_head_section_width n m kappa (paper_main_head_selection m q (S n) pi x).1) ->
  paper_main_head_section_operator_bound (m+q) (fun i => paper_main_head_feature x i)
    (L*sqrt(INR (S n))) ->
  ~ paper_main_data_coordinate_event (m+q) (S n) (sqrt(sqrt(INR (S n)))) x ->
  ~ (paper_main_head_selection m q (S n) pi @^-1`
    paper_main_head_subcritical_bad n m q alpha kappa theta L) x ->
  forall t : nat -> R, euclidean_norm t (List.seq 0 (m+q)) = 1 ->
    (forall i, List.In i J -> t i = 0) ->
    (forall i, Rabs(t i) <= theta/sqrt(INR (S n))) ->
    exists P : 'M[R]_(S n), paper_main_head_condition kappa P /\
      (forall i, List.In i J -> paper_main_pairing (paper_main_head_feature x i) P = 0%R) /\
      0 < paper_main_support_score (S n) (m+q) (paper_main_head_feature x) t P.
Proof.
move=> Ha Hab Hk HL HJu HJs HJa Hhead Htail Hwidth Hop Hcoord Hbad t Hunit Hzero Hcap.
pose h := (paper_main_head_selection m q (S n) pi x).1.
pose z := (paper_main_head_selection m q (S n) pi x).2.
pose a := ((1/2-sqrt alpha)/4)*sqrt(INR (S n)).
have Hgap := paper_main_soft_subcritical_gap alpha Ha Hab.
have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
have Hsqrt : 0 < sqrt(INR (S n)) by exact: sqrt_lt_R0.
have Ha0 : (0 < a)%R by apply/RltP; change (0 < a); unfold a; nra.
have HkMC : (1 <= kappa)%R by exact/RleP.
have Htailcoord := paper_main_head_compact_coordinate_tail n m q _ pi x Hcoord.
have Hcapdual := paper_main_head_restriction_capped m q n theta J t HJu HJs HJa Hunit Hzero Hcap.
have HOpRaw := paper_main_head_compact_operator_from_full n m q (L*sqrt(INR (S n))) J pi x
  HJu HJs HJa Htail (proj1 Hop) (proj2 Hop).
have HOpClip : paper_main_head_section_operator_bound q
    (fun i => paper_main_data_clipped_feature (sqrt(sqrt(INR (S n)))) n i (tval z))
    (L*sqrt(INR (S n))).
{ apply/(paper_main_head_compact_clipped_operator_eq n q _ _ z Htailcoord); exact HOpRaw. }
have Hvalue : (a < paper_main_head_compact_value n m q kappa theta h z)%R.
{ rewrite ltNge; apply/negP => Hlow.
  apply Hbad; split.
  - eexists; exact Hcapdual.
  - split.
    + have Hfin := paper_main_head_section_width_fin n m kappa h HkMC.
      rewrite -(fineK Hfin) lee_fin; exact/RleP.
    + split; first exact HOpClip.
      rewrite (paper_main_head_compact_clipped_eq n m q kappa theta _ h z Htailcoord).
      exact Hlow. }
have [P [HP [_ [HK Hpos]]]] := paper_main_head_compact_tail_duals_pos n m q kappa theta a J pi x
  HJu HJs HJa Hhead Htail Ha0 (ltW Hvalue) t Hunit Hzero Hcap.
by exists P.
Qed.
