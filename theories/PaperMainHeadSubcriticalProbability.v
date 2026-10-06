(* Under a subcritical density, all small heads have positive tail support
   outside events of probability tending to 0.

   paper_main_head_subcritical_probability: let 0 <= alpha < 1/4,
   kappa >= 1 and L >= 0. There is theta > 0 such that for every K >= 0 and
   every N(d) with N(d) <= alpha d^2 eventually, there are measurable events
   E_d with probability tending to 0 with the following property. For all
   large d = S n, let x be a sample outside E_d and outside the coordinate
   event at d^(1/4), whose features satisfy the operator bound L sqrt d.
   Then every list J of distinct rows of length at most K d ln d, whose
   heads have section width at least (1/2 - (1/2 - sqrt alpha)/16) d
   (paper_main_head_size_width), satisfies paper_main_head_list_positive:
   some cone matrix annihilates the features of J, and every unit tail dual
   vanishing on J and capped by theta / sqrt d has a positive support score
   at such a matrix.

   For each d, paper_main_head_subcritical_family_event gives one event for
   all heads, of probability at most the number of head families times
   exp(-c d sqrt d), and paper_main_head_families_exp bounds this number by
   exp(C d (ln d)^2). The events are chosen with Hilbert's epsilon. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology ereal measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral measurable_realfun probability.
From EllipsoidFitting Require Import AnalysisBridge GaussianProbabilityProductContinuity
  GaussianProbabilityProductDefinitions PaperMainDefinitions PaperMainGeometryHeadFeature
  PaperMainHeadSectionApprox PaperMainDataSampleTail PaperMainGordonQuantization
  PaperMainHeadDataRates PaperMainClippingLimits PaperMainHeadFamilyCount
  PaperMainHeadSubcriticalFixed PaperMainHeadSubcriticalFamily.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_head_subcritical_probability alpha kappa L :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  exists theta, 0 < theta /\ forall K, 0 <= K -> forall N : nat -> nat,
    (exists DN, forall d, Nat.le DN d -> INR (N d) <= alpha*(INR d)^2) ->
    exists E : forall d, set (paper_main_sample (N d) d),
      (forall d, measurable (E d)) /\
      paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
      exists D, forall n, Nat.le D n -> forall x, ~ E (S n) x ->
        ~ paper_main_data_coordinate_event (N (S n)) (S n) (sqrt(sqrt(INR (S n)))) x ->
        paper_main_head_section_operator_bound (N (S n)) (fun i => paper_main_head_feature x i)
          (L*sqrt(INR (S n))) ->
        forall J, List.NoDup J -> List.incl J (List.seq 0 (N (S n))) ->
          INR (List.length J) <= K*INR (S n)*Rpower.ln(INR (S n)) ->
          paper_main_head_size_width n (N (S n)) (List.length J) kappa
            ((1/2-(1/2-sqrt alpha)/16)*INR (S n)) x ->
          paper_main_head_list_positive n (N (S n)) J kappa theta x.
Proof.
move=> Ha Hab Hk HL.
have [theta [c [Ht [Hc [D0 HD]]]]] := paper_main_head_subcritical_family_event alpha kappa L Ha Hab Hk HL.
exists theta; split; first exact Ht.
move=> K HK N [DN HN].
pose budget d := paper_main_gordon_ceiling (K*INR d*Rpower.ln(INR d)).
pose D := Nat.max D0 DN.
pose good n (E : set (paper_main_sample (N (S n)) (S n))) := measurable E /\
  (paper_main_probability (N (S n)) (S n) E <=
    (INR (List.length (paper_main_head_families (N (S n)) (budget (S n))))*
      exp(-c*INR (S n)*sqrt(INR (S n))))%:E)%E /\
  forall x, ~ E x ->
    ~ paper_main_data_coordinate_event (N (S n)) (S n) (sqrt(sqrt(INR (S n)))) x ->
    paper_main_head_section_operator_bound (N (S n)) (fun i => paper_main_head_feature x i)
      (L*sqrt(INR (S n))) ->
    forall J, List.NoDup J -> List.incl J (List.seq 0 (N (S n))) ->
      (List.length J <= budget (S n))%coq_nat ->
      paper_main_head_size_width n (N (S n)) (List.length J) kappa
        ((1/2-(1/2-sqrt alpha)/16)*INR (S n)) x ->
      paper_main_head_list_positive n (N (S n)) J kappa theta x.
pose pick n := epsilon (inhabits (@set0 (paper_main_sample (N (S n)) (S n)))) (good n).
have Hpick n : Nat.le D n -> good n (pick n).
{ move=> Hn; apply: epsilon_spec.
  exact: HD n ltac:(unfold D in Hn; lia) (N (S n)) (budget (S n))
    (HN (S n) ltac:(unfold D in Hn; lia)). }
pose E d : set (paper_main_sample (N d) d) :=
  match d as j return set (paper_main_sample (N j) j) with
  | O => set0
  | S n => if (D <= n)%N then pick n else set0
  end.
exists E; split.
- case=> [|n]; first exact: measurable0.
  rewrite /E; case Hdn: (D <= n)%N; last exact: measurable0.
  exact: (proj1 (Hpick n (elimT ssrnat.leP Hdn))).
split.
- have [HC0 _] := paper_main_log_successor_bound alpha Ha.
  have HC : 0 <= (K+1)*(Rpower.ln(alpha+1)+2) by nra.
  apply: (paper_main_clipped_head_union_tends_to_zero _ ((K+1)*(Rpower.ln(alpha+1)+2)) c HC Hc).
  + move=> d; exact: measure_ge0.
  + have [DL HDL] := INR_unbounded (exp 1).
    exists (Nat.max (S D) DL) => d Hdd.
    have Hlarge : exp 1 < INR d by have := le_INR DL d ltac:(lia); lra.
    have Hd : 1 <= INR d by have := exp_ineq1_le 1; lra.
    have Hlog : 1 <= Rpower.ln(INR d).
    { rewrite -(ln_exp 1); apply Rlt_le,ln_increasing; [exact: exp_pos|exact Hlarge]. }
    case: d Hdd Hlarge Hd Hlog => [|n] Hdd Hlarge Hd Hlog; first lia.
    have Hdn : (D <= n)%N by apply/ssrnat.leP; lia.
    rewrite /E Hdn.
    have [_ [HB _]] := Hpick n ltac:(lia).
    have Hbudget := proj2 (paper_main_head_data_budget K (INR (S n)) HK Hd Hlog).
    have Hcount := paper_main_head_families_exp (N (S n)) (budget (S n)) alpha (K+1)
      (INR (S n)) Ha ltac:(lra) Hd Hlog (HN (S n) ltac:(unfold D in Hdd; lia)) Hbudget.
    apply: le_trans HB _; rewrite lee_fin; apply/RleP.
    exact: Rmult_le_compat_r _ _ _ (Rlt_le _ _ (exp_pos _)) Hcount.
- have [DL HDL] := INR_unbounded (exp 1).
  exists (Nat.max D DL) => n Hn x Hx Hcoord Hop J HJu HJa Hlen HW.
  have Hdn : (D <= n)%N by apply/ssrnat.leP; lia.
  rewrite /E Hdn in Hx.
  have Hlarge : exp 1 < INR (S n) by have := le_INR DL (S n) ltac:(lia); lra.
  have Hd : 1 <= INR (S n) by have := exp_ineq1_le 1; lra.
  have Hlog : 1 <= Rpower.ln(INR (S n)).
  { rewrite -(ln_exp 1); apply Rlt_le,ln_increasing; [exact: exp_pos|exact Hlarge]. }
  have Hbudget := proj1 (paper_main_head_data_budget K (INR (S n)) HK Hd Hlog).
  have HJbudget : (List.length J <= budget (S n))%coq_nat.
  { apply INR_le; unfold budget; lra. }
  exact: (proj2 (proj2 (Hpick n ltac:(lia))) x Hx Hcoord Hop J HJu HJa HJbudget HW).
Qed.
