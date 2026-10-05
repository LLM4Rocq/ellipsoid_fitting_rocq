(* One exceptional event for all heads of at most K sample points.

   paper_main_head_subcritical_family_event: for 0 <= alpha < 1/4,
   kappa >= 1 and L >= 0 there are theta, c > 0 with the following property
   for every large d = S n and N <= alpha d^2. Some measurable event E has
   probability at most |paper_main_head_families N K| exp(-c d sqrt d), and
   for every sample x outside E whose coordinates are all below d^(1/4) and
   whose head features have operator bound L sqrt d, every list J of at
   most K distinct indices below N satisfies paper_main_head_list_positive,
   provided the heads of size |J| have head-section width at least
   (1/2 - (1/2 - sqrt alpha)/16) d (paper_main_head_size_width).
   E is the union, over the finite family paper_main_head_families N K, of
   the events given for each list by
   paper_main_head_subcritical_fixed_event. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology ereal measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral measurable_realfun probability.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductContinuity
  GaussianProbabilityProductDefinitions PaperMainDefinitions PaperMainGeometryHeadFeature
  PaperMainHeadSectionApprox PaperMainDataSampleTail
  PaperMainHeadFamilyCount PaperMainHeadFamilyUnion PaperMainHeadSubcriticalFixed.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_head_subcritical_family_event alpha kappa L :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  exists theta c, 0 < theta /\ 0 < c /\
  exists D, forall n, Nat.le D n -> forall N K,
    INR N <= alpha*(INR (S n))^2 ->
    exists E : set (paper_main_sample N (S n)), measurable E /\
      (paper_main_probability N (S n) E <=
        (INR (List.length (paper_main_head_families N K))*
          exp(-c*INR (S n)*sqrt(INR (S n))))%:E)%E /\
      forall x, ~ E x ->
        ~ paper_main_data_coordinate_event N (S n) (sqrt(sqrt(INR (S n)))) x ->
        paper_main_head_section_operator_bound N (fun i => paper_main_head_feature x i)
          (L*sqrt(INR (S n))) ->
        forall J, List.NoDup J -> List.incl J (List.seq 0 N) ->
          (List.length J <= K)%coq_nat ->
          paper_main_head_size_width n N (List.length J) kappa
            ((1/2-(1/2-sqrt alpha)/16)*INR (S n)) x ->
          paper_main_head_list_positive n N J kappa theta x.
Proof.
move=> Ha Hab Hk HL.
have [theta [c [Ht [Hc [D HD]]]]] := paper_main_head_subcritical_fixed_event alpha kappa L Ha Hab Hk HL.
exists theta,c; split; first exact Ht; split; first exact Hc.
exists D => n Hn N K HN.
pose good J (E : set (paper_main_sample N (S n))) :=
  measurable E /\
  (paper_main_probability N (S n) E <= (exp(-c*INR (S n)*sqrt(INR (S n))))%:E)%E /\
  forall x, ~ E x ->
    ~ paper_main_data_coordinate_event N (S n) (sqrt(sqrt(INR (S n)))) x ->
    paper_main_head_section_operator_bound N (fun i => paper_main_head_feature x i)
      (L*sqrt(INR (S n))) ->
    List.NoDup J -> List.incl J (List.seq 0 N) ->
    paper_main_head_size_width n N (List.length J) kappa
      ((1/2-(1/2-sqrt alpha)/16)*INR (S n)) x ->
    paper_main_head_list_positive n N J kappa theta x.
have Hex J : exists E, good J E.
{ have [HJ|HJ] := pselect (List.NoDup J /\ List.incl J (List.seq 0 N)).
  - have [E [mE [HB HG]]] := HD n Hn N J HN (proj1 HJ) (proj2 HJ).
    exists E; split; first exact mE; split; first exact HB.
    move=> x Hx Hcoord Hop _ _ HW; exact: HG x Hx Hcoord HW Hop.
  - exists set0; split; first exact: measurable0.
    split.
    + rewrite /paper_main_probability measure0 lee_fin; apply/RleP; apply Rlt_le,exp_pos.
    + move=> x Hx Hcoord Hop HJu HJa HW; exfalso; apply HJ; by split. }
pose pick J := epsilon (inhabits (@set0 (paper_main_sample N (S n)))) (good J).
have Hpick J : good J (pick J) by apply: epsilon_spec; exact: Hex.
exists (paper_main_head_family_event N K pick).
split.
- apply: paper_main_head_family_event_measurable => J _; exact: (proj1 (Hpick J)).
split.
- apply: paper_main_head_family_event_bound.
  + move=> J _; exact: (proj1 (Hpick J)).
  + move=> J _; exact: (proj1 (proj2 (Hpick J))).
- move=> x Hx Hcoord Hop J HJu HJa Hlen HW.
  have Hnot : ~ pick J x.
  { move=> Hj; apply Hx; apply: paper_main_head_family_event_complete Hlen _ Hj.
    move=> i Hi; have HH := HJa i Hi; apply List.in_seq in HH; lia. }
  exact: (proj2 (proj2 (Hpick J)) x Hnot Hcoord Hop HJu HJa HW).
Qed.
