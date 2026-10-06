(* The bad event of the clipped compact value for a subcritical tail, and its
   probability.

   For d = S n, a head h of m points and a tail x of q points of R^d,
   paper_main_head_subcritical_bad is the event that capped unit duals
   exist, the head section width is at least
   (1/2 - (1/2 - sqrt alpha)/16) d, the tail features clipped at d^(1/4)
   satisfy the operator bound L sqrt d, and yet the clipped compact value is
   at most ((1/2 - sqrt alpha)/4) sqrt d.
   - paper_main_head_subcritical_bad_measurable: it is measurable for
     kappa >= 1.
   - paper_main_head_subcritical_bad_probability: for 0 <= alpha < 1/4,
     kappa >= 1 and L >= 0 there are theta, c > 0 such that, for all large
     d, all m, all q <= alpha d^2 and every row permutation pi, the event
     that the head selection by pi is bad is measurable with probability at
     most exp(-c d sqrt d). It follows from
     paper_main_head_subcritical_selected_tail. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology ereal measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral measurable_realfun probability.
From EllipsoidFitting Require Import AnalysisBridge GaussianProbabilityProductContinuity
  GaussianProbabilityProductDefinitions PaperMainDefinitions PaperMainGordonProcessCovariance
  PaperMainHeadSelectionLaw PaperMainHeadSectionMeasurable PaperMainHeadSectionWidthLaw
  PaperMainHeadSectionApprox PaperMainDataClipped PaperMainHeadSubcriticalConditional
  PaperMainHeadCompactEvent PaperMainHeadCompactEventOperator PaperMainHeadCompactEventClipped.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_head_subcritical_bad n m q alpha kappa theta L :
    set (paper_main_sample m (S n) * paper_main_sample q (S n)) :=
  [set hx |
    (exists y, paper_main_head_capped_dual q (S n) theta y) /\
    ((((1/2-(1/2-sqrt alpha)/16)*INR (S n))%Rcoq)%:E <=
      paper_main_head_section_width n m kappa hx.1)%E /\
    paper_main_head_section_operator_bound q
      (fun i => paper_main_data_clipped_feature (sqrt(sqrt(INR (S n)))) n i (tval hx.2))
      (L*sqrt(INR (S n)))%Rcoq /\
    (paper_main_head_compact_clipped_value n m q kappa theta (sqrt(sqrt(INR (S n)))) hx.1 hx.2 <=
      (((1/2-sqrt alpha)/4)*sqrt(INR (S n)))%Rcoq)%R].

Lemma paper_main_head_width_good_measurable n m q kappa a :
  1 <= kappa ->
  measurable [set hx : paper_main_sample m (S n) * paper_main_sample q (S n) |
    (a%:E <= paper_main_head_section_width n m kappa hx.1)%E].
Proof.
move=> Hk; rewrite -[X in measurable X]setTI.
apply: measurable_lee => //.
apply: measurableT_comp _ measurable_fst.
apply: paper_main_head_section_width_measurable; exact/RleP.
Qed.

Lemma paper_main_head_subcritical_bad_measurable n m q alpha kappa theta L :
  1 <= kappa -> measurable (paper_main_head_subcritical_bad n m q alpha kappa theta L).
Proof.
move=> Hk.
have HkMC : (1 <= kappa)%R by exact/RleP.
have [HY|HY] := pselect (exists y, paper_main_head_capped_dual q (S n) theta y).
- have E : paper_main_head_subcritical_bad n m q alpha kappa theta L =
    [set hx : paper_main_sample m (S n) * paper_main_sample q (S n) |
      ((((1/2-(1/2-sqrt alpha)/16)*INR (S n))%Rcoq)%:E <= paper_main_head_section_width n m kappa hx.1)%E] `&`
    ([set hx : paper_main_sample m (S n) * paper_main_sample q (S n) |
      paper_main_head_section_operator_bound q
        (fun i => paper_main_data_clipped_feature (sqrt(sqrt(INR (S n)))) n i (tval hx.2))
        (L*sqrt(INR (S n)))] `&`
    [set hx : paper_main_sample m (S n) * paper_main_sample q (S n) |
      (paper_main_head_compact_clipped_value n m q kappa theta (sqrt(sqrt(INR (S n)))) hx.1 hx.2 <=
        (((1/2-sqrt alpha)/4)*sqrt(INR (S n)))%Rcoq)%R]).
  { by apply/seteqP; split=> hx; [case=> _|move=> H; split]. }
  rewrite E; apply: measurableI.
  + exact: paper_main_head_width_good_measurable.
  + apply: measurableI.
    * exact: paper_main_head_compact_clipped_operator_measurable.
    * apply: paper_main_head_section_le_measurable; last exact: measurable_cst.
      exact: paper_main_head_compact_clipped_measurable.
- have E : paper_main_head_subcritical_bad n m q alpha kappa theta L = set0.
  { apply/seteqP; split=> hx; last by case.
    by case=> H _; exact: HY H. }
  rewrite E; exact: measurable0.
Qed.

Theorem paper_main_head_subcritical_bad_probability alpha kappa L :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  exists theta c, 0 < theta /\ 0 < c /\
  exists D, forall n, Nat.le D n -> forall m q (pi : 'S_(m+q)),
    INR q <= alpha*(INR (S n))^2 ->
    measurable (paper_main_head_selection m q (S n) pi @^-1`
      paper_main_head_subcritical_bad n m q alpha kappa theta L) /\
    (paper_main_probability (m+q) (S n)
      (paper_main_head_selection m q (S n) pi @^-1`
        paper_main_head_subcritical_bad n m q alpha kappa theta L) <=
      (exp(-c*INR (S n)*sqrt(INR (S n))))%:E)%E.
Proof.
move=> Ha Hab Hk HL.
have [theta [c [Ht [Hc [D HD]]]]] :=
  paper_main_head_subcritical_selected_tail alpha kappa L Ha Hab Hk HL.
exists theta,c; split; first exact Ht; split; first exact Hc.
exists D => n Hn m q pi HN.
have mE := paper_main_head_subcritical_bad_measurable n m q alpha kappa theta L Hk.
have [HY|HY] := pselect (exists y, paper_main_head_capped_dual q (S n) theta y); last first.
- have E : paper_main_head_selection m q (S n) pi @^-1`
    paper_main_head_subcritical_bad n m q alpha kappa theta L = set0.
  { apply/seteqP; split=> x; last by case.
    by case=> H _; exact: HY H. }
  rewrite E; split; first exact: measurable0.
  rewrite /paper_main_probability measure0 lee_fin; apply/RleP; apply Rlt_le,exp_pos.
case: q pi HN HY mE => [|q] pi HN HY mE.
- case: HY => y [Hy _].
  change (0 = 1) in Hy; lra.
- apply: (HD n Hn m q (paper_main_head_capped_dual (S q) (S n) theta) pi
    (paper_main_head_subcritical_bad n m (S q) alpha kappa theta L) HN HY _ _ mE).
  + move=> y Hy; exact: paper_main_head_capped_dual_unit Hy.
  + move=> y i Hy Hi.
    have Hi' : (i < S q)%N by apply/ssrnat.ltP; lia.
    have HH := (proj2 Hy) i Hi'.
    exact HH.
  + move=> h x [_ [Hwidth [Hop Hbad]]]; split.
    * have HkMC : (1 <= kappa)%R by exact/RleP.
      have Hfin := paper_main_head_section_width_fin n m kappa h HkMC.
      rewrite -(fineK Hfin) lee_fin in Hwidth.
      apply/RleP; exact Hwidth.
    * split; first exact Hop.
      apply/RleP; exact Hbad.
Qed.
