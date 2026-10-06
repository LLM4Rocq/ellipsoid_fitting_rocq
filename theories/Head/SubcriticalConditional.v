(* The subcritical tail bound, integrated over the head. The points of a
   sample of m + q + 1 points are split by a permutation pi into a head of
   m points and a tail of q + 1 points (paper_main_head_selection).
   - paper_main_head_selection_section_bound: if every section of a
     measurable event E of pairs (head, tail) has probability at most p,
     then the preimage of E under the selection has probability at most p.
   - paper_main_head_subcritical_selected_tail: let 0 <= alpha < 1/4,
     kappa >= 1, L >= 0 and g = 1/2 - sqrt alpha. There are theta, c > 0
     such that, for all large n, with d = n + 1, q + 1 <= alpha d^2 and a
     nonempty set Y of unit dual vectors with coordinates at most
     theta / sqrt d, the preimage of every measurable event E is measurable
     and has probability at most exp(-c d sqrt d) when, on E, the head
     section has width at least (1/2 - g/16) d, the clipped tail features
     have operator bound L sqrt d, and the minimax over the head section is
     at most (g/4) sqrt d. For a head of large width the section bound is
     paper_main_head_subcritical_clipped_tail; for a head of smaller width
     the section of E is empty. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology ereal measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral measurable_realfun probability.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  GaussianProbabilityProductDefinitions Gaussian.ProductLawBasics
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions
  Geometry.HeadFeature Geometry.HeadWidth Gordon.ProcessCovariance Head.Law
  Head.LawBounds Head.SelectionLaw Head.SectionMinimax Head.SectionApprox
  Head.SectionWidthLaw Data.Clipped Head.SubcriticalTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_head_selection_section_bound k q d (pi : 'S_(k+q))
    (E : set (paper_main_sample k d * paper_main_sample q d)) (p : \bar R) :
  measurable E ->
  (forall h, (paper_main_probability q d (xsection E h) <= p)%E) ->
  (paper_main_probability (k+q) d (paper_main_head_selection k q d pi @^-1` E) <= p)%E.
Proof.
move=> mE HP.
rewrite (paper_main_head_selection_law k q d pi E mE).
rewrite -(paper_main_split_points_law k q d E mE).
exact: paper_main_split_points_section_bound.
Qed.

Theorem paper_main_head_subcritical_selected_tail alpha kappa L :
  0 <= alpha -> alpha < 1/4 -> 1 <= kappa -> 0 <= L ->
  let g := 1/2-sqrt alpha in
  exists theta c, 0 < theta /\ 0 < c /\
  exists D, forall n, Nat.le D n -> forall m q
    (Y : (nat -> R) -> Prop) (pi : 'S_(m+S q))
    (E : set (paper_main_sample m (S n) * paper_main_sample (S q) (S n))),
    INR (S q) <= alpha*(INR (S n))^2 ->
    (exists y, Y y) -> (forall y, Y y -> paper_main_gordon_dot (S q) y y = 1) ->
    (forall y i, Y y -> (i <= q)%coq_nat -> Rabs(y i) <= theta/sqrt(INR (S n))) ->
    measurable E ->
    (forall h x, E (h,x) ->
      (1/2-g/16)*INR (S n) <= fine (paper_main_head_section_width n m kappa h) /\
      paper_main_head_section_operator_bound (S q)
        (fun i => paper_main_data_clipped_feature (sqrt(sqrt(INR (S n)))) n i (tval x))
        (L*sqrt(INR (S n))) /\
      paper_main_head_section_minimax kappa (S q) Y
        (fun k : 'I_m => paper_main_head_feature h k)
        (fun i => paper_main_data_clipped_feature (sqrt(sqrt(INR (S n)))) n i (tval x)) <=
          (g/4)*sqrt(INR (S n))) ->
    measurable (paper_main_head_selection m (S q) (S n) pi @^-1` E) /\
    (paper_main_probability (m+S q) (S n)
      (paper_main_head_selection m (S q) (S n) pi @^-1` E) <=
      (exp(-c*INR (S n)*sqrt(INR (S n))))%:E)%E.
Proof.
move=> Ha Hab Hk HL g.
have [eps [A [theta [c [He [HA [Ht [Hc [D HD]]]]]]]]] :=
  paper_main_head_subcritical_clipped_tail alpha kappa L Ha Hab Hk HL.
exists theta,c; split; first exact Ht; split; first exact Hc.
exists D => n Hn m q Y pi E HN HY Hunit Hcap mE HE.
split.
- have H := paper_main_head_selection_measurable m (S q) (S n) pi measurableT E mE.
  by rewrite setTI in H.
- apply: paper_main_head_selection_section_bound => // h.
  have [Hwidth|Hwidth] := pselect
    ((1/2-g/16)*INR (S n) <= fine (paper_main_head_section_width n m kappa h)).
  + apply: (HD n Hn m q h Y (xsection E h) HN HY Hunit Hcap Hwidth).
    * exact: measurable_xsection.
    * move=> x /xsectionP Hx; exact: (proj2 (HE h x Hx)).
  + have Hempty : xsection E h = set0.
    { apply/seteqP; split=> x; last by case.
      move/xsectionP=> Hx; exact: Hwidth (proj1 (HE h x Hx)). }
    rewrite Hempty /paper_main_probability measure0 lee_fin; apply/RleP; apply Rlt_le,exp_pos.
Qed.
