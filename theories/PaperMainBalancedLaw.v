(* Exact finite-dimensional probability consequences of the recovered
   separation and measurability proofs. No phase-limit premise is used. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions PaperMainAsymptotics PaperMainFixedDensity
  PaperMainBalancedProbability PaperMainGeometryExclusion
  PaperMainGeometryHomogeneous PaperMainGaussianSpanning
  PaperMainGeometrySeparation PaperMainMeasurabilityFit
  PaperMainMeasurabilityBalanced PaperMainBalancedSupercritical.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma paper_main_not_fit_balanced n d (x : paper_main_sample n d) :
  (0 < d)%N -> paper_main_spanning x ->
  ~ paper_main_fit_event n d x -> paper_main_balanced_pd_event n d x.
Proof.
move=> Hd Hspan Hnotfit.
case: (pselect (paper_main_balanced_pd_event n d x)) => // Hnotbalanced.
exfalso; apply: Hnotfit.
exact: (proj2 (paper_main_fit_alternative n d x Hd Hspan) Hnotbalanced).
Qed.

Theorem paper_main_balanced_probability_complement n d :
  (0 < d)%N -> (d <= n)%N ->
  paper_main_probability n d (paper_main_balanced_pd_event n d) =
    (1 - paper_main_probability n d (paper_main_fit_event n d))%E.
Proof.
move=> Hd Hdn.
apply: paper_main_balanced_complement_from_separation.
- exact Hd.
- exact Hdn.
- exact: pm_fit_event_measurable.
- exact: pm_balanced_pd_event_measurable.
- move=> x Hspan Hnotfit.
  exact: paper_main_not_fit_balanced n d x Hd Hspan Hnotfit.
Qed.

Theorem paper_main_balanced_probability_upper n d :
  (0 < d)%N ->
  (paper_main_probability n d (paper_main_balanced_pd_event n d) <=
    1 - paper_main_probability n d (paper_main_fit_event n d))%E.
Proof.
move=> Hd.
apply: paper_main_balanced_probability_le_complement.
- exact Hd.
- exact: pm_fit_event_measurable.
- exact: pm_balanced_pd_event_measurable.
Qed.
