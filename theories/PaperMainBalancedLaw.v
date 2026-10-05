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
