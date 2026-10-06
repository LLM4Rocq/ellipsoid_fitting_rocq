(* One direction of the alternative behind cor:alternative, for a fixed
   sample. For d > 0 and points x_i that span R^d, if no S >= 0 satisfies
   x_i^T S x_i = d for every i, then some weights y with sum_i y_i = 0
   make sum_i y_i x_i x_i^T positive definite:
   paper_main_not_fit_balanced, from the equivalence
   paper_main_fit_alternative of Geometry.Separation.
   Deterministic. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions Asymptotics Fixed.Density Balanced.Probability
  Geometry.Exclusion Geometry.Homogeneous Gaussian.Spanning.AlmostSure
  Geometry.Separation Measurability.Fit Measurability.Balanced
  Balanced.Supercritical.
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
