(* Gaussian null sets, for the almost-sure spanning obligation.
   These are probability foundations, not a proof of spanning by themselves. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions GaussianProbabilityProductMeasure.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma paper_main_gaussian_singleton (a : R) :
  gaussian_law_probability [set a] = 0%E.
Proof.
have Hdom := normal_prob_dominates (0 : R) 1.
move/null_content_dominatesP: Hdom => Hdom.
apply: Hdom; [exact: measurable_set1 | exact: lebesgue_measure_set1].
Qed.
