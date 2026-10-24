(* S2 assembled from the arbitrary-shift upper fit and the simultaneous
   lower bound. The additional fit-level lower inequality follows from
   the defining infimum; it does not require an attained optimum. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From EllipsoidUniversality Require Import ShiftedGaussianStatement ConditionDefinitions.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Shifted Require Import Translations GaussianCondition ConditionLower GaussianBounds.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Theorem shifted_gaussian_theorem : shifted_gaussian_statement.
Proof.
split.
- move=>n d m C; split.
  - rewrite -[X in measurable X]setTI.
    exact: measurable_sample_translate (measurable_pd_fit_event _ _).
  - exact: measurable_gaussian_shift_fit.
  - exact: measurable_gaussian_shift_condition_number.
- move=>alpha a0.
  have [c [c0 hc]] := gaussian_translated_condition_lower a0.
  exists c; split=>// n hn eps eps0.
  have [D hD] := hc n hn eps eps0; exists D=>d dD.
  have [E [mE pE hE]] := hD d dD.
  exists E; split=>// x nx m.
  have lo := hE x nx m; split=>// B fit.
  have hi : (data_condition_number (n d) d (sample_translate m x) <= B%:E)%E.
    apply: ge_ereal_inf; exists B%:E=>//; by exists B.
  by move: (le_trans lo hi); rewrite lee_fin.
- move=>alpha a0 a4.
  have [c [C [c0 cC hC]]] := gaussian_arbitrary_shift_condition_bounds a0 a4.
  exists c,C; split=>// n m hn eps eps0.
  have [D hD] := hC n m hn eps eps0; exists D=>d dD.
  have [E [mE pE hE]] := hD d dD.
  exists E; split=>// x nx.
  have [fit bounds] := hE x nx; split=>//.
  exact: cond_sub_pd fit.
Qed.
