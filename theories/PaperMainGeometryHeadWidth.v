(* The supremum form of the width transfer eq:width-transfer of
   lem:head-correction-bounds (manuscript lines 990-995 and the last
   sentence of its proof).

   For a unit-sphere set A of matrices, the support value
   sup_(S in A) <Z, S> is the MathComp-Analysis supremum of the values
   <Z, S>, S in A; these are bounded by |Z|_F. With
   K_kappa \cap S_F = paper_main_head_cone_sphere kappa (the Loewner form of
   paper_main_head_condition, with unit Frobenius norm) and
   K_kappa \cap ker W_J \cap S_F = paper_main_head_section kappa W:
   if P maximizes <Z, .> on K_(kappa_0) \cap S_F and Pt in the section
   satisfies <Z, Pt> >= <Z, P> - 2 eta |Z|_F, then
   sup_(section) <Z, S> >= sup_(K_(kappa_0) \cap S_F) <Z, R> - 2 eta |Z|_F.
   With paper_main_head_correction_bounds_cone this is eq:width-transfer on
   the features with error 2 eta |Z|_F, for every injective head.
   The existence of a (measurable) maximizer P and the data-event
   hypotheses of paper_main_head_correction_bounds_cone are not proved
   here. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* K_kappa \cap S_F, with K_kappa \ {0} in Loewner form. *)
Definition paper_main_head_cone_sphere {d : nat} (kappa : R) : set 'M[R]_d :=
  [set S | paper_main_head_condition kappa S /\ paper_main_frobenius S = 1].

(* K_kappa \cap ker W_J \cap S_F. *)
Definition paper_main_head_section {d m : nat} (kappa : R) (W : 'I_m -> 'M[R]_d) :
    set 'M[R]_d :=
  [set S | paper_main_head_condition kappa S /\ paper_main_frobenius S = 1 /\
     forall k : 'I_m, paper_main_pairing (W k) S = 0].

(* The support value sup_(S in A) <Z, S>. *)
Definition paper_main_head_support {d : nat} (Z : 'M[R]_d) (A : set 'M[R]_d) : R :=
  sup [set paper_main_pairing Z S | S in A].

Section Width.
Variable d : nat.
Implicit Types (P S Z : 'M[R]_d) (A : set 'M[R]_d).

Lemma pmh_support_ubound Z A :
  (forall S, A S -> paper_main_frobenius S = 1) ->
  ubound [set paper_main_pairing Z S | S in A] (paper_main_frobenius Z).
Proof.
move=> HA _ [S HS <-].
have Hb := pmh_pairing_frobenius_bound _ Z S.
rewrite (HA S HS) mulr1 in Hb.
exact: le_trans (ler_norm _) Hb.
Qed.

Lemma pmh_support_ge Z A S :
  (forall S, A S -> paper_main_frobenius S = 1) -> A S ->
  paper_main_pairing Z S <= paper_main_head_support Z A.
Proof.
move=> HA HS; apply: ub_le_sup; last by exists S.
by exists (paper_main_frobenius Z); exact: pmh_support_ubound.
Qed.

End Width.
