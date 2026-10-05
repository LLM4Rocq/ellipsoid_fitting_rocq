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
   the public features with error 2 eta |Z|_F, for every injective head.
   The existence of a (measurable) maximizer P and the data-event
   hypotheses of the capstone are not proved here. Nothing from the paper
   is assumed. *)
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

Lemma pmh_support_le_max Z A P :
  A P -> (forall S, A S -> paper_main_pairing Z S <= paper_main_pairing Z P) ->
  paper_main_head_support Z A <= paper_main_pairing Z P.
Proof.
move=> HP Hmax; apply: ge_sup; first by exists (paper_main_pairing Z P), P.
by move=> _ [S HS <-]; exact: Hmax.
Qed.

(* The supremum step of eq:width-transfer. *)
Theorem paper_main_head_width_transfer m (W : 'I_m -> 'M[R]_d) P (Pt Z : 'M[R]_d)
    (kappa0 kappa1 eta : R) :
  paper_main_head_cone_sphere kappa0 P ->
  (forall S, paper_main_head_cone_sphere kappa0 S ->
     paper_main_pairing Z S <= paper_main_pairing Z P) ->
  paper_main_head_section kappa1 W Pt ->
  paper_main_pairing Z P - 2 * eta * paper_main_frobenius Z <= paper_main_pairing Z Pt ->
  paper_main_head_support Z (paper_main_head_cone_sphere kappa0) -
    2 * eta * paper_main_frobenius Z <=
  paper_main_head_support Z (paper_main_head_section kappa1 W).
Proof.
move=> HP Hmax HPt Htr.
have H1 := pmh_support_le_max _ _ _ HP Hmax.
have H2 : paper_main_pairing Z Pt <=
    paper_main_head_support Z (paper_main_head_section kappa1 W).
  by apply: pmh_support_ge => // S [_ [HS _]].
lra.
Qed.

End Width.

(* eq:width-transfer on the public features, from the deterministic head
   correction: for a support maximizer P on K_(kappa_0) \cap S_F, every
   injective head and the explicit data-event inputs of
   paper_main_head_correction_bounds_cone. *)
Theorem paper_main_head_width_transfer_features n d m (x : paper_main_sample n d)
    (s : 'I_m -> 'I_n) (P Z : 'M[R]_d)
    (mu q0 q1 Rd lam eta A_1 A_inf delta kappa0 kappa : R) :
  (0 < d)%N -> injective s -> 0 < mu ->
  paper_main_head_coercive
    (paper_main_head_gram (fun i : 'I_n => paper_main_head_feature x i)) mu ->
  0 < q0 ->
  (forall k : 'I_m, q0 <= paper_main_pairing (paper_main_head_feature x (s k))
                              (paper_main_head_feature x (s k))) ->
  0 <= q1 ->
  (forall k l : 'I_m, l != k ->
     `|paper_main_pairing (paper_main_head_feature x (s k))
                          (paper_main_head_feature x (s l))| <= q1) ->
  0 <= Rd ->
  (forall k : 'I_m, `|paper_main_pairing (paper_main_head_feature x (s k)) P| <= Rd) ->
  paper_main_loewner_le (paper_main_head_data_gram x s) (lam *: 1%:M) ->
  m%:R * Rd ^+ 2 <= mu * eta ^+ 2 -> 0 <= eta -> eta < 1 ->
  m%:R * Rd <= mu * A_1 -> Rd + q1 * A_1 <= q0 * A_inf ->
  (Num.sqrt d%:R)^-1 * (A_inf * lam + A_1) <= delta ->
  delta < (kappa0 * Num.sqrt d%:R)^-1 ->
  kappa0 / Num.sqrt d%:R + delta <= kappa * ((kappa0 * Num.sqrt d%:R)^-1 - delta) ->
  paper_main_head_cone_sphere kappa0 P ->
  (forall S, paper_main_head_cone_sphere kappa0 S ->
     paper_main_pairing Z S <= paper_main_pairing Z P) ->
  paper_main_head_support Z (paper_main_head_cone_sphere kappa0) -
    2 * eta * paper_main_frobenius Z <=
  paper_main_head_support Z
    (paper_main_head_section kappa (fun k : 'I_m => paper_main_head_feature x (s k))).
Proof.
move=> Hd Hs Hmu HG Hq0 Hdiag Hq1 Hoff HRd0 HRd Hlam Heta2 Heta0 Heta HA1 HAinf Hdel
  Hlm Hk [HC HP] Hmax.
have [_ [C U K _ T]] := paper_main_head_correction_bounds_cone _ _ _ _ _ _ Z _ _ _ _ _ _ _ _ _ _ _
  Hd Hs Hmu HG Hq0 Hdiag Hq1 Hoff HRd0 HRd Hlam Heta2 Heta0 Heta HA1 HAinf Hdel Hlm Hk HC HP.
apply: (paper_main_head_width_transfer _ _ _ _ _ _ _ _ _ (conj HC HP) Hmax _ T).
split => //; split => // k.
by rewrite paper_main_head_feature_pairing K subrr mulr0.
Qed.
