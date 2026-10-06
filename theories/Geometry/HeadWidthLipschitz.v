(* The support functions of the unit sections are 1-Lipschitz and bounded:
   the geometric prerequisite for the measurability, integrability and
   Gaussian concentration of the widths in eq:width-transfer and
   prop:heads.

   For a nonempty set A of unit-Frobenius matrices and
   h_A(Z) = sup_(S in A) <Z, S> (paper_main_head_support):
   |h_A(Z) - h_A(Y)| <= |Z - Y|_F and |h_A(Z)| <= |Z|_F. This holds in
   particular for A = K_kappa \cap S_F (nonempty for d > 0, kappa >= 1),
   and for every head section K_kappa \cap ker W_J \cap S_F that is
   nonempty, for instance one that contains the normalized head correction.
   No maximizer, measurable or not, is used. Gaussian integration and
   concentration are not done here. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Geometry.HeadCorrection
  Geometry.HeadWidth Geometry.HeadWidthCompact.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WidthLipschitz.
Variable d : nat.
Implicit Types (S Y Z : 'M[R]_d) (A : set 'M[R]_d).

Lemma pmh_support_upper Z Y A :
  A !=set0 -> (forall S, A S -> paper_main_frobenius S = 1) ->
  paper_main_head_support Z A <=
  paper_main_head_support Y A + paper_main_frobenius (Z - Y).
Proof.
move=> HA0 HA; apply: ge_sup.
  by case: HA0 => S HS; exists (paper_main_pairing Z S), S.
move=> _ [S HS <-].
have H1 := pmh_support_ge _ Y _ _ HA HS.
have H2 := pmh_pairing_frobenius_bound _ (Z - Y) S.
rewrite (HA S HS) mulr1 in H2.
have H3 : paper_main_pairing Z S =
    paper_main_pairing Y S + paper_main_pairing (Z - Y) S.
  by rewrite pmh_pairingBl addrC subrK.
have H4 := ler_norm (paper_main_pairing (Z - Y) S).
lra.
Qed.

Theorem paper_main_head_support_lipschitz Z Y A :
  A !=set0 -> (forall S, A S -> paper_main_frobenius S = 1) ->
  `|paper_main_head_support Z A - paper_main_head_support Y A| <=
  paper_main_frobenius (Z - Y).
Proof.
move=> HA0 HA.
have H1 := pmh_support_upper Z Y A HA0 HA.
have H2 := pmh_support_upper Y Z A HA0 HA.
rewrite pmh_frobeniusB in H2.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

Theorem paper_main_head_support_bound Z A :
  A !=set0 -> (forall S, A S -> paper_main_frobenius S = 1) ->
  `|paper_main_head_support Z A| <= paper_main_frobenius Z.
Proof.
move=> HA0 HA.
have Hup : paper_main_head_support Z A <= paper_main_frobenius Z.
  apply: ge_sup; first by case: HA0 => S HS; exists (paper_main_pairing Z S), S.
  exact: pmh_support_ubound.
case: HA0 => S HS.
have Hlo := pmh_support_ge _ Z _ _ HA HS.
have Hb := pmh_pairing_frobenius_bound _ Z S.
rewrite (HA S HS) mulr1 ler_norml in Hb.
case/andP: Hb => Hb _.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(* The width of the unit section of the bounded-condition cone. *)
Corollary paper_main_head_cone_support_lipschitz (kappa : R) Z Y :
  (0 < d)%N -> 1 <= kappa ->
  `|paper_main_head_support Z (paper_main_head_cone_sphere kappa) -
    paper_main_head_support Y (paper_main_head_cone_sphere kappa)| <=
  paper_main_frobenius (Z - Y).
Proof.
move=> Hd Hk; apply: paper_main_head_support_lipschitz.
  by exists ((Num.sqrt d%:R)^-1 *: 1%:M); exact: paper_main_head_cone_sphere_nonempty.
by move=> S [_ HS].
Qed.

End WidthLipschitz.
