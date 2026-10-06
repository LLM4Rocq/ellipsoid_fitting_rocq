(* Support values of the PSD unit ball and unit sphere through the Moreau
   decomposition: the correct pointwise identities behind manuscript
   lem:psd-width (width of the PSD cone and its positive part).

   For symmetric Z with P = paper_main_psd_projection Z and
   h_A(Z) = sup_(S in A) <Z, S>:
   - PSD unit ball (|S|_F <= 1): h(Z) = |P|_F, for every d
     (paper_main_psd_ball_support);
   - PSD unit sphere (|S|_F = 1): h(Z) = |P|_F when P <> 0
     (paper_main_psd_sphere_support_pos), and in general, for d > 0,
     max(h(Z), 0) = |P|_F (paper_main_psd_sphere_support_max).
   Equality without the maximum fails. For Z = -I and d > 0, P = 0 while the
   sphere support is at most -1 (paper_main_psd_sphere_support_neg_identity):
   a unit PSD S has Tr S >= 1, since <S, S> <= (Tr S)^2 from
   S_ij^2 <= S_ii S_jj. So the width of the PSD unit sphere is not
   pointwise |P|_F; only its positive part is. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.Compact Geometry.HeadFrobenius
  Geometry.HeadCorrection Geometry.HeadFeature Geometry.HeadSpectral
  Geometry.HeadWidth Geometry.HeadWidthCompact Cone.Projection.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* The dimension of the projection is implicit in this file only. *)
#[local] Arguments paper_main_psd_projection {d} Z.
#[local] Arguments paper_main_psd_negative_part {d} Z.

Definition paper_main_psd_sphere {d : nat} : set 'M[R]_d :=
  [set S | paper_main_psd S /\ paper_main_frobenius S = 1].

Lemma pmcs_sup_attained (E : set R) (m : R) : E m -> ubound E m -> sup E = m.
Proof.
move=> Hm Hub; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: ge_sup => //; exists m.
by apply: (ub_le_sup (ex_intro _ m Hub)).
Qed.

Section ConeSupport.
Variable d : nat.
Implicit Types (S Z : 'M[R]_d).

Lemma pmcs_pairing_le Z S :
  paper_main_symmetric Z -> paper_main_psd S ->
  paper_main_pairing Z S <=
  paper_main_frobenius (paper_main_psd_projection Z) * paper_main_frobenius S.
Proof.
move=> HZ HS.
have [HP HN HZd Horth] := paper_main_psd_moreau _ _ HZ.
set P := paper_main_psd_projection Z in HP HZd Horth *.
set N := paper_main_psd_negative_part Z in HN HZd Horth *.
rewrite HZd pmh_pairingBl.
have HNS := pmh_pairing_psd_ge0 _ _ _ HN HS.
have CS := pmh_pairing_frobenius_bound _ P S.
have := ler_norm (paper_main_pairing P S); lra.
Qed.

Lemma pmcs_value_normalized Z :
  paper_main_symmetric Z -> paper_main_psd_projection Z != 0 ->
  paper_main_pairing Z
    ((paper_main_frobenius (paper_main_psd_projection Z))^-1 *: paper_main_psd_projection Z) =
  paper_main_frobenius (paper_main_psd_projection Z).
Proof.
move=> HZ HP0.
have [HP HN HZd Horth] := paper_main_psd_moreau _ _ HZ.
have Hp := pmh_frobenius_gt0 _ _ HP0.
set P := paper_main_psd_projection Z in HP HZd Horth Hp HP0 *.
set N := paper_main_psd_negative_part Z in HN HZd Horth *.
rewrite paper_main_pairing_scale HZd pmh_pairingBl (paper_main_pairingC _ N P) Horth subr0.
rewrite -pmh_frobenius_sqr expr2 mulrA mulVf ?mul1r //.
exact: lt0r_neq0.
Qed.

Lemma pmcs_normalized_sphere Z :
  paper_main_psd_projection Z != 0 ->
  paper_main_psd_sphere
    ((paper_main_frobenius (paper_main_psd_projection Z))^-1 *: paper_main_psd_projection Z).
Proof.
move=> HP0; split; last exact: pmh_frobenius_normalize.
apply: paper_main_psd_scale; last exact: paper_main_psd_projection_psd.
by rewrite invr_ge0; exact: pmh_frobenius_ge0.
Qed.

(* The PSD unit sphere when P <> 0. *)
Theorem paper_main_psd_sphere_support_pos Z :
  paper_main_symmetric Z -> paper_main_psd_projection Z != 0 ->
  paper_main_head_support Z paper_main_psd_sphere =
  paper_main_frobenius (paper_main_psd_projection Z).
Proof.
move=> HZ HP0; apply: pmcs_sup_attained.
  by exists ((paper_main_frobenius (paper_main_psd_projection Z))^-1 *:
    paper_main_psd_projection Z);
    [exact: pmcs_normalized_sphere | exact: pmcs_value_normalized].
move=> _ [S [HS HS1] <-].
by have := pmcs_pairing_le _ _ HZ HS; rewrite HS1 mulr1.
Qed.

Lemma pmcs_sphere_nonempty : (0 < d)%N ->
  paper_main_psd_sphere ((Num.sqrt d%:R)^-1 *: (1%:M : 'M[R]_d)).
Proof.
move=> Hd; split; last by have [_ HF] := paper_main_head_cone_sphere_nonempty _ _ Hd (lexx 1).
by apply: pmh_psd_scalar; rewrite invr_ge0 sqrtr_ge0.
Qed.

(* The PSD unit sphere in general: max(h(Z), 0) = |P|_F. *)
Theorem paper_main_psd_sphere_support_max Z :
  (0 < d)%N -> paper_main_symmetric Z ->
  Num.max (paper_main_head_support Z paper_main_psd_sphere) 0 =
  paper_main_frobenius (paper_main_psd_projection Z).
Proof.
move=> Hd HZ.
have [HP0|HP0] := eqVneq (paper_main_psd_projection Z) 0.
  have Hle : paper_main_head_support Z paper_main_psd_sphere <= 0.
    apply: ge_sup.
      by exists (paper_main_pairing Z ((Num.sqrt d%:R)^-1 *: 1%:M)), ((Num.sqrt d%:R)^-1 *: 1%:M);
        last by []; exact: pmcs_sphere_nonempty.
    move=> _ [S [HS HS1] <-].
    by have := pmcs_pairing_le _ _ HZ HS; rewrite HP0 pmh_frobenius0 mul0r.
  by rewrite max_r // HP0 pmh_frobenius0.
rewrite paper_main_psd_sphere_support_pos // max_l //.
exact: pmh_frobenius_ge0.
Qed.

End ConeSupport.
