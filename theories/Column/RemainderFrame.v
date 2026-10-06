(* Operator norm bound on the error E_k of the non-backtracking recursion
   (pmlo_E) for the square-free feature columns of a sample that satisfies
   the frame conditions paper_main_column_frame_good.

   paper_main_column_remainder_frame_scaled: if 0 < delta <= 1,
   kap N <= 2, kap^2 N = 1/C(d,2) and d <= C0 N delta^2, then for every k
   the operator norm of E_k is at most
     ((k+2) (4 C0)^(k+2) + 4^(k+1) (2 C0) + 2^k) delta.
   The proof splits E_k into three terms (paper_main_column_remainder_split)
   and bounds each one: the cross term by pmcr_cross_opbound, the column
   norm term by paper_main_column_coefficient_opbound and the diagonal term
   by pmcr_diagonal_error. Deterministic. *)
From Stdlib Require Import Reals List Lia FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions
  Geometry.HeadCoefficients Geometry.HeadFrobenius SquareFree.EdgeLower
  SquareFree.WalkNB Column.Remainder Column.RemainderBounds
  Column.RemainderPowers Column.RemainderCross Column.RemainderScaling
  Column.ConcentrationFrame Column.ConcentrationCoefficient.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Theorem paper_main_column_remainder_frame_scaled N d (C0 delta kap : R)
    (x : paper_main_sample N d) :
  (0 < N)%N -> 0 <= C0 -> 0 < delta -> delta <= 1 -> 0 <= kap ->
  kap*N%:R <= 2 -> kap^+2*N%:R = (('C(d,2))%:R)^-1 ->
  d%:R <= (C0*N%:R)*delta^+2 -> paper_main_column_frame_good N d C0 delta x ->
  forall k, pmlo_opb N
    (pmlo_E N [the finType of ('I_d * 'I_d)%type] (@pmnb_X R d (tval x) N) kap (kap*N%:R) k)
    (((k.+2)%:R*(2*(2*C0))^+k.+2 + 4^+k.+1*(2*C0) + 2^+k)*delta).
Proof.
move=>HN HC Hd Hd1 Hkap Hs Hnorm Hentry Hframe k.
have Hn : 0 < N%:R :> R by rewrite ltr0n.
have Hn0 := ltW Hn.
have Hd0 := ltW Hd.
pose C := [the finType of ('I_d * 'I_d)%type].
pose X : 'I_N -> C -> R := @pmnb_X R d (tval x) N.
pose U : R := C0*N%:R.
have HU : 0 <= U by apply: mulr_ge0.
have Hh : kap*U <= 2*C0.
{ rewrite /U mulrCA [leRHS]mulrC; exact (ler_wpM2l HC Hs). }
have Hframe0 := Hframe.
case: Hframe0=>[[HQ Hratio] [HX [Hm HmU]] HG HD Hdiag].
have [Hb Hmb HbU HmUb] := pmcr_tolerance_energy U d%:R delta HU Hm Hd0 Hd1 Hentry.
have Hp : (2 <= k.+2)%N by [].
have Hcross := pmcr_cross_opbound N C X U d%:R (U*delta) HU Hm Hb Hmb HmU HbU HmUb HQ HX HD HG k.+2 Hp.
have HcrossS := pmcr_cross_scaled N C X U (U*delta) kap k.+2 Hkap Hcross.
have HcrossB := pmcr_cross_radius_bound kap U delta (2*C0) k.+1 Hkap HU Hd0 Hh.
have HCROSS : pmlo_opb N (kap^+k.+2 *: (\sum_c ((pmcr_rankone N C X c-pmcr_diagonal N C X c)^+k.+2-
  (pmcr_rankone N C X c)^+k.+2))) ((k.+2)%:R*(2*(2*C0))^+k.+2*delta).
{ exact: (pmlo_opb_le N _ _ _ HcrossS HcrossB). }
have Hcoef := paper_main_column_coefficient_opbound N d C0 delta x k.+1 HN Hd Hd1 Hframe.
have HcoefS := pmlo_opb_scale N _ _ (kap^+k.+2) Hcoef.
rewrite ger0_norm ?exprn_ge0 // in HcoefS.
have HcoefB := pmcr_coefficient_radius_bound (kap*N%:R) (kap*U) (2*C0) delta k.+1
  (mulr_ge0 Hkap Hn0) Hs (mulr_ge0 Hkap HU) Hh Hd0.
have HCOEF : pmlo_opb N
  (kap^+k.+2 *: (\sum_c (((pmcr_column_norm N C X c)^+k.+1-N%:R^+k.+1) *: pmcr_rankone N C X c)))
  ((4^+k.+1*(2*C0))*delta).
{ apply: (pmlo_opb_le N _ _ _ HcoefS).
  change (kap^+k.+2*(N%:R^+k.+1*(2^+k.+1-1)*delta*U) <= (4^+k.+1*(2*C0))*delta).
  rewrite pmcr_coefficient_radius_identity; exact HcoefB. }
have HDIAG0 : pmlo_opb N ((kap^+2*N%:R) *: (\sum_c pmcr_diagonal N C X c)-1%:M) delta.
{ apply: pmcr_diagonal_error=>// i.
  rewrite Hnorm mulrC; exact: Hdiag. }
have HDIAGS := pmlo_opb_scale N _ _ ((kap*N%:R)^+k) HDIAG0.
rewrite ger0_norm ?exprn_ge0 ?mulr_ge0 // in HDIAGS.
have HDIAG : pmlo_opb N ((kap*N%:R)^+k *: ((kap^+2*N%:R) *: (\sum_c pmcr_diagonal N C X c)-1%:M)) (2^+k*delta).
{ apply: (pmlo_opb_le N _ _ _ HDIAGS).
  exact (pmcr_diagonal_radius_bound (kap*N%:R) delta k (mulr_ge0 Hkap Hn0) Hs Hd0). }
have Hsum := pmlo_opb_add N _ _ _ _ (pmlo_opb_add N _ _ _ _ HCROSS HCOEF) HDIAG.
rewrite paper_main_column_remainder_split //.
apply: (pmlo_opb_le N _ _ _ Hsum).
change ((k.+2)%:R*(2*(2*C0))^+k.+2*delta+(4^+k.+1*(2*C0))*delta+2^+k*delta <=
 ((k.+2)%:R*(2*(2*C0))^+k.+2+4^+k.+1*(2*C0)+2^+k)*delta).
by rewrite !mulrDl.
Qed.
