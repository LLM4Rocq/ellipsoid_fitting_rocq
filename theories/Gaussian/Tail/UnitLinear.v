(* Two-sided tails of linear forms under the Gaussian product law. For a
   unit vector a (paper_main_gordon_dot d a a = 1) and u > 0,
     P[u <= |<a, x>|] <= 2 exp (- u^2 / 2)
   (paper_main_gaussian_unit_linear_absolute_tail). Read on row vectors
   through Gaussian.Law.LibraryBridge, <a, x> is mxdot x a, and the bound is
   gauss_mxdot_abs_tail of the library. The event is measurable
   (paper_main_gaussian_linear_absolute_measurable). *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From GaussianAnalysis Require Import measurable_matrix gauss euclidean gauss_linear.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Gaussian.Law.ProductBasics Gaussian.Law.LibraryBridge Analysis.RealsBridge
  Gordon.ProcessCovariance Gaussian.Tail.LinearMeasurable
  Gaussian.Lipschitz.Concentration.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation RR := (R : realType).

Section linear_tails.
Variables (d : nat) (a : nat -> R).

Let ar : 'rV[RR]_d := (\row_i a i)%R.

Let linear_row t : paper_main_gaussian_linear_random d a t = mxdot (row_of_tuple d t) ar.
Proof.
rewrite /paper_main_gaussian_linear_random /paper_main_gordon_dot.
rewrite finite_sum_seqE /mxdot big_ord1.
by apply: eq_bigr => i _; rewrite !mxE gpp_nthE -tnth_nth mulrC.
Qed.

Let event u : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_gaussian_linear_random d a x))] =
  row_of_tuple d @^-1` [set x | (u <= `|mxdot x ar|)%R].
Proof.
apply/seteqP; split => t /=; rewrite linear_row RabsE.
  by move/RleP.
by move=> /RleP.
Qed.

Let measurable_row_event u : measurable [set x : 'rV[RR]_d | (u <= `|mxdot x ar|)%R].
Proof.
have := measurableT_comp (@normr_measurable RR _) (measurable_mxdot ar)
  measurableT (measurable_itv (`[u, +oo[)%R).
rewrite setTI; congr measurable; apply/seteqP; split => x /=;
  by rewrite in_itv/= andbT.
Qed.

Lemma paper_main_gaussian_linear_absolute_measurable u :
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_gaussian_linear_random d a x))].
Proof.
rewrite event; have := measurable_row_of_tuple d measurableT _ (measurable_row_event u).
by rewrite setTI.
Qed.

Theorem paper_main_gaussian_unit_linear_absolute_tail u :
  paper_main_gordon_dot d a a = 1 -> 0 < u ->
  (gaussian_product_law d [set x | Rle u (Rabs (paper_main_gaussian_linear_random d a x))] <=
    (2*exp(-u^2/2))%:E)%E.
Proof.
move=> Ha Hu.
have a1 : mxdot ar ar = 1.
  rewrite -Ha /paper_main_gordon_dot finite_sum_seqE /mxdot big_ord1.
  by apply: eq_bigr => i _; rewrite !mxE.
have a0 : ar != 0%R by rewrite -mxdot_eq0 a1 oner_eq0.
rewrite event -(gauss_gaussian_product_law _ _ (measurable_row_event u)).
have Hu' : (0 <= u)%R by apply/ltW/RltP.
apply: (le_trans (gauss_mxdot_abs_tail a0 Hu')).
by rewrite /frobenius a1 sqrtr1 expr1n mulr1 lee_fin expF RpowE RdivE !IZRposE !INRE.
Qed.

End linear_tails.
