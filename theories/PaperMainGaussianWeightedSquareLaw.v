(* Weighted centered Gaussian squares under the product law
   gaussian_product_law d. Q d a xs = sum_(i < d) a_i (x_i^2 - 1) is
   continuous (paper_main_weighted_square_continuous). Read on row vectors
   through GaussianLawBridge, Q is the weighted centered chi-square
   centered_chi2 of the library, so its two-sided tail is
   gauss_centered_chi2_abs_tail: with |a_i| <= L, v = sum_(i < d) a_i^2,
   u > 0 and v + L u > 0,
     P[u <= |Q|] <= 2 exp (- u^2 / (4 v + 4 L u))
   (paper_main_weighted_square_two_sided_tail). *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From GaussianAnalysis Require Import measurable_matrix gauss euclidean chi_square.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianFiniteSums
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianProbabilityProductDefinitions GaussianLawBridge RealsBridge
  PaperMainGaussianWeightedSquare PaperMainGaussianLipschitzConcentration.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation RR := (R : realType).

Lemma paper_main_weighted_square_continuous d (a : nat -> R) :
  finite_joint_continuous d (paper_main_weighted_square d a).
Proof.
rewrite /paper_main_weighted_square.
apply: (finite_joint_continuous_sum d (List.seq 0 d)
  (fun i xs => a i * (List.nth i xs 0 ^ 2 - 1))) => i Hi.
have Hi' := proj1 (List.in_seq _ _ _) Hi.
apply: finite_joint_continuous_scale.
apply: (finite_joint_continuous_ext d (fun xs => List.nth i xs 0 * List.nth i xs 0 + -1)).
  by move=> xs _; ring.
apply: finite_joint_continuous_add; last exact: finite_joint_continuous_constant.
by apply: finite_joint_continuous_mult; apply: finite_joint_continuous_nth; lia.
Qed.

Theorem paper_main_weighted_square_two_sided_tail d (a : nat -> R) L u :
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d [set x | Rle u (Rabs (paper_main_weighted_square d a (tval x)))] <=
    (2 * exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) + 4 * L * u)))%:E)%E.
Proof.
move=> Ha HL Hu Hden.
pose ar : 'rV[RR]_d := (\row_i a i)%R.
have Qr x : paper_main_weighted_square d a (list_of_row x) = centered_chi2 ar x.
  rewrite /paper_main_weighted_square paper_main_gaussian_finite_sum_seq /centered_chi2.
  by apply: eq_bigr => i _; rewrite mxE list_of_row_nth RpowE.
have vr : finite_sum (fun i => a i ^ 2) (List.seq 0 d) = mxdot ar ar.
  rewrite paper_main_gaussian_finite_sum_seq /mxdot big_ord1.
  by apply: eq_bigr => i _; rewrite !mxE RpowE expr2.
have mE : measurable [set x : 'rV[RR]_d | (u <= `|centered_chi2 ar x|)%R].
  have := measurableT_comp (@normr_measurable RR _) (measurable_centered_chi2 ar)
    measurableT (measurable_itv (`[u, +oo[)%R).
  rewrite setTI; congr measurable; apply/seteqP; split => x /=;
    by rewrite in_itv/= andbT.
have -> : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_weighted_square d a (tval x)))] =
    row_of_tuple d @^-1` [set x | (u <= `|centered_chi2 ar x|)%R].
  apply/seteqP; split => t /=; rewrite -Qr list_of_row_of_tuple RabsE.
    by move/RleP.
  by move=> /RleP.
rewrite -gauss_gaussian_product_law//.
have HL' : (0 <= L)%R by apply/RleP.
have Hu' : (0 < u)%R by apply/RltP.
have Ha' (i : 'I_d) : (`|ar 0 i| <= L)%R.
  by rewrite mxE -RabsE; apply/RleP; apply: Ha; apply/ssrnat.ltP.
have Hden' : (0 < mxdot ar ar + L * u)%R by rewrite -vr; apply/RltP.
apply: (le_trans (gauss_centered_chi2_abs_tail HL' Ha' Hu' Hden')).
rewrite lee_fin -vr.
have -> : 4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) + 4 * L * u =
    4 * (finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u) by ring.
by rewrite expF RpowE RdivE !IZRposE !INRE.
Qed.
