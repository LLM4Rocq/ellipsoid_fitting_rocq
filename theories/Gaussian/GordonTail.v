(* The lower tail of a Euclidean-Lipschitz test below a lower bound of its
   mean, under the Gaussian product law. For F on lists of length d with
   |F xs - F ys| <= L paper_main_gordon_distance d xs ys, L > 0, a lower
   bound b <= E_d F of its iterated expectation and u > 0,
     P [F x <= b - u] <= exp (- u^2 / (2 L^2))
   (paper_main_gaussian_lipschitz_lower_margin), from the lower tail
   paper_main_gaussian_lipschitz_lower_tail of
   Gaussian.LipschitzConcentration. The sublevel set {F x <= c} of a jointly
   continuous F is measurable (paper_main_gaussian_continuous_le_measurable). *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.IteratedExpectationDefinitions
  Gaussian.CoordinatePolynomialContinuity GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gordon.ProcessCovariance
  Gordon.Lipschitz Gordon.SetWidth Gaussian.Norm Gordon.CompactMinmax
  Gaussian.SmoothLaw Gaussian.SmoothTail Gaussian.LipschitzClip
  Gaussian.LipschitzApproximationLaw Gaussian.LipschitzConcentration.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_gaussian_continuous_le_measurable d F c :
  finite_joint_continuous d F ->
  measurable [set x : d.-tuple (measurableTypeR R) | Rle (F (tval x)) c].
Proof.
move=> HC.
have HE : [set x : d.-tuple (measurableTypeR R) | Rle (F (tval x)) c] =
  [set x | Rle (-c) (-1 * F (tval x))].
{ apply/seteqP; split=> x /= H; lra. }
rewrite HE; apply: (paper_main_gaussian_smooth_ge_measurable d (fun xs => -1 * F xs) (-c)).
apply finite_joint_continuous_scale; exact HC.
Qed.

Theorem paper_main_gaussian_lipschitz_lower_margin d F L b u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  b <= gaussian_iterated_expectation d F -> 0 < u ->
  (gaussian_product_law d [set x | Rle (F (tval x)) (b - u)] <=
    (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> HL Hlip Hb Hu.
have HC := paper_main_gaussian_lipschitz_continuous d F L (Rlt_le _ _ HL) Hlip.
have HS : [set x : d.-tuple (measurableTypeR R) | Rle (F (tval x)) (b-u)] `<=`
  [set x | Rle (F (tval x)) (gaussian_iterated_expectation d F-u)].
{ move=> x /= H; lra. }
have HM : (gaussian_product_law d [set x | Rle (F (tval x)) (b-u)] <=
  gaussian_product_law d [set x | Rle (F (tval x)) (gaussian_iterated_expectation d F-u)])%E.
{ apply: le_measure; rewrite ?inE.
  - exact: paper_main_gaussian_continuous_le_measurable.
  - exact: paper_main_gaussian_continuous_le_measurable.
  - exact HS. }
exact: le_trans HM (paper_main_gaussian_lipschitz_lower_tail d F L u HL Hlip Hu).
Qed.
