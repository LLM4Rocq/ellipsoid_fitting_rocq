(* Gordon lower tails for the actual set-index min-max under the public
   Gaussian matrix law. The exact Gaussian norm mean is preserved. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import GaussianCoordinateDefinitions GaussianProductDefinitions
  GaussianCoordinatePolynomialContinuity GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainGordonProcessCovariance
  PaperMainGordonLipschitz PaperMainGordonSetWidth PaperMainGaussianNorm
  PaperMainGordonCompactMinmax PaperMainGordonCompactExpectation
  PaperMainGaussianSmoothLaw PaperMainGaussianSmoothTail PaperMainGaussianLipschitzClip
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianLipschitzConcentration.
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

Theorem paper_main_gaussian_gordon_minmax_law N M T :
  Nat.lt 0 N -> (exists v, T v) ->
  (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  (gaussian_product_law (N*M)).-integrable setT
    (fun x => (paper_main_gordon_compact_minmax N M T (tval x))%:E) /\
  (\int[gaussian_product_law (N*M)]_x
     (paper_main_gordon_compact_minmax N M T (tval x))%:E =
    (gaussian_iterated_expectation (N*M) (paper_main_gordon_compact_minmax N M T))%:E)%E.
Proof.
move=> HN HT HU.
exact (paper_main_gaussian_lipschitz_law (N*M) (paper_main_gordon_compact_minmax N M T) 1 Rle_0_1
  (paper_main_gordon_compact_minmax_lipschitz N M T HN HT HU)).
Qed.

Theorem paper_main_gaussian_gordon_lower_tail N M T u :
  Nat.lt 0 N -> (exists v, T v) ->
  (forall v, T v -> paper_main_gordon_dot M v v = 1) -> 0 < u ->
  (gaussian_product_law (N*M) [set x |
    Rle (paper_main_gordon_compact_minmax N M T (tval x))
      (paper_main_gordon_set_width M T -
       gaussian_iterated_expectation N paper_main_gaussian_norm - u)] <=
    (exp (-u ^ 2 / 2))%:E)%E.
Proof.
move=> HN HT HU Hu.
have H := paper_main_gaussian_lipschitz_lower_margin (N*M)
  (paper_main_gordon_compact_minmax N M T) 1
  (paper_main_gordon_set_width M T - gaussian_iterated_expectation N paper_main_gaussian_norm) u
  Rlt_0_1 (paper_main_gordon_compact_minmax_lipschitz N M T HN HT HU)
  (paper_main_gordon_compact_expectation N M T HN HT HU) Hu.
replace (2 * 1 ^ 2) with 2 in H by ring; exact H.
Qed.

(* The manuscript's stated 2 exp(-u^2/4) bound follows from the stronger
   concentration bound above; the same infimum/supremum and exact norm mean. *)
Theorem paper_main_gaussian_gordon_paper_tail N M T u :
  Nat.lt 0 N -> (exists v, T v) ->
  (forall v, T v -> paper_main_gordon_dot M v v = 1) -> 0 < u ->
  (gaussian_product_law (N*M) [set x |
    Rle (paper_main_gordon_compact_minmax N M T (tval x))
      (paper_main_gordon_set_width M T -
       gaussian_iterated_expectation N paper_main_gaussian_norm - u)] <=
    (2 * exp (-u ^ 2 / 4))%:E)%E.
Proof.
move=> HN HT HU Hu.
apply: le_trans (paper_main_gaussian_gordon_lower_tail N M T u HN HT HU Hu) _.
rewrite lee_fin; apply/RleP.
change (exp (-u ^ 2 / 2) <= 2 * exp (-u ^ 2 / 4)).
have HE : exp (-u ^ 2 / 2) <= exp (-u ^ 2 / 4).
  destruct (Rle_lt_or_eq_dec (-u ^ 2 / 2) (-u ^ 2 / 4) ltac:(nra)) as [Hlt|Heq].
  - apply Rlt_le, exp_increasing; exact Hlt.
  - rewrite Heq; lra.
pose proof (exp_pos (-u ^ 2 / 4)); lra.
Qed.
