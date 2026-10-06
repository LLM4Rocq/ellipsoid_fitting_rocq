(* Gaussian concentration for every Euclidean-Lipschitz test on length-d
   lists, under the exact Gaussian product law. The centered exponential
   moment bound is gauss_concentration of the library: the test read on the
   coordinates of a row vector is Lipschitz for the Euclidean norm
   (paper_main_gordon_distance_list_of_row), and GaussianLawBridge carries
   the iterated expectation and the product law over to gauss d. The tails
   follow by Chernoff's bound. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianProductDefinitions GaussianProduct GaussianCoordinatePolynomialContinuity
  GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainGordonLipschitz
  PaperMainGaussianSmoothLaw PaperMainGaussianSmoothTail PaperMainGaussianTailLimit
  PaperMainGaussianLipschitzClip PaperMainGaussianLipschitzApproximation
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianLipschitzConcentrationTail.
From mathcomp Require Import matrix.
From GaussianAnalysis Require Import measurable_matrix gauss euclidean gauss_smoothing.
From GaussianAnalysis Require Import gauss_concentration.
From EllipsoidFitting Require Import GaussianCovarianceSums GaussianLawBridge RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Local Notation RR := (R : realType).

Lemma paper_main_gaussian_finite_sum_seq d (f : nat -> R) :
  finite_sum f (List.seq 0 d) = (\sum_(j < d) f j)%R.
Proof.
revert f; induction d as [|d IH]; intro f.
- by rewrite big_ord0.
- rewrite big_ord_recl /= finite_sum_seq_shift.
  change (f 0%nat + finite_sum (fun j => f (S j)) (List.seq 0 d) =
    f 0%nat + (\sum_(j < d) f (S j))%R).
  by rewrite IH.
Qed.

(* The distance of the lists of coordinates is the Euclidean distance. *)
Lemma paper_main_gordon_distance_list_of_row d (x y : 'rV[RR]_d) :
  paper_main_gordon_distance d (list_of_row x) (list_of_row y) = frobenius (x - y).
Proof.
rewrite /paper_main_gordon_distance finite_sum_seqE sqrtF.
rewrite /frobenius /mxdot big_ord1; congr Num.sqrt; apply: eq_bigr => j _.
by rewrite !list_of_row_nth !mxE powF expr2.
Qed.

Theorem paper_main_gaussian_lipschitz_centered_mgf d F L t :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= t ->
  (\int[gaussian_product_law d]_x
     (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E <=
     (exp (t ^ 2 * L ^ 2 / 2))%:E)%E.
Proof.
move=> HL Hlip Ht.
have [iG ->] := @gaussian_iterated_expectation_gauss_poly d F _ _
  (paper_main_gaussian_lipschitz_continuous d F L HL Hlip)
  (paper_main_gaussian_lipschitz_polynomial_bound d F L HL Hlip).
pose G := fun x : 'rV[RR]_d => (F (list_of_row x) : RR).
have GL (x y : 'rV[RR]_d) : (`|G x - G y| <= L * frobenius (x - y))%R.
  have := Hlip (list_of_row x) (list_of_row y) (list_of_row_length x)
    (list_of_row_length y).
  by rewrite paper_main_gordon_distance_list_of_row RabsF => /RleP.
pose E := (\int[gauss d]_x G x)%R.
have iE := integrable_gauss_concentration GL t.
under eq_integral do rewrite -list_of_row_of_tuple expF.
rewrite -(@integral_gauss_gaussian_product_law d
  (fun y => (expR (t * (G y - E)))%:E) iE).
rewrite expF RdivE !RpowE IZRposE INRE /=.
exact: gauss_concentration GL t.
Qed.

Theorem paper_main_gaussian_lipschitz_mgf_integrable d F L t :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= t ->
  (gaussian_product_law d).-integrable setT
    (fun x => (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E).
Proof.
move=> HL Hlip Ht; apply/integrableP; split.
- have HE : (fun x : d.-tuple (measurableTypeR R) =>
      (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E) =
    (fun x => (expR (t * (paper_main_gaussian_smooth_random d F x -
      gaussian_iterated_expectation d F))%R)%:E).
  { apply: funext => x; rewrite RexpE; reflexivity. }
  rewrite HE; apply: paper_main_centered_exponential_measurable.
  exact: (paper_main_gaussian_lipschitz_random_measurable d F L HL Hlip).
- have HA : (\int[gaussian_product_law d]_x
      `|(exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E| =
    \int[gaussian_product_law d]_x
      (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E)%E.
  { apply: eq_integral => x _; apply: gee0_abs.
    by rewrite lee_fin RexpE expR_ge0. }
  rewrite HA.
  apply: le_lt_trans (paper_main_gaussian_lipschitz_centered_mgf d F L t HL Hlip Ht) _.
  exact: ltry.
Qed.

Theorem paper_main_gaussian_lipschitz_upper_tail d F L u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 < u ->
  (gaussian_product_law d
     [set x | Rle (gaussian_iterated_expectation d F + u) (F (tval x))] <=
   (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> HL Hlip Hu.
apply: paper_main_gaussian_mgf_upper_tail => //.
- exact: (paper_main_gaussian_lipschitz_continuous d F L (Rlt_le _ _ HL) Hlip).
- apply: paper_main_gaussian_lipschitz_centered_mgf => //.
  + exact: Rlt_le.
  + apply Rlt_le, Rdiv_lt_0_compat => //; exact: pow_lt.
Qed.

Lemma paper_main_gaussian_lipschitz_neg d F L :
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (-1 * F xs - (-1 * F ys)) <= L * paper_main_gordon_distance d xs ys.
Proof.
intros Hlip xs ys Hx Hy.
replace (-1 * F xs - (-1 * F ys)) with (- (F xs - F ys)) by ring.
rewrite Rabs_Ropp; exact (Hlip xs ys Hx Hy).
Qed.

Lemma paper_main_gaussian_lipschitz_neg_mean d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_expectation d (fun xs => -1 * F xs) =
    -1 * gaussian_iterated_expectation d F.
Proof.
intros HL Hlip.
destruct (paper_main_gaussian_lipschitz_domain d F L HL Hlip) as [HI _].
exact (proj2 (gaussian_iterated_scale d F (-1) HI)).
Qed.

Theorem paper_main_gaussian_lipschitz_lower_tail d F L u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 < u ->
  (gaussian_product_law d
     [set x | Rle (F (tval x)) (gaussian_iterated_expectation d F - u)] <=
   (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> HL Hlip Hu.
have H := paper_main_gaussian_lipschitz_upper_tail d (fun xs => -1 * F xs) L u
  HL (paper_main_gaussian_lipschitz_neg d F L Hlip) Hu.
rewrite (paper_main_gaussian_lipschitz_neg_mean d F L (Rlt_le _ _ HL) Hlip) in H.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle (F (tval x)) (gaussian_iterated_expectation d F - u)] =
  [set x | Rle (-1 * gaussian_iterated_expectation d F + u) (-1 * F (tval x))].
{ apply/seteqP; split=> x /= Hx; lra. }
rewrite HS; exact H.
Qed.

Theorem paper_main_gaussian_lipschitz_two_sided_tail d F L u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 < u ->
  (gaussian_product_law d
     [set x | Rle u (Rabs (F (tval x) - gaussian_iterated_expectation d F))] <=
   (2 * exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> HL Hlip Hu.
have Hc := paper_main_gaussian_lipschitz_continuous d F L (Rlt_le _ _ HL) Hlip.
have Hcn : finite_joint_continuous d (fun xs => -1 * F xs)
  by apply finite_joint_continuous_scale.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (F (tval x) - gaussian_iterated_expectation d F))] =
  [set x | Rle (gaussian_iterated_expectation d F + u) (F (tval x))] `|`
  [set x | Rle (-1 * gaussian_iterated_expectation d F + u) (-1 * F (tval x))].
{ apply/seteqP; split=> x /=.
  - unfold Rabs; destruct Rcase_abs => Hx; [right|left]; lra.
  - move=> [Hx|Hx]; unfold Rabs; destruct Rcase_abs; lra. }
rewrite HS.
have H1 := paper_main_gaussian_lipschitz_upper_tail d F L u HL Hlip Hu.
have H2 := paper_main_gaussian_lipschitz_lower_tail d F L u HL Hlip Hu.
have HS2 : [set x : d.-tuple (measurableTypeR R) |
    Rle (F (tval x)) (gaussian_iterated_expectation d F - u)] =
  [set x | Rle (-1 * gaussian_iterated_expectation d F + u) (-1 * F (tval x))].
{ apply/seteqP; split=> x /= Hx; lra. }
rewrite HS2 in H2.
eapply le_trans; first exact: (measureU2 _
  (paper_main_gaussian_smooth_ge_measurable d F _ Hc)
  (paper_main_gaussian_smooth_ge_measurable d (fun xs => -1 * F xs) _ Hcn)).
have H := leeD H1 H2.
move: H; rewrite -EFinD.
have HE (z : R) : (z + z)%R = Rmult 2 z.
{ change (z + z = 2 * z); lra. }
rewrite HE; trivial.
Qed.
