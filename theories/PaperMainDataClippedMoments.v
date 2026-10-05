(* Gaussian second moments of raw and clipped data-feature soft scores
   (G11, checkpoint B, law part). D = N * d, d = S n, and S(xs) is the sum of
   the squares of the D coordinates.
   - The sum of squares has iterated expectation D (existing) and second
     moment D^2 + 2 D (paper_main_gaussian_sum_squares_second_moment).
   - A jointly continuous F with |F xs| <= c (S(xs) + D) + C is integrable
     for gaussian_product_law D together with F * F. Both integrals are the
     iterated expectations, and E (F * F) <= 2 c^2 (4 D^2 + 2 D) + 2 C^2
     (paper_main_data_growth_law). The integrands have the form of the
     premises of paper_main_gaussian_clipping_mean_loss, and the iterated
     expectation of F * F is stated with the Stdlib product in both places.
   - The raw soft minimax and the clipped soft minimax of admissible
     families satisfy this with c = k / sqrt d and the entropy C. The
     clipped one also has the uniform bound.
   Continuity of the raw scores is proved directly from coordinate
   products. No moment, regularity or law statement is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval boolp.
From mathcomp Require Import classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums
  GaussianDefinitions GaussianExpectation GaussianIntegration
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity GaussianFiniteSums GaussianProductDefinitions
  GaussianProduct GaussianCoordinateMarginals GaussianProbabilityProductDefinitions
  MaximumRadiusRegularity MaximumRadiusComparison PaperMainGaussianNorm
  PaperMainGaussianSmoothLaw PaperMainGordonContinuity PaperMainGordonLipschitz
  PaperMainGaussianLipschitzClip MatrixDefinitions OperatorDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainSymmetricBilinear
  PaperMainMatrixTransport PaperMainMatrixDuality PaperMainDataFeatureMoments
  PaperMainDataClippedScore PaperMainDataClipped PaperMainDataClippedSoft
  PaperMainDataClippedGrowth.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Import ListNotations.
Open Scope R_scope.

(* 1. The second moment of the sum of squares. *)
Lemma pmdcm_squares_bound d :
  finite_polynomial_bound d (INR d) 2 gaussian_sum_squares.
Proof.
split; [exact: pos_INR|] => xs Hxs.
rewrite (Rabs_pos_eq _ (maximum_radius_squares_nonnegative xs)) -Hxs.
exact: maximum_radius_squares_polynomial.
Qed.

Lemma pmdcm_squares_sq_integrable d :
  gaussian_iterated_integrable d
    (fun xs => gaussian_sum_squares xs * gaussian_sum_squares xs).
Proof.
apply: (gaussian_iterated_polynomial_integrable d _ (INR d * INR d) (2 + 2)).
- apply: finite_joint_continuous_mult; exact: maximum_radius_squares_continuous.
- by apply: finite_polynomial_bound_mult; exact: pmdcm_squares_bound.
Qed.

Theorem paper_main_gaussian_sum_squares_second_moment d :
  gaussian_iterated_expectation d
    (fun xs => gaussian_sum_squares xs * gaussian_sum_squares xs) =
  INR d * INR d + 2 * INR d.
Proof.
elim: d => [|d IH]; first by rewrite /=; ring.
change (gaussian_expectation (fun x => gaussian_iterated_expectation d
  (fun xs => (x * x + gaussian_sum_squares xs) * (x * x + gaussian_sum_squares xs))) =
  INR (S d) * INR (S d) + 2 * INR (S d)).
have HS := maximum_radius_squares_integrable d.
have HSS := pmdcm_squares_sq_integrable d.
have HE : forall x, gaussian_iterated_expectation d
    (fun xs => (x * x + gaussian_sum_squares xs) * (x * x + gaussian_sum_squares xs)) =
    x ^ 4 + (2 * INR d * x ^ 2 + (INR d * INR d + 2 * INR d)).
  move=> x.
  have [HC HCE] := gaussian_iterated_constant d (x * x * (x * x)).
  have [HZ HZE] := gaussian_iterated_scale d gaussian_sum_squares (2 * (x * x)) HS.
  have [HA HAE] := gaussian_iterated_add d _ _ HZ HSS.
  have [HB HBE] := gaussian_iterated_add d _ _ HC HA.
  have Eext : gaussian_iterated_expectation d
      (fun xs => (x * x + gaussian_sum_squares xs) * (x * x + gaussian_sum_squares xs)) =
    gaussian_iterated_expectation d
      (fun xs => x * x * (x * x) + (2 * (x * x) * gaussian_sum_squares xs +
        gaussian_sum_squares xs * gaussian_sum_squares xs)).
    by apply: gaussian_iterated_expectation_ext => xs _; ring.
  rewrite Eext HBE HCE HAE HZE IH gaussian_sum_squares_expectation; ring.
have Hfun : (fun x => gaussian_iterated_expectation d
    (fun xs => (x * x + gaussian_sum_squares xs) * (x * x + gaussian_sum_squares xs))) =
    (fun x => x ^ 4 + (2 * INR d * x ^ 2 + (INR d * INR d + 2 * INR d))).
  by apply: functional_extensionality => x; rewrite HE.
rewrite Hfun.
have I4 := proj1 (proj2 (gaussian_power_moments 4)).
have I2 := proj1 (proj2 (gaussian_power_moments 2)).
have I2s := gaussian_integral_exists_scale _ (2 * INR d) I2.
have IC := gaussian_integral_exists_constant (INR d * INR d + 2 * INR d).
have I2C := gaussian_integral_exists_add _ _ I2s IC.
rewrite (gaussian_expectation_add _ _ I4 I2C) (gaussian_expectation_add _ _ I2s IC).
rewrite (gaussian_expectation_scale _ _ I2) gaussian_expectation_of_constant.
rewrite (proj2 (proj2 (proj2 gaussian_standard_moments))).
rewrite (proj1 (proj2 (proj2 gaussian_standard_moments))) S_INR; ring.
Qed.

(* 2. The quadratic majorant 2 (c (S + D))^2 + 2 C^2. *)
Definition pmdcm_majorant (D : nat) (c C : R) (xs : list R) : R :=
  2 * (c * (gaussian_sum_squares xs + INR D)) * (c * (gaussian_sum_squares xs + INR D)) +
  2 * (C * C).

Lemma pmdcm_majorant_law D c C :
  gaussian_iterated_integrable D (pmdcm_majorant D c C) /\
  gaussian_iterated_expectation D (pmdcm_majorant D c C) =
    2 * c ^ 2 * (4 * INR D ^ 2 + 2 * INR D) + 2 * C ^ 2.
Proof.
have HS := maximum_radius_squares_integrable D.
have HSS := pmdcm_squares_sq_integrable D.
have [H1 E1] := gaussian_iterated_scale D _ (2 * c ^ 2) HSS.
have [H2 E2] := gaussian_iterated_scale D gaussian_sum_squares (4 * c ^ 2 * INR D) HS.
have [H3 E3] := gaussian_iterated_constant D (2 * c ^ 2 * INR D ^ 2 + 2 * C ^ 2).
have [H23 E23] := gaussian_iterated_add D _ _ H2 H3.
have [H E] := gaussian_iterated_add D _ _ H1 H23.
have Ext : forall xs, length xs = D ->
    2 * c ^ 2 * (gaussian_sum_squares xs * gaussian_sum_squares xs) +
    (4 * c ^ 2 * INR D * gaussian_sum_squares xs + (2 * c ^ 2 * INR D ^ 2 + 2 * C ^ 2)) =
    pmdcm_majorant D c C xs.
  by move=> xs _; rewrite /pmdcm_majorant; ring.
split; first exact: (gaussian_iterated_integrable_ext D _ _ Ext H).
rewrite -(gaussian_iterated_expectation_ext D _ _ Ext) E E23 E1 E2 E3.
rewrite paper_main_gaussian_sum_squares_second_moment gaussian_sum_squares_expectation.
ring.
Qed.

(* 3. From pointwise growth to the square law. *)
Definition paper_main_data_square_law D (F : list R -> R) (V : R) : Prop :=
  (gaussian_product_law D).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law D]_x (F (tval x))%:E =
    (gaussian_iterated_expectation D F)%:E)%E /\
  (gaussian_product_law D).-integrable setT (fun x => (F (tval x) * F (tval x))%:E) /\
  (\int[gaussian_product_law D]_x (F (tval x) * F (tval x))%:E =
    (gaussian_iterated_expectation D (fun xs => Rmult (F xs) (F xs)))%:E)%E /\
  gaussian_iterated_expectation D (fun xs => F xs * F xs) <= V.

Lemma pmdcm_growth_polynomial D c C (F : list R -> R) :
  0 <= c -> 0 <= C ->
  (forall xs, Rabs (F xs) <=
    c * (finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 D) + INR D) + C) ->
  finite_polynomial_bound D (2 * c * INR D + C) 2 F.
Proof.
move=> Hc HC HF; have HD := pos_INR D.
split; first by have := Rmult_le_pos _ _ Hc HD; lra.
move=> xs Hxs.
have HW := gaussian_coordinate_product_weight_at_least_one 2 xs.
have HSq := maximum_radius_squares_polynomial xs; rewrite Hxs in HSq.
have H := HF xs; rewrite (paper_main_gaussian_squares_coordinates D xs Hxs) in H.
move: HW HSq H; set W := gaussian_coordinate_product_weight 2 xs.
set S := gaussian_sum_squares xs => HW HSq H.
have H1 : c * S <= c * (INR D * W) by apply: Rmult_le_compat_l.
have H2 : c * INR D <= c * INR D * W.
  by have := Rmult_le_pos _ _ Hc HD; nra.
have H3 : C <= C * W by nra.
nra.
Qed.

Theorem paper_main_data_growth_law D c C (F : list R -> R) :
  0 <= c -> 0 <= C -> finite_joint_continuous D F ->
  (forall xs, Rabs (F xs) <=
    c * (finite_sum (fun l => List.nth l xs 0 ^ 2) (List.seq 0 D) + INR D) + C) ->
  paper_main_data_square_law D F (2 * c ^ 2 * (4 * INR D ^ 2 + 2 * INR D) + 2 * C ^ 2).
Proof.
move=> Hc HC Hcont HF.
have Hb := pmdcm_growth_polynomial D c C F Hc HC HF.
have Hb2 := finite_polynomial_bound_mult _ _ _ _ _ _ _ Hb Hb.
have Hcont2 := finite_joint_continuous_mult _ _ _ Hcont Hcont.
have [I1 E1] := paper_main_gaussian_law_transport D F _ _ Hcont Hb.
have [I2 E2] := paper_main_gaussian_law_transport D (fun xs => F xs * F xs) _ _ Hcont2 Hb2.
split; first exact: I1.
split; first exact: E1.
split; first exact: I2.
split; first exact: E2.
have IFF := gaussian_iterated_polynomial_integrable D _ _ _ Hcont2 Hb2.
have [IM EM] := pmdcm_majorant_law D c C.
rewrite -EM.
apply: gaussian_iterated_monotone => // xs Hxs.
have H := HF xs; rewrite (paper_main_gaussian_squares_coordinates D xs Hxs) in H.
have HS0 := maximum_radius_squares_nonnegative xs.
have HT : 0 <= c * (gaussian_sum_squares xs + INR D).
  by apply: Rmult_le_pos => //; have := pos_INR D; lra.
have := paper_main_data_square_bound (F xs) _ _ HT HC H.
by rewrite /pmdcm_majorant; lra.
Qed.

(* 4. Joint continuity of the raw scores. *)
Lemma pmdcm_quad_finite n (f : nat -> R) (B : 'M[R]_(S n)) :
  ((paper_main_symmetric_column n f)^T *m B *m paper_main_symmetric_column n f)%R ord0 ord0 =
  finite_sum (fun a => finite_sum (fun b => f a * B (inord a) (inord b) * f b)
    (List.seq 0 (S n))) (List.seq 0 (S n)).
Proof.
rewrite -paper_main_quadratic_formE /paper_main_quadratic_form.
rewrite paper_main_finite_sum_public; apply: eq_bigr => i _.
rewrite paper_main_finite_sum_public; apply: eq_bigr => j _.
by rewrite !mxE !inord_val.
Qed.

Lemma pmdcm_index_lt N n i a :
  In i (List.seq 0 N) -> In a (List.seq 0 (S n)) -> ((i * S n + a)%N < (N * S n)%N)%coq_nat.
Proof.
move=> /in_seq [_ Hi] /in_seq [_ Ha].
apply/ssrnat.ltP; apply: pmdcl_index; apply/ssrnat.ltP; lia.
Qed.

Lemma pmdcm_raw_pairing_continuous n N (B : 'M[R]_(S n)) i :
  In i (List.seq 0 N) ->
  finite_joint_continuous (N * S n) (fun xs =>
    paper_main_pairing (paper_main_data_feature n (fun j => List.nth (i * S n + j)%N xs 0)) B).
Proof.
move=> Hi.
apply: (finite_joint_continuous_ext _ (fun xs => / sqrt (INR (S n)) *
  (finite_sum (fun a => finite_sum (fun b => List.nth (i * S n + a)%N xs 0 *
    B (inord a) (inord b) * List.nth (i * S n + b)%N xs 0) (List.seq 0 (S n)))
    (List.seq 0 (S n)) - paper_main_trace B))).
  by move=> xs _; rewrite pmdcg_pairing_eq pmdcm_quad_finite.
apply: finite_joint_continuous_scale.
apply: finite_joint_continuous_minus; last exact: finite_joint_continuous_constant.
apply: finite_joint_continuous_sum => a Ha.
apply: finite_joint_continuous_sum => b Hb.
apply: finite_joint_continuous_mult; last exact: finite_joint_continuous_nth (pmdcm_index_lt _ _ _ _ Hi Hb).
apply: (finite_joint_continuous_ext _ (fun xs => B (inord a) (inord b) * List.nth (i * S n + a)%N xs 0)).
  by move=> xs _; rewrite Rmult_comm.
apply: finite_joint_continuous_scale.
exact: finite_joint_continuous_nth (pmdcm_index_lt _ _ _ _ Hi Ha).
Qed.

Theorem paper_main_data_raw_score_continuous n N (B : 'M[R]_(S n)) (y : nat -> R) :
  finite_joint_continuous (N * S n) (paper_main_data_raw_score n N B y).
Proof.
rewrite /paper_main_data_raw_score.
apply: (finite_joint_continuous_sum (N * S n) (List.seq 0 N) (fun i xs => y i *
  paper_main_pairing (paper_main_data_feature n (fun j => List.nth (i * S n + j)%N xs 0)) B)).
move=> i Hi; apply: finite_joint_continuous_scale.
exact: pmdcm_raw_pairing_continuous.
Qed.

(* 5. The raw and the clipped soft minimax. *)
Definition paper_main_data_raw_soft n N beta gamma (Bf : nat -> nat -> 'M[R]_(S n))
    (yf : nat -> nat -> nat -> R) (Y Q : list nat) (xs : list R) : R :=
  soft_minimax beta gamma (paper_main_data_raw_family n N Bf yf xs) Y Q.

Definition paper_main_data_clipped_soft U n N beta gamma (Bf : nat -> nat -> 'M[R]_(S n))
    (yf : nat -> nat -> nat -> R) (Y Q : list nat) (xs : list R) : R :=
  soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf xs) Y Q.

Theorem paper_main_data_raw_soft_continuous n N beta gamma Bf yf Y Q :
  Y <> [] -> Q <> [] ->
  finite_joint_continuous (N * S n) (paper_main_data_raw_soft n N beta gamma Bf yf Y Q).
Proof.
move=> HY HQ.
apply: (paper_main_gordon_soft_minimax_continuous (N * S n) beta gamma
  (paper_main_data_raw_family n N Bf yf)) => // z q _ _.
exact: paper_main_data_raw_score_continuous.
Qed.

Theorem paper_main_data_clipped_soft_continuous U n N k beta gamma Bf yf Y Q :
  0 <= U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  finite_joint_continuous (N * S n) (paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q).
Proof.
move=> HU Hk Hb Hg HY HQ Had.
apply: (paper_main_gaussian_lipschitz_continuous _ _ (2 * k * U)).
  by apply: Rmult_le_pos => //; lra.
move=> xs ys _ _.
exact: paper_main_data_clipped_soft_lipschitz.
Qed.

Theorem paper_main_data_raw_soft_square_law n N k beta gamma Bf yf Y Q :
  0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  paper_main_data_square_law (N * S n) (paper_main_data_raw_soft n N beta gamma Bf yf Y Q)
    (2 * (k / sqrt (INR (S n))) ^ 2 *
      (4 * INR (N * S n) ^ 2 + 2 * INR (N * S n)) +
     2 * paper_main_data_soft_entropy beta gamma Y Q ^ 2).
Proof.
move=> Hk Hb Hg HY HQ Had.
have Hsp : 0 < sqrt (INR (S n)) by apply: sqrt_lt_R0; apply: lt_0_INR; lia.
apply: paper_main_data_growth_law.
- by apply: Rmult_le_pos => //; apply: Rlt_le; exact: Rinv_0_lt_compat.
- exact: paper_main_data_soft_entropy_ge0.
- exact: paper_main_data_raw_soft_continuous.
- by move=> xs; exact: paper_main_data_raw_soft_growth.
Qed.

Theorem paper_main_data_clipped_soft_square_law U n N k beta gamma Bf yf Y Q :
  0 <= U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  paper_main_data_square_law (N * S n)
    (paper_main_data_clipped_soft U n N beta gamma Bf yf Y Q)
    (2 * (k / sqrt (INR (S n))) ^ 2 *
      (4 * INR (N * S n) ^ 2 + 2 * INR (N * S n)) +
     2 * paper_main_data_soft_entropy beta gamma Y Q ^ 2).
Proof.
move=> HU Hk Hb Hg HY HQ Had.
have Hsp : 0 < sqrt (INR (S n)) by apply: sqrt_lt_R0; apply: lt_0_INR; lia.
apply: paper_main_data_growth_law.
- by apply: Rmult_le_pos => //; apply: Rlt_le; exact: Rinv_0_lt_compat.
- exact: paper_main_data_soft_entropy_ge0.
- exact: (paper_main_data_clipped_soft_continuous U n N k beta gamma Bf yf Y Q
    HU Hk Hb Hg HY HQ Had).
- by move=> xs; exact: paper_main_data_clipped_soft_growth.
Qed.
