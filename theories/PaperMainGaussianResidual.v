(* Residual tails for one Gaussian data point. For a list xs with column
   x = paper_main_symmetric_column xs, the feature is
     W(xs) = (x x^T - I) / sqrt d   (paper_main_gaussian_residual_feature),
   the one-point form of paper_main_head_feature. Then
     <W(xs), P> = (x^T P x - trace P) / sqrt d,
   so for d = S n the residual event {R <= |<W, P>|} is the quadratic event
   {R sqrt d <= |x^T P x - trace P|}. For symmetric P with
   paper_main_pairing P P = 1, 0 <= kappa and the bilinear bound
   paper_main_cone_opnorm_le P (kappa / sqrt d), the Gaussian Hanson-Wright
   tail of PaperMainGaussianQuadraticTail with u = R sqrt d and
   b = kappa / sqrt d gives, under gaussian_product_law d and for R > 0,
     P[R <= |<W, P>|] <= 2 exp (- d R^2 / (4 + 4 kappa R)).
   The events are measurable. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature
  PaperMainConeConditionOperator PaperMainGaussianSmoothTail
  PaperMainSymmetricDiagonalizationBridge PaperMainGaussianQuadraticTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition paper_main_gaussian_residual_feature {d : nat} (xs : list R) : 'M[R]_d :=
  (Num.sqrt d%:R)^-1 *:
    (paper_main_symmetric_column xs *m (paper_main_symmetric_column xs)^T - 1%:M).

Lemma paper_main_gaussian_residual_pairing d (xs : list R) (P : 'M[R]_d) :
  paper_main_pairing (paper_main_gaussian_residual_feature xs) P =
  (Num.sqrt d%:R)^-1 * paper_main_gaussian_quadratic_statistic P xs.
Proof.
rewrite /paper_main_gaussian_residual_feature pmh_pairingZl pmh_pairingBl pmh_pairing_id.
by rewrite paper_main_pairingC paper_main_pairing_outer.
Qed.

Lemma paper_main_gaussian_residual_continuous d (P : 'M[R]_d) :
  paper_main_symmetric P ->
  finite_joint_continuous d
    (fun xs => paper_main_pairing (paper_main_gaussian_residual_feature xs) P).
Proof.
move=> HP.
apply: (finite_joint_continuous_ext d
  (fun xs => Rmult ((Num.sqrt d%:R)^-1) (paper_main_gaussian_quadratic_statistic P xs))).
  by move=> xs _; rewrite paper_main_gaussian_residual_pairing.
apply: finite_joint_continuous_scale.
exact: paper_main_gaussian_quadratic_continuous.
Qed.

Theorem paper_main_gaussian_residual_measurable d (P : 'M[R]_d) (r : R) :
  paper_main_symmetric P ->
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle r (Rabs (paper_main_pairing (paper_main_gaussian_residual_feature (tval x)) P))].
Proof.
move=> HP.
exact: (paper_main_gaussian_smooth_ge_measurable d _ r
  (finite_joint_continuous_abs d _ (paper_main_gaussian_residual_continuous d P HP))).
Qed.

(* The sqrt d transport of the event. *)

Lemma paper_main_gaussian_residual_eventE n (P : 'M[R]_(S n)) (r : R) :
  [set x : (S n).-tuple (measurableTypeR R) |
    Rle r (Rabs (paper_main_pairing (paper_main_gaussian_residual_feature (tval x)) P))] =
  [set x | Rle (r * Num.sqrt (S n)%:R)
    (Rabs (paper_main_gaussian_quadratic_statistic P (tval x)))].
Proof.
have Hs : 0 < Num.sqrt ((S n)%:R : R) by rewrite sqrtr_gt0 ltr0n.
apply/seteqP; split=> x /=; rewrite paper_main_gaussian_residual_pairing => /RleP H;
  apply/RleP; move: H; rewrite !RabsE normrM ger0_norm ?invr_ge0 ?sqrtr_ge0 //.
- by rewrite mulrC -(ler_pdivlMr _ _ Hs).
- by rewrite mulrC (ler_pdivlMr _ _ Hs).
Qed.

(* The tail of one residual. *)

Theorem paper_main_gaussian_residual_tail n (P : 'M[R]_(S n)) (kappa r : R) :
  paper_main_symmetric P -> paper_main_pairing P P = 1 -> 0 <= kappa ->
  paper_main_cone_opnorm_le P (kappa / Num.sqrt (S n)%:R) -> 0 < r ->
  (gaussian_product_law (S n)
    [set x | Rle r (Rabs (paper_main_pairing (paper_main_gaussian_residual_feature (tval x)) P))]
    <= (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
      (Rplus 4 (Rmult (Rmult 4 kappa) r)))))%:E)%E.
Proof.
move=> HP HP1 Hk HB Hr.
set s := Num.sqrt ((S n)%:R : R).
have Hs : 0 < s by rewrite sqrtr_gt0 ltr0n.
have Hs2 : s * s = (S n)%:R by rewrite -expr2 sqr_sqrtr // ler0n.
have Hb : 0 <= kappa / s by rewrite divr_ge0 // ltW.
have Hu : 0 < r * s by rewrite mulr_gt0.
have Hs0' : s != 0 by rewrite gt_eqF.
have Hbu : kappa / s * (r * s) = kappa * r.
  by rewrite mulrCA -[kappa / s * s]mulrA mulVf // mulr1 mulrC.
have Hden : (0 < paper_main_pairing P P + kappa / s * (r * s))%R.
  by rewrite HP1 Hbu; apply: ltr_wpDr; [rewrite mulr_ge0 // ltW | exact: ltr01].
have H := paper_main_gaussian_quadratic_tail (S n) P (kappa / s) (r * s) HP
  (elimT RleP Hb) HB (elimT RltP Hu) (elimT RltP Hden).
rewrite paper_main_gaussian_residual_eventE.
apply: (le_trans H).
rewrite lee_fin HP1; apply/RleP; right.
congr (Rmult 2 (exp _)).
have Hbu' : Rmult (kappa / s) (r * s) = Rmult kappa r := Hbu.
have Hu2 : Rmult (r * s) (r * s) = Rmult (INR (S n)) (Rmult r r).
  rewrite INRE -Hs2.
  by change (Rmult (Rmult r s) (Rmult r s) = Rmult (Rmult s s) (Rmult r r)); ring.
rewrite Rmult_assoc Hbu'.
replace (pow (Rmult r s) 2) with (Rmult (INR (S n)) (pow r 2)).
  have E : Rplus (Rmult 4 1) (Rmult 4 (Rmult kappa r)) =
      Rplus 4 (Rmult (Rmult 4 kappa) r) by ring.
  by rewrite E.
by simpl; rewrite !Rmult_1_r; symmetry; exact: Hu2.
Qed.
