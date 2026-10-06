(* Actual isotropic symmetric Gaussian PSD widths. The sphere support is
   signed; its positive part, rather than the support itself, equals the
   projection norm. All expectations below are of the constructed law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gaussian.LipschitzApproximationLaw
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.CoordinateWeightDefinitions Gaussian.CoordinatePolynomialContinuity
  Gaussian.CoordinateWeights Gaussian.IteratedExpectationDefinitions
  Gaussian.IteratedExpectation Gaussian.CovarianceDefinitions
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Geometry.HeadFrobenius
  Geometry.HeadWidth Geometry.HeadWidthLipschitz Cone.Projection
  Cone.ProjectionSupport Gordon.Lipschitz Gaussian.LipschitzClip
  Gaussian.LipschitzApproximation Gaussian.LipschitzVariance
  Gaussian.WidthVariance Gaussian.SymmetricLaw Gaussian.SymmetricLawPublic
  Gaussian.FeatureCoordinates.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_psd_projection_norm n xs : R :=
  paper_main_frobenius (paper_main_psd_projection (S n)
    (paper_main_public_symmetric_gaussian n xs)).
Definition paper_main_gaussian_psd_support n xs : R :=
  paper_main_head_support (paper_main_public_symmetric_gaussian n xs)
    (@paper_main_psd_sphere (S n)).
Definition paper_main_gaussian_psd_width n : R :=
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_gaussian_psd_support n).

Lemma paper_main_psd_projection_norm_real_lipschitz d (A B : 'M[R]_d) :
  Rabs (paper_main_frobenius (paper_main_psd_projection d A) -
        paper_main_frobenius (paper_main_psd_projection d B)) <=
    1 * paper_main_frobenius (A - B)%R.
Proof.
have H := paper_main_psd_projection_norm_lipschitz d A B.
rewrite -RabsE in H; move/RleP: H => H.
change (Rabs (paper_main_frobenius (paper_main_psd_projection d A) -
  paper_main_frobenius (paper_main_psd_projection d B)) <=
  paper_main_frobenius (A-B)%R) in H; lra.
Qed.

Theorem paper_main_gaussian_psd_projection_lipschitz n xs ys :
  List.length xs = paper_main_symmetric_dimension n ->
  List.length ys = paper_main_symmetric_dimension n ->
  Rabs (paper_main_gaussian_psd_projection_norm n xs -
    paper_main_gaussian_psd_projection_norm n ys) <=
    1 * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
apply: (paper_main_public_symmetric_lipschitz_transfer n
  (fun A => paper_main_frobenius (paper_main_psd_projection (S n) A)) 1).
move=> A B _ _; exact: paper_main_psd_projection_norm_real_lipschitz.
Qed.

Theorem paper_main_gaussian_psd_support_lipschitz n xs ys :
  List.length xs = paper_main_symmetric_dimension n ->
  List.length ys = paper_main_symmetric_dimension n ->
  Rabs (paper_main_gaussian_psd_support n xs -
    paper_main_gaussian_psd_support n ys) <=
    1 * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
apply: (paper_main_public_symmetric_lipschitz_transfer n
  (fun A => paper_main_head_support A (@paper_main_psd_sphere (S n))) 1).
move=> A B _ _.
have Hne : (@paper_main_psd_sphere (S n)) !=set0.
  exists (((Num.sqrt (S n)%:R)^-1 *: (1%:M : 'M[R]_(S n)))%R).
  exact: pmcs_sphere_nonempty.
have H := paper_main_head_support_lipschitz (S n) A B
  (@paper_main_psd_sphere (S n)) Hne (fun S H => proj2 H).
rewrite -RabsE in H; move/RleP: H => H.
change (Rabs (paper_main_head_support A (@paper_main_psd_sphere (S n)) -
  paper_main_head_support B (@paper_main_psd_sphere (S n))) <=
  paper_main_frobenius (A-B)%R) in H; lra.
Qed.

Theorem paper_main_gaussian_psd_projection_second_moment n :
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_gaussian_psd_projection_norm n xs *
      paper_main_gaussian_psd_projection_norm n xs) =
  INR (paper_main_symmetric_dimension n) / 2.
Proof.
pose D := paper_main_symmetric_dimension n.
pose F := paper_main_gaussian_psd_projection_norm n.
pose G := fun xs => paper_main_frobenius (paper_main_psd_projection (S n)
  (- paper_main_public_symmetric_gaussian n xs)%R).
have HF := paper_main_gaussian_psd_projection_lipschitz n.
have HG : forall xs ys, List.length xs = D -> List.length ys = D ->
  Rabs (G xs - G ys) <= 1 * paper_main_gordon_distance D xs ys.
  apply: (paper_main_public_symmetric_neg_lipschitz_transfer n
    (fun A => paper_main_frobenius (paper_main_psd_projection (S n) A)) 1).
  move=> A B _ _; exact: paper_main_psd_projection_norm_real_lipschitz.
have HF2 := paper_main_gaussian_lipschitz_square_domain D F 1 Rle_0_1 HF.
have HG2 := paper_main_gaussian_lipschitz_square_domain D G 1 Rle_0_1 HG.
have HC := paper_main_gaussian_lipschitz_continuous D F 1 Rle_0_1 HF.
have HB := paper_main_gaussian_lipschitz_polynomial_bound D F 1 Rle_0_1 HF.
have Hsym := paper_main_public_symmetric_gaussian_sign_symmetry n
  (fun A => paper_main_frobenius (paper_main_psd_projection (S n) A) *
    paper_main_frobenius (paper_main_psd_projection (S n) A)) _ 4
  (finite_joint_continuous_mult D F F HC HC)
  (finite_polynomial_bound_mult D _ _ 2 2 F F HB HB).
change (gaussian_iterated_expectation D (fun xs => G xs * G xs) =
  gaussian_iterated_expectation D (fun xs => F xs * F xs)) in Hsym.
have HE : gaussian_iterated_expectation D
  (fun xs => paper_main_frobenius (paper_main_public_symmetric_gaussian n xs)^2) =
  gaussian_iterated_expectation D (fun xs => F xs * F xs + G xs * G xs).
  apply: gaussian_iterated_expectation_ext => xs _.
  have HZ := paper_main_public_symmetric_gaussian_symmetric n xs.
  have H := paper_main_psd_moreau_frobenius (S n) _ HZ.
  rewrite -(paper_main_psd_projection_opp (S n) _ HZ) !expr2 in H.
  change (paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) *
    paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) =
    F xs * F xs + G xs * G xs) in H; nra.
have [_ [HM _]] := paper_main_public_symmetric_gaussian_moments n.
rewrite (proj2 (gaussian_iterated_add D _ _ HF2 HG2)) Hsym in HE.
change (gaussian_iterated_expectation D
  (fun xs => paper_main_frobenius (paper_main_public_symmetric_gaussian n xs)^2) =
  INR D) in HM.
change (gaussian_iterated_expectation D (fun xs => F xs * F xs) = INR D / 2).
lra.
Qed.

Theorem paper_main_gaussian_psd_support_positive_part n xs :
  Rmax (paper_main_gaussian_psd_support n xs) 0 =
  paper_main_gaussian_psd_projection_norm n xs.
Proof.
have H := paper_main_psd_sphere_support_max (S n)
  (paper_main_public_symmetric_gaussian n xs) (ltn0Sn n)
  (paper_main_public_symmetric_gaussian_symmetric n xs).
change (Num.max (paper_main_gaussian_psd_support n xs) 0 =
  paper_main_gaussian_psd_projection_norm n xs) in H.
destruct (Rle_dec (paper_main_gaussian_psd_support n xs) 0) as [Ha|Ha].
- rewrite (Rmax_right _ _ Ha).
  have Hb : (paper_main_gaussian_psd_support n xs <= 0)%R by apply/RleP.
  by rewrite max_r in H.
- have Ha' : 0 <= paper_main_gaussian_psd_support n xs by lra.
  rewrite (Rmax_left _ _ Ha').
  have Hb : (0 <= paper_main_gaussian_psd_support n xs)%R by apply/RleP.
  by rewrite max_l in H.
Qed.

Theorem paper_main_gaussian_psd_positive_square n :
  paper_main_gaussian_positive_square (paper_main_symmetric_dimension n)
    (paper_main_gaussian_psd_support n) = INR (paper_main_symmetric_dimension n)/2.
Proof.
rewrite /paper_main_gaussian_positive_square
  -(paper_main_gaussian_psd_projection_second_moment n).
apply: gaussian_iterated_expectation_ext => xs _.
by rewrite paper_main_gaussian_psd_support_positive_part.
Qed.

Lemma paper_main_psd_support_real_lipschitz n (A B : 'M[R]_(S n)) :
  Rabs (paper_main_head_support A (@paper_main_psd_sphere (S n)) -
    paper_main_head_support B (@paper_main_psd_sphere (S n))) <=
  1 * paper_main_frobenius (A-B)%R.
Proof.
have Hne : (@paper_main_psd_sphere (S n)) !=set0.
  exists (((Num.sqrt (S n)%:R)^-1 *: (1%:M : 'M[R]_(S n)))%R).
  exact: pmcs_sphere_nonempty.
have H := paper_main_head_support_lipschitz (S n) A B
  (@paper_main_psd_sphere (S n)) Hne (fun S H => proj2 H).
rewrite -RabsE in H; move/RleP: H => H.
change (Rabs (paper_main_head_support A (@paper_main_psd_sphere (S n)) -
  paper_main_head_support B (@paper_main_psd_sphere (S n))) <=
  paper_main_frobenius (A-B)%R) in H; lra.
Qed.

Theorem paper_main_gaussian_psd_width_nonnegative n :
  0 <= paper_main_gaussian_psd_width n.
Proof.
pose D := paper_main_symmetric_dimension n.
pose F := paper_main_gaussian_psd_support n.
pose G := fun xs => paper_main_head_support
  (- paper_main_public_symmetric_gaussian n xs)%R (@paper_main_psd_sphere (S n)).
have HPhi : forall A B : 'M[R]_(S n), paper_main_symmetric A -> paper_main_symmetric B ->
  Rabs (paper_main_head_support A (@paper_main_psd_sphere (S n)) -
    paper_main_head_support B (@paper_main_psd_sphere (S n))) <=
  1 * paper_main_frobenius (A-B)%R.
  move=> A B _ _; exact: paper_main_psd_support_real_lipschitz.
have HF := paper_main_gaussian_psd_support_lipschitz n.
have HG := paper_main_public_symmetric_neg_lipschitz_transfer n
  (fun A => paper_main_head_support A (@paper_main_psd_sphere (S n))) 1 HPhi.
have [IF _] := paper_main_gaussian_lipschitz_domain D F 1 Rle_0_1 HF.
have [IG _] := paper_main_gaussian_lipschitz_domain D G 1 Rle_0_1 HG.
have Hsym := paper_main_public_symmetric_lipschitz_sign_symmetry n
  (fun A => paper_main_head_support A (@paper_main_psd_sphere (S n))) 1 Rle_0_1 HPhi.
change (gaussian_iterated_expectation D G = gaussian_iterated_expectation D F) in Hsym.
have [IS ES] := gaussian_iterated_add D F G IF IG.
have Hnon : forall xs, List.length xs = D -> 0 <= F xs + G xs.
  move=> xs _.
  pose Z := paper_main_public_symmetric_gaussian n xs.
  pose S0 : 'M[R]_(S n) := (((Num.sqrt (S n)%:R)^-1 *: (1%:M : 'M[R]_(S n)))%R).
  have HS : paper_main_psd_sphere S0 by exact: pmcs_sphere_nonempty.
  have H1 := pmh_support_ge (S n) Z (@paper_main_psd_sphere (S n)) S0
    (fun S H => proj2 H) HS.
  have H2 := pmh_support_ge (S n) (-Z)%R (@paper_main_psd_sphere (S n)) S0
    (fun S H => proj2 H) HS.
  rewrite pmh_pairingNl in H2.
  move/RleP: H1 => H1; move/RleP: H2 => H2.
  change (paper_main_pairing Z S0 <= F xs) in H1.
  change (-paper_main_pairing Z S0 <= G xs) in H2; lra.
have H := gaussian_iterated_nonnegative D _ IS Hnon.
rewrite ES Hsym in H.
change (0 <= gaussian_iterated_expectation D F); lra.
Qed.

Theorem paper_main_gaussian_psd_width_bounds n :
  sqrt (INR (paper_main_symmetric_dimension n)/2 - 1) <=
    paper_main_gaussian_psd_width n <=
  sqrt (INR (paper_main_symmetric_dimension n)/2).
Proof.
have HL := paper_main_gaussian_psd_support_lipschitz n.
have Hlo := paper_main_gaussian_mean_positive_square_lower
  (paper_main_symmetric_dimension n) (paper_main_gaussian_psd_support n)
  1 Rle_0_1 HL (paper_main_gaussian_psd_width_nonnegative n).
have Hhi := paper_main_gaussian_mean_positive_square_upper
  (paper_main_symmetric_dimension n) (paper_main_gaussian_psd_support n)
  1 Rle_0_1 HL.
rewrite paper_main_gaussian_psd_positive_square in Hlo Hhi.
replace (1^2) with 1 in Hlo by ring.
split; assumption.
Qed.

Theorem paper_main_gaussian_psd_projection_mean_bounds n :
  sqrt (INR (paper_main_symmetric_dimension n)/2 - 1) <=
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
      (paper_main_gaussian_psd_projection_norm n) <=
  sqrt (INR (paper_main_symmetric_dimension n)/2).
Proof.
pose D := paper_main_symmetric_dimension n.
pose F := paper_main_gaussian_psd_projection_norm n.
have HL := paper_main_gaussian_psd_projection_lipschitz n.
have [HF _] := paper_main_gaussian_lipschitz_domain D F 1 Rle_0_1 HL.
have Hnon : forall xs, List.length xs = D -> 0 <= F xs.
  move=> xs _; apply/RleP; exact: pmh_frobenius_ge0.
have Hmean := gaussian_iterated_nonnegative D F HF Hnon.
have Hvar := paper_main_gaussian_variance_identity D F 1 Rle_0_1 HL.
have Hbound := paper_main_gaussian_lipschitz_variance D F 1 Rle_0_1 HL.
have Hsq := paper_main_gaussian_lipschitz_mean_square D F 1 Rle_0_1 HL.
have HM : gaussian_iterated_expectation D (fun xs => F xs*F xs) = INR D/2.
  exact: paper_main_gaussian_psd_projection_second_moment.
rewrite HM in Hvar Hsq.
have HD : 0 <= INR D/2 by have := pos_INR D; lra.
have HS := pow2_sqrt _ HD; have HSp := sqrt_pos (INR D/2).
change (sqrt (INR D/2-1) <= gaussian_iterated_expectation D F <= sqrt (INR D/2)).
split; last nra.
destruct (Rle_dec 0 (INR D/2-1)) as [Ha|Ha].
- have := pow2_sqrt _ Ha; have := sqrt_pos (INR D/2-1); nra.
- rewrite sqrt_neg_0; lra.
Qed.
