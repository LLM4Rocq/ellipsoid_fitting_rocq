(* The isotropic symmetric Gaussian on the matrices 'M[R]_(S n).
   paper_main_public_symmetric_gaussian n xs is the transport, by
   paper_main_matrix_to_public, of the internal Z(xs) of
   PaperMainGaussianSymmetricLaw. The feature row of
   PaperMainGaussianPublicFeature is goe_scale n *: Zp(xs), with
   goe_scale n = sqrt (2 / (n+1)). In 'M[R]_(S n): Zp(xs) is symmetric;
   its pairings with the transported orthonormal basis are the coordinates
   xs_k; its Frobenius pairings and norm are those of the coordinate lists;
   Zp(-xs) = -Zp(xs); and the Frobenius distance of two values is the
   coordinate distance. The trace is sum_k c_k xs_k with sum_k c_k^2 = n+1,
   so it is sqrt(n+1)-Lipschitz. The moments E||Zp||_F^2 = D, E Tr Zp = 0 and
   E (Tr Zp)^2 = n+1 hold with their domains, and also as integrals for
   gaussian_product_law D. A test Phi that is L-Lipschitz for the Frobenius
   distance on symmetric matrices is integrable for that law, its mean is
   the iterated mean, and E Phi(-Zp) = E Phi(Zp). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums MatrixDefinitions
  MatrixCoordinates MatrixTrace TensorDefinitions GoeDefinitions GoeSynthesis
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateWeights GaussianCoordinateSuffixAlgebra
  GaussianProductDefinitions GaussianProduct GaussianCovarianceDefinitions
  GaussianProbabilityProductDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainMatrixTransport PaperMainGordonProcessCovariance PaperMainGordonScalar
  PaperMainGaussianFeatureCoordinates
  PaperMainGaussianPublicFeature PaperMainGordonLipschitz PaperMainGaussianNorm
  PaperMainGaussianSmoothLaw PaperMainGaussianLipschitzClip
  PaperMainGaussianLipschitzApproximation PaperMainGaussianLipschitzApproximationLaw
  PaperMainGaussianSymmetricLawReflection PaperMainGaussianSymmetricLaw.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_public_symmetric_gaussian n (xs : list R) : 'M[R]_(S n) :=
  paper_main_matrix_to_public n (paper_main_symmetric_gaussian n xs).

Definition paper_main_public_symmetric_basis n k : 'M[R]_(S n) :=
  paper_main_matrix_to_public n (goe_basis n k).

(* The transport is linear. *)

Lemma paper_main_public_transport_sub n (A B : MatrixDefinitions.matrix n) :
  paper_main_matrix_to_public n (A - B)%R =
    (paper_main_matrix_to_public n A - paper_main_matrix_to_public n B)%R.
Proof.
apply/matrixP => i j; rewrite !mxE ?paper_main_matrix_to_public_entry.
exact: paper_main_symmetric_entry_sub.
Qed.

Lemma paper_main_public_transport_opp n (A : MatrixDefinitions.matrix n) :
  paper_main_matrix_to_public n (- A)%R = (- paper_main_matrix_to_public n A)%R.
Proof.
apply/matrixP => i j; rewrite !mxE ?paper_main_matrix_to_public_entry.
exact: paper_main_symmetric_entry_opp.
Qed.

Lemma paper_main_public_transport_scale n c (A : MatrixDefinitions.matrix n) :
  paper_main_matrix_to_public n (matrix_scale n c A) =
    (c *: paper_main_matrix_to_public n A)%R.
Proof.
apply/matrixP => i j; rewrite !mxE ?paper_main_matrix_to_public_entry.
exact: matrix_entry_scale.
Qed.

Lemma paper_main_public_transport_trace n (A : MatrixDefinitions.matrix n) :
  paper_main_trace (paper_main_matrix_to_public n A) = matrix_trace n A.
Proof.
rewrite /paper_main_trace /matrix_trace paper_main_matrix_coordinate_sum.
by apply: eq_bigr => i _; rewrite paper_main_matrix_to_public_entry.
Qed.

(* The conversion from the feature row. *)

Theorem paper_main_public_symmetric_feature_conversion n xs :
  paper_main_public_gaussian_row n 0 xs =
    (goe_scale n *: paper_main_public_symmetric_gaussian n xs)%R.
Proof.
by rewrite /paper_main_public_gaussian_row paper_main_symmetric_feature_row_conversion
  paper_main_public_transport_scale.
Qed.

Lemma paper_main_public_symmetric_gaussian_symmetric n xs :
  paper_main_symmetric (paper_main_public_symmetric_gaussian n xs).
Proof.
apply: paper_main_matrix_public_symmetric; exact: paper_main_symmetric_gaussian_symmetric.
Qed.

(* Coordinates in the transported orthonormal basis. *)

(* Frobenius norm, negation and isometry. *)

Theorem paper_main_public_symmetric_gaussian_frobenius n xs :
  paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) =
    (`|paper_main_symmetric_gaussian n xs|)%R.
Proof.
by rewrite /paper_main_public_symmetric_gaussian -paper_main_matrix_public_frobenius.
Qed.

Theorem paper_main_public_symmetric_gaussian_frobenius_sum_squares n xs :
  List.length xs = paper_main_symmetric_dimension n ->
  paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) ^ 2 =
    gaussian_sum_squares xs.
Proof.
move=> Hxs; rewrite paper_main_public_symmetric_gaussian_frobenius.
exact: paper_main_symmetric_gaussian_frobenius_sum_squares.
Qed.

Lemma paper_main_public_symmetric_gaussian_frobenius_nonnegative n xs :
  0 <= paper_main_frobenius (paper_main_public_symmetric_gaussian n xs).
Proof.
rewrite paper_main_public_symmetric_gaussian_frobenius.
apply/RleP; exact: normr_ge0.
Qed.

Theorem paper_main_public_symmetric_gaussian_norm n xs :
  List.length xs = paper_main_symmetric_dimension n ->
  paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) =
    paper_main_gaussian_norm xs.
Proof.
move=> Hxs; rewrite /paper_main_gaussian_norm.
rewrite -(paper_main_public_symmetric_gaussian_frobenius_sum_squares n xs Hxs).
by rewrite (sqrt_pow2 _ (paper_main_public_symmetric_gaussian_frobenius_nonnegative n xs)).
Qed.

Theorem paper_main_public_symmetric_gaussian_opp n xs :
  paper_main_public_symmetric_gaussian n (List.map Ropp xs) =
    (- paper_main_public_symmetric_gaussian n xs)%R.
Proof.
by rewrite /paper_main_public_symmetric_gaussian paper_main_symmetric_gaussian_opp
  paper_main_public_transport_opp.
Qed.

Theorem paper_main_public_symmetric_gaussian_isometry n xs ys :
  paper_main_frobenius (paper_main_public_symmetric_gaussian n xs -
    paper_main_public_symmetric_gaussian n ys)%R =
  paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
rewrite /paper_main_public_symmetric_gaussian -paper_main_public_transport_sub.
rewrite -paper_main_matrix_public_frobenius.
exact: paper_main_symmetric_gaussian_isometry.
Qed.

(* The trace. *)

Theorem paper_main_public_symmetric_gaussian_trace_internal n xs :
  paper_main_trace (paper_main_public_symmetric_gaussian n xs) =
    matrix_trace n (paper_main_symmetric_gaussian n xs).
Proof. exact: paper_main_public_transport_trace. Qed.

Theorem paper_main_public_symmetric_gaussian_trace n xs :
  paper_main_trace (paper_main_public_symmetric_gaussian n xs) =
    finite_sum (fun k => paper_main_symmetric_trace_coefficient n k * List.nth k xs 0)
      (List.seq 0 (paper_main_symmetric_dimension n)).
Proof.
rewrite paper_main_public_symmetric_gaussian_trace_internal.
exact: paper_main_symmetric_gaussian_trace.
Qed.

Theorem paper_main_public_symmetric_trace_lipschitz n xs ys :
  Rabs (paper_main_trace (paper_main_public_symmetric_gaussian n xs) -
        paper_main_trace (paper_main_public_symmetric_gaussian n ys)) <=
  sqrt (INR (S n)) * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
rewrite !paper_main_public_symmetric_gaussian_trace -finite_sum_minus.
have -> : finite_sum (fun k => paper_main_symmetric_trace_coefficient n k * List.nth k xs 0 -
    paper_main_symmetric_trace_coefficient n k * List.nth k ys 0)
    (List.seq 0 (paper_main_symmetric_dimension n)) =
  finite_sum (fun k => paper_main_symmetric_trace_coefficient n k *
    (List.nth k xs 0 - List.nth k ys 0)) (List.seq 0 (paper_main_symmetric_dimension n)).
  by apply: finite_sum_ext => k _; ring.
have HC := paper_main_gordon_sum_cauchy (paper_main_symmetric_trace_coefficient n)
  (fun k => List.nth k xs 0 - List.nth k ys 0)
  (List.seq 0 (paper_main_symmetric_dimension n)).
have Hc2 : finite_sum (fun k => paper_main_symmetric_trace_coefficient n k ^ 2)
    (List.seq 0 (paper_main_symmetric_dimension n)) = INR (S n).
  rewrite -(paper_main_symmetric_trace_coefficient_squares n).
  by apply: finite_sum_ext => k _; ring.
rewrite Hc2 in HC.
rewrite /paper_main_gordon_distance -(sqrt_mult_alt _ _ (pos_INR (S n))).
rewrite -sqrt_Rsqr_abs; apply: sqrt_le_1_alt.
rewrite Rsqr_pow2; exact: HC.
Qed.

(* Regularity of the moment functions. *)

Theorem paper_main_public_symmetric_trace_regular n :
  finite_joint_continuous (paper_main_symmetric_dimension n)
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs)) /\
  exists C, finite_polynomial_bound (paper_main_symmetric_dimension n) C 2
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs)).
Proof.
have HL : 0 <= sqrt (INR (S n)) by apply: sqrt_pos.
have HLip : forall xs ys,
    List.length xs = paper_main_symmetric_dimension n ->
    List.length ys = paper_main_symmetric_dimension n ->
    Rabs (paper_main_trace (paper_main_public_symmetric_gaussian n xs) -
      paper_main_trace (paper_main_public_symmetric_gaussian n ys)) <=
    sqrt (INR (S n)) * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
  by move=> xs ys _ _; exact: paper_main_public_symmetric_trace_lipschitz.
split; first exact: (paper_main_gaussian_lipschitz_continuous _ _ _ HL HLip).
eexists; exact: (paper_main_gaussian_lipschitz_polynomial_bound _ _ _ HL HLip).
Qed.

Theorem paper_main_public_symmetric_trace_square_regular n :
  finite_joint_continuous (paper_main_symmetric_dimension n)
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs) *
      paper_main_trace (paper_main_public_symmetric_gaussian n xs)) /\
  exists C, finite_polynomial_bound (paper_main_symmetric_dimension n) C 4
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs) *
      paper_main_trace (paper_main_public_symmetric_gaussian n xs)).
Proof.
have [HC [C HB]] := paper_main_public_symmetric_trace_regular n.
split; first exact: finite_joint_continuous_mult.
exists (C * C); exact: (finite_polynomial_bound_mult _ _ _ 2 2 _ _ HB HB).
Qed.

Theorem paper_main_public_symmetric_frobenius_regular n :
  finite_joint_continuous (paper_main_symmetric_dimension n)
    (fun xs => paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) ^ 2) /\
  finite_polynomial_bound (paper_main_symmetric_dimension n)
    (INR (paper_main_symmetric_dimension n)) 2
    (fun xs => paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) ^ 2).
Proof.
have [HC HB] := paper_main_symmetric_gaussian_frobenius_regular n.
have He : forall xs, List.length xs = paper_main_symmetric_dimension n ->
    (`|paper_main_symmetric_gaussian n xs|)%R ^ 2 =
    paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) ^ 2.
  by move=> xs _; rewrite paper_main_public_symmetric_gaussian_frobenius.
split; first exact: (finite_joint_continuous_ext _ _ _ He HC).
exact: (finite_polynomial_bound_ext _ _ _ _ _ He HB).
Qed.

(* The moments under the iterated Gaussian expectation on D coordinates. *)

Theorem paper_main_public_symmetric_gaussian_moments n :
  gaussian_covariance_domain (paper_main_symmetric_dimension n)
    (fun xs => paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) ^ 2) /\
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) ^ 2) =
    INR (paper_main_symmetric_dimension n) /\
  gaussian_covariance_domain (paper_main_symmetric_dimension n)
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs)) /\
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs)) = 0 /\
  gaussian_covariance_domain (paper_main_symmetric_dimension n)
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs) *
      paper_main_trace (paper_main_public_symmetric_gaussian n xs)) /\
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs) *
      paper_main_trace (paper_main_public_symmetric_gaussian n xs)) = INR (S n).
Proof.
have -> : (fun xs => paper_main_frobenius (paper_main_public_symmetric_gaussian n xs) ^ 2) =
    (fun xs => (`|paper_main_symmetric_gaussian n xs|)%R ^ 2).
  by apply: funext => xs; rewrite paper_main_public_symmetric_gaussian_frobenius.
have -> : (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs)) =
    (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs)).
  by apply: funext => xs; rewrite paper_main_public_symmetric_gaussian_trace_internal.
have -> : (fun xs => paper_main_trace (paper_main_public_symmetric_gaussian n xs) *
      paper_main_trace (paper_main_public_symmetric_gaussian n xs)) =
    (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs) *
      matrix_trace n (paper_main_symmetric_gaussian n xs)).
  by apply: funext => xs; rewrite paper_main_public_symmetric_gaussian_trace_internal.
split; first exact: paper_main_symmetric_gaussian_frobenius_domain.
split; first exact: paper_main_symmetric_gaussian_frobenius_moment.
exact: paper_main_symmetric_gaussian_trace_moments.
Qed.

(* Sign symmetry. *)

Theorem paper_main_public_symmetric_gaussian_sign_symmetry n (Phi : 'M[R]_(S n) -> R) C p :
  finite_joint_continuous (paper_main_symmetric_dimension n)
    (fun xs => Phi (paper_main_public_symmetric_gaussian n xs)) ->
  finite_polynomial_bound (paper_main_symmetric_dimension n) C p
    (fun xs => Phi (paper_main_public_symmetric_gaussian n xs)) ->
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (- paper_main_public_symmetric_gaussian n xs)%R) =
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (paper_main_public_symmetric_gaussian n xs)).
Proof.
move=> HC HB.
rewrite -(paper_main_gaussian_iterated_reflect _ _ C p HC HB).
apply: gaussian_iterated_expectation_ext => xs _; cbv beta.
by rewrite paper_main_public_symmetric_gaussian_opp.
Qed.

(* Frobenius-Lipschitz tests on symmetric matrices. *)

Theorem paper_main_public_symmetric_lipschitz_transfer n (Phi : 'M[R]_(S n) -> R) L :
  (forall A B : 'M[R]_(S n), paper_main_symmetric A -> paper_main_symmetric B ->
    Rabs (Phi A - Phi B) <= L * paper_main_frobenius (A - B)%R) ->
  forall xs ys, List.length xs = paper_main_symmetric_dimension n ->
    List.length ys = paper_main_symmetric_dimension n ->
    Rabs (Phi (paper_main_public_symmetric_gaussian n xs) -
      Phi (paper_main_public_symmetric_gaussian n ys)) <=
    L * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
move=> HPhi xs ys _ _.
rewrite -paper_main_public_symmetric_gaussian_isometry.
apply: HPhi; exact: paper_main_public_symmetric_gaussian_symmetric.
Qed.

Lemma paper_main_public_symmetric_distance_neg d xs ys :
  paper_main_gordon_distance d (List.map Ropp xs) (List.map Ropp ys) =
    paper_main_gordon_distance d xs ys.
Proof.
rewrite /paper_main_gordon_distance; congr sqrt; apply: finite_sum_ext => k _.
rewrite !paper_main_symmetric_nth_neg; ring.
Qed.

Theorem paper_main_public_symmetric_neg_lipschitz_transfer n (Phi : 'M[R]_(S n) -> R) L :
  (forall A B : 'M[R]_(S n), paper_main_symmetric A -> paper_main_symmetric B ->
    Rabs (Phi A - Phi B) <= L * paper_main_frobenius (A - B)%R) ->
  forall xs ys, List.length xs = paper_main_symmetric_dimension n ->
    List.length ys = paper_main_symmetric_dimension n ->
    Rabs (Phi (- paper_main_public_symmetric_gaussian n xs)%R -
      Phi (- paper_main_public_symmetric_gaussian n ys)%R) <=
    L * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
move=> HPhi xs ys Hxs Hys.
rewrite -!paper_main_public_symmetric_gaussian_opp -paper_main_public_symmetric_distance_neg.
apply: (paper_main_public_symmetric_lipschitz_transfer n Phi L HPhi);
  by rewrite List.length_map.
Qed.

Theorem paper_main_public_symmetric_lipschitz_sign_symmetry n (Phi : 'M[R]_(S n) -> R) L :
  0 <= L ->
  (forall A B : 'M[R]_(S n), paper_main_symmetric A -> paper_main_symmetric B ->
    Rabs (Phi A - Phi B) <= L * paper_main_frobenius (A - B)%R) ->
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (- paper_main_public_symmetric_gaussian n xs)%R) =
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (paper_main_public_symmetric_gaussian n xs)).
Proof.
move=> HL HPhi.
have HLip := paper_main_public_symmetric_lipschitz_transfer n Phi L HPhi.
exact: (paper_main_public_symmetric_gaussian_sign_symmetry n Phi _ 2
  (paper_main_gaussian_lipschitz_continuous _ _ L HL HLip)
  (paper_main_gaussian_lipschitz_polynomial_bound _ _ L HL HLip)).
Qed.

(* Transport to the law gaussian_product_law D. *)

Theorem paper_main_public_symmetric_gaussian_law_moments n :
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
    (fun x => (paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x)) ^ 2)%:E) /\
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_x
      (paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x)) ^ 2)%:E =
    (INR (paper_main_symmetric_dimension n))%:E)%E /\
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
    (fun x => (paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)))%:E) /\
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_x
      (paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)))%:E = 0%:E)%E /\
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
    (fun x => (paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)) *
      paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)))%:E) /\
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_x
      (paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)) *
       paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)))%:E =
    (INR (S n))%:E)%E.
Proof.
have [_ [HF2 [_ [HT1 [_ HT2]]]]] := paper_main_public_symmetric_gaussian_moments n.
have [HFc HFb] := paper_main_public_symmetric_frobenius_regular n.
have [HTc [C HTb]] := paper_main_public_symmetric_trace_regular n.
have [HSc [C' HSb]] := paper_main_public_symmetric_trace_square_regular n.
have [IF EF] := paper_main_gaussian_law_transport _ _ _ _ HFc HFb.
have [IT ET] := paper_main_gaussian_law_transport _ _ _ _ HTc HTb.
have [IS ES] := paper_main_gaussian_law_transport _ _ _ _ HSc HSb.
split; first exact: IF.
split; first by rewrite EF HF2.
split; first exact: IT.
split; first by rewrite ET HT1.
split; first exact: IS.
by rewrite ES HT2.
Qed.
