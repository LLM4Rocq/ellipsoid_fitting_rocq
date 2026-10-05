(* The isotropic standard Gaussian on the symmetric (n+1) x (n+1)
   matrices. On D = (n+1)(n+2)/2 standard Gaussian coordinates xs,
   Z(xs) is the matrix whose coordinates in the checked orthonormal
   symmetric basis goe_basis are exactly xs. It is the existing feature row
   rescaled: paper_main_gaussian_feature_row n 0 xs = goe_scale n * Z(xs)
   with goe_scale n = sqrt (2 / (n+1)). This module proves the Frobenius
   identity ||Z||_F^2 = sum_k xs_k^2, the Frobenius isometry and the
   negation identity Z(-xs) = -Z(xs); the moments E||Z||_F^2 = D,
   E Tr Z = 0 and E (Tr Z)^2 = n+1 with their domains; and the sign symmetry
   E Phi(-Z) = E Phi(Z) for continuous, polynomially bounded Phi o Z. No
   Gaussian symmetry, moment or normalization is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  MatrixDefinitions MatrixCoordinates MatrixTrace MatrixGradient TensorDefinitions
  OperatorDefinitions NormEquivalence SymmetricDefinitions SymmetricBasis
  GoeDefinitions GoePairs GoeParseval GoeSynthesis
  VectorCoordinateDefinitions VectorCoordinates
  GaussianVectorDefinitions GaussianVectorMoments GaussianCovarianceDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianProductDefinitions GaussianProduct GaussianCoordinateSteinDomains
  GaussianCoordinateTopology GaussianCoordinateSuffixAlgebra
  MaximumRadiusRegularity MaximumRadiusComparison
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonBilinear
  PaperMainGordonLipschitz PaperMainGaussianNorm PaperMainGaussianFeatureCoordinates
  PaperMainGaussianLipschitzClip PaperMainGaussianLipschitzApproximation
  PaperMainGaussianSymmetricLawReflection.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_symmetric_gaussian n (xs : list R) : matrix n :=
  matrix_scale n (/ goe_scale n) (paper_main_gaussian_feature_row n 0 xs).

Definition paper_main_symmetric_identity n : matrix n :=
  matrix_build n (fun i j => if Nat.eqb i j then 1 else 0).

Lemma paper_main_symmetric_goe_scale n : goe_scale n = sqrt (2 / INR (S n)).
Proof. reflexivity. Qed.

Lemma paper_main_symmetric_feature_conversion n xs i j :
  matrix_entry n (paper_main_gaussian_feature_row n 0 xs) i j =
    goe_scale n * matrix_entry n (paper_main_symmetric_gaussian n xs) i j.
Proof.
unfold paper_main_symmetric_gaussian; rewrite matrix_entry_scale.
field; apply Rgt_not_eq; apply goe_scale_positive.
Qed.

Theorem paper_main_symmetric_feature_row_conversion n xs :
  paper_main_gaussian_feature_row n 0 xs =
    matrix_scale n (goe_scale n) (paper_main_symmetric_gaussian n xs).
Proof.
apply matrix_ext; intros i j Hi Hj.
rewrite matrix_entry_scale; apply paper_main_symmetric_feature_conversion.
Qed.

Lemma paper_main_symmetric_combination n (A B : matrix n) c :
  symmetric_matrix n A -> symmetric_matrix n B ->
  symmetric_matrix n (matrix_add n A (matrix_scale n c B)).
Proof.
intros HA HB i j Hi Hj.
rewrite !matrix_entry_add, !matrix_entry_scale.
rewrite (HA i j Hi Hj), (HB i j Hi Hj); reflexivity.
Qed.

Lemma paper_main_symmetric_gaussian_symmetric n xs :
  symmetric_matrix n (paper_main_symmetric_gaussian n xs).
Proof.
intros i j Hi Hj; unfold paper_main_symmetric_gaussian.
rewrite !matrix_entry_scale.
rewrite (paper_main_gaussian_feature_row_symmetric n 0 xs i j Hi Hj); reflexivity.
Qed.

Lemma paper_main_symmetric_gaussian_coordinate n xs k :
  (k < paper_main_symmetric_dimension n)%nat ->
  paper_main_symmetric_coordinates n (paper_main_symmetric_gaussian n xs) k =
    List.nth k xs 0.
Proof.
intros Hk; unfold paper_main_symmetric_coordinates, paper_main_symmetric_gaussian.
rewrite trace_pair_scale.
change (/ goe_scale n * paper_main_symmetric_coordinates n
  (paper_main_gaussian_feature_row n 0 xs) k = List.nth k xs 0).
rewrite (paper_main_gaussian_feature_row_coordinate n 0 xs k Hk).
rewrite Nat.mul_0_l, Nat.add_0_l.
field; apply Rgt_not_eq; apply goe_scale_positive.
Qed.

Lemma paper_main_symmetric_coordinate_add n (A B : matrix n) c k :
  paper_main_symmetric_coordinates n (matrix_add n A (matrix_scale n c B)) k =
    paper_main_symmetric_coordinates n A k + c * paper_main_symmetric_coordinates n B k.
Proof.
unfold paper_main_symmetric_coordinates.
rewrite trace_pair_add, trace_pair_scale; reflexivity.
Qed.

Lemma paper_main_symmetric_norm_coordinates n (A : matrix n) :
  symmetric_matrix n A ->
  ((`|A|)%R) ^ 2 = finite_sum (fun k => paper_main_symmetric_coordinates n A k *
    paper_main_symmetric_coordinates n A k) (List.seq 0 (paper_main_symmetric_dimension n)).
Proof.
intros HA.
rewrite <- (paper_main_symmetric_coordinate_norm n A HA).
rewrite paper_main_gordon_euclidean_squared; reflexivity.
Qed.

Lemma paper_main_symmetric_gaussian_frobenius_squared n xs :
  ((`|paper_main_symmetric_gaussian n xs|)%R) ^ 2 =
    finite_sum (fun k => List.nth k xs 0 * List.nth k xs 0)
      (List.seq 0 (paper_main_symmetric_dimension n)).
Proof.
rewrite (paper_main_symmetric_norm_coordinates n _ (paper_main_symmetric_gaussian_symmetric n xs)).
apply finite_sum_ext; intros k Hk; apply in_seq in Hk.
rewrite (paper_main_symmetric_gaussian_coordinate n xs k ltac:(lia)); reflexivity.
Qed.

Lemma paper_main_symmetric_gaussian_frobenius_sum_squares n xs :
  List.length xs = paper_main_symmetric_dimension n ->
  ((`|paper_main_symmetric_gaussian n xs|)%R) ^ 2 = gaussian_sum_squares xs.
Proof.
intros Hxs.
rewrite paper_main_symmetric_gaussian_frobenius_squared.
rewrite <- (paper_main_gaussian_squares_coordinates _ xs Hxs).
apply finite_sum_ext; intros k _; ring.
Qed.

Lemma paper_main_symmetric_coordinates_zero n (A : matrix n) :
  symmetric_matrix n A ->
  (forall k, (k < paper_main_symmetric_dimension n)%nat ->
    paper_main_symmetric_coordinates n A k = 0) ->
  A = 0%R.
Proof.
intros HA Hz.
pose proof (paper_main_symmetric_norm_coordinates n A HA) as H2.
rewrite (finite_sum_ext _ (fun _ => 0)) in H2.
- rewrite finite_sum_zero in H2.
  apply (@normr0_eq0 _ (matrix_NormedModule n) A).
  change ((`|A|)%R = 0).
  pose proof (paper_main_gordon_euclidean_nonnegative (paper_main_symmetric_dimension n)
    (paper_main_symmetric_coordinates n A)) as Hn.
  rewrite (paper_main_symmetric_coordinate_norm n A HA) in Hn.
  nra.
- intros k Hk; apply in_seq in Hk.
  rewrite (Hz k ltac:(lia)); ring.
Qed.

Lemma paper_main_symmetric_nth_neg (xs : list R) k :
  List.nth k (List.map Ropp xs) 0 = - List.nth k xs 0.
Proof.
revert k; induction xs as [|x xs IH]; intros [|k]; simpl; try ring.
apply IH.
Qed.

(* The matrix instance on the left of linearB is reached by conversion. *)
Lemma paper_main_symmetric_entry_sub n (A B : matrix n) i j :
  matrix_entry n (A - B)%R i j = matrix_entry n A i j - matrix_entry n B i j.
Proof.
unfold matrix_entry.
transitivity (tuple_entry R^o n j (tuple_entry (tuple_NormedModule R^o n) n i A -
  tuple_entry (tuple_NormedModule R^o n) n i B)%R).
- f_equal. exact (linearB (tuple_entry (tuple_NormedModule R^o n) n i) A B).
- exact (linearB (tuple_entry R^o n j) (tuple_entry (tuple_NormedModule R^o n) n i A)
    (tuple_entry (tuple_NormedModule R^o n) n i B)).
Qed.

Lemma paper_main_symmetric_entry_opp n (A : matrix n) i j :
  matrix_entry n (- A)%R i j = - matrix_entry n A i j.
Proof.
unfold matrix_entry.
transitivity (tuple_entry R^o n j (- tuple_entry (tuple_NormedModule R^o n) n i A)%R).
- f_equal. exact (linearN (tuple_entry (tuple_NormedModule R^o n) n i) A).
- exact (linearN (tuple_entry R^o n j) (tuple_entry (tuple_NormedModule R^o n) n i A)).
Qed.

Theorem paper_main_symmetric_gaussian_neg n xs :
  paper_main_symmetric_gaussian n (List.map Ropp xs) =
    matrix_scale n (-1) (paper_main_symmetric_gaussian n xs).
Proof.
assert (Hzero : matrix_add n (paper_main_symmetric_gaussian n (List.map Ropp xs))
    (matrix_scale n 1 (paper_main_symmetric_gaussian n xs)) = matrix_zero n).
{ apply paper_main_symmetric_coordinates_zero.
  - apply paper_main_symmetric_combination; apply paper_main_symmetric_gaussian_symmetric.
  - intros k Hk.
    rewrite paper_main_symmetric_coordinate_add.
    rewrite (paper_main_symmetric_gaussian_coordinate n _ k Hk).
    rewrite (paper_main_symmetric_gaussian_coordinate n xs k Hk).
    rewrite paper_main_symmetric_nth_neg; ring. }
apply matrix_ext; intros i j Hi Hj.
pose proof (f_equal (fun M => matrix_entry n M i j) Hzero) as He; cbv beta in He.
rewrite matrix_entry_add, matrix_entry_scale, matrix_entry_zero in He.
rewrite matrix_entry_scale; lra.
Qed.

Corollary paper_main_symmetric_gaussian_opp n xs :
  paper_main_symmetric_gaussian n (List.map Ropp xs) = (- paper_main_symmetric_gaussian n xs)%R.
Proof.
apply matrix_ext; intros i j Hi Hj.
rewrite paper_main_symmetric_entry_opp, paper_main_symmetric_gaussian_neg, matrix_entry_scale.
ring.
Qed.

Theorem paper_main_symmetric_gaussian_isometry n xs ys :
  (`|paper_main_symmetric_gaussian n xs - paper_main_symmetric_gaussian n ys|)%R =
    paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
assert (Hsub : (paper_main_symmetric_gaussian n xs - paper_main_symmetric_gaussian n ys)%R =
    matrix_add n (paper_main_symmetric_gaussian n xs)
      (matrix_scale n (-1) (paper_main_symmetric_gaussian n ys))).
{ apply matrix_ext; intros i j Hi Hj.
  rewrite paper_main_symmetric_entry_sub, matrix_entry_add, matrix_entry_scale; ring. }
rewrite Hsub.
pose proof (paper_main_symmetric_combination n _ _ (-1)
  (paper_main_symmetric_gaussian_symmetric n xs)
  (paper_main_symmetric_gaussian_symmetric n ys)) as HS.
rewrite <- (paper_main_symmetric_coordinate_norm n _ HS).
unfold euclidean_norm, paper_main_gordon_distance, squared_norm.
f_equal; apply finite_sum_ext; intros k Hk; apply in_seq in Hk.
rewrite paper_main_symmetric_coordinate_add.
rewrite (paper_main_symmetric_gaussian_coordinate n xs k ltac:(lia)).
rewrite (paper_main_symmetric_gaussian_coordinate n ys k ltac:(lia)); ring.
Qed.

(* The identity matrix and the trace. *)

Lemma paper_main_symmetric_identity_symmetric n :
  symmetric_matrix n (paper_main_symmetric_identity n).
Proof.
intros i j Hi Hj; unfold paper_main_symmetric_identity.
rewrite (matrix_entry_build n _ i j Hi Hj).
rewrite (matrix_entry_build n _ j i Hj Hi).
rewrite Nat.eqb_sym; reflexivity.
Qed.

Lemma paper_main_symmetric_trace_identity n (A : matrix n) :
  matrix_trace n A = trace_pair n (paper_main_symmetric_identity n) A.
Proof.
unfold matrix_trace, trace_pair.
apply coordinate_sum_ext; intros i Hi.
transitivity (coordinate_sum n (fun j => matrix_entry n A j i *
  (if Nat.eqb j i then 1 else 0))).
- symmetry; exact (gradient_coordinate_sum_select n i (fun j => matrix_entry n A j i) Hi).
- apply coordinate_sum_ext; intros j Hj.
  unfold paper_main_symmetric_identity; rewrite (matrix_entry_build n _ i j Hi Hj).
  rewrite Nat.eqb_sym; ring.
Qed.

Lemma paper_main_symmetric_identity_trace n :
  trace_pair n (paper_main_symmetric_identity n) (paper_main_symmetric_identity n) =
    INR (S n).
Proof.
rewrite <- paper_main_symmetric_trace_identity.
unfold matrix_trace.
rewrite paper_main_feature_coordinate_sum.
rewrite (finite_sum_ext _ (fun _ => 1)).
- rewrite finite_sum_const; rewrite length_seq; ring.
- intros i Hi; apply in_seq in Hi.
  unfold paper_main_symmetric_identity.
  rewrite (matrix_entry_build n _ i i ltac:(lia) ltac:(lia)).
  rewrite Nat.eqb_refl; reflexivity.
Qed.

Definition paper_main_symmetric_trace_coefficient n k : R :=
  paper_main_symmetric_coordinates n (paper_main_symmetric_identity n) k.

Theorem paper_main_symmetric_gaussian_trace n xs :
  matrix_trace n (paper_main_symmetric_gaussian n xs) =
    finite_sum (fun k => paper_main_symmetric_trace_coefficient n k * List.nth k xs 0)
      (List.seq 0 (paper_main_symmetric_dimension n)).
Proof.
rewrite paper_main_symmetric_trace_identity.
rewrite <- (paper_main_symmetric_coordinate_pairing n _ _
  (paper_main_symmetric_identity_symmetric n) (paper_main_symmetric_gaussian_symmetric n xs)).
unfold paper_main_gordon_dot; apply finite_sum_ext; intros k Hk; apply in_seq in Hk.
rewrite (paper_main_symmetric_gaussian_coordinate n xs k ltac:(lia)); reflexivity.
Qed.

Theorem paper_main_symmetric_trace_coefficient_squares n :
  finite_sum (fun k => paper_main_symmetric_trace_coefficient n k *
    paper_main_symmetric_trace_coefficient n k)
    (List.seq 0 (paper_main_symmetric_dimension n)) = INR (S n).
Proof.
rewrite <- paper_main_symmetric_identity_trace.
rewrite <- (paper_main_symmetric_coordinate_pairing n _ _
  (paper_main_symmetric_identity_symmetric n) (paper_main_symmetric_identity_symmetric n)).
reflexivity.
Qed.

(* Moments under the iterated Gaussian expectation on D coordinates. *)

Lemma paper_main_symmetric_trace_linear_form n xs :
  matrix_trace n (paper_main_symmetric_gaussian n xs) =
    coordinate_sum (goe_vector_index n) (fun i =>
      paper_main_symmetric_trace_coefficient n i *
      vector_entry (goe_vector_index n) (vector_of_list (goe_vector_index n) xs) i).
Proof.
rewrite paper_main_symmetric_gaussian_trace; rewrite paper_main_feature_coordinate_sum.
unfold paper_main_symmetric_dimension.
apply finite_sum_ext; intros i Hi; apply in_seq in Hi.
rewrite (vector_entry_of_list (goe_vector_index n) xs i ltac:(lia)); reflexivity.
Qed.

Theorem paper_main_symmetric_gaussian_frobenius_moment n :
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => ((`|paper_main_symmetric_gaussian n xs|)%R) ^ 2) =
  INR (paper_main_symmetric_dimension n).
Proof.
rewrite (gaussian_iterated_expectation_ext _ _ gaussian_sum_squares).
- apply gaussian_sum_squares_expectation.
- intros xs Hxs; exact (paper_main_symmetric_gaussian_frobenius_sum_squares n xs Hxs).
Qed.

Theorem paper_main_symmetric_gaussian_frobenius_regular n :
  finite_joint_continuous (paper_main_symmetric_dimension n)
    (fun xs => ((`|paper_main_symmetric_gaussian n xs|)%R) ^ 2) /\
  finite_polynomial_bound (paper_main_symmetric_dimension n)
    (INR (paper_main_symmetric_dimension n)) 2
    (fun xs => ((`|paper_main_symmetric_gaussian n xs|)%R) ^ 2).
Proof.
split.
- apply (finite_joint_continuous_ext _ gaussian_sum_squares).
  + intros xs Hxs; symmetry; exact (paper_main_symmetric_gaussian_frobenius_sum_squares n xs Hxs).
  + apply maximum_radius_squares_continuous.
- apply (finite_polynomial_bound_ext _ _ _ gaussian_sum_squares).
  + intros xs Hxs; symmetry; exact (paper_main_symmetric_gaussian_frobenius_sum_squares n xs Hxs).
  + split; [apply pos_INR|].
    intros xs Hxs; rewrite Rabs_pos_eq by apply maximum_radius_squares_nonnegative.
    rewrite <- Hxs; apply maximum_radius_squares_polynomial.
Qed.

Theorem paper_main_symmetric_gaussian_frobenius_domain n :
  gaussian_covariance_domain (paper_main_symmetric_dimension n)
    (fun xs => ((`|paper_main_symmetric_gaussian n xs|)%R) ^ 2).
Proof.
destruct (paper_main_symmetric_gaussian_frobenius_regular n) as [HC HB].
exact (gaussian_coordinate_polynomial_domain _ _ _ _ HC HB).
Qed.

Theorem paper_main_symmetric_gaussian_trace_moments n :
  gaussian_covariance_domain (paper_main_symmetric_dimension n)
    (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs)) /\
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs)) = 0 /\
  gaussian_covariance_domain (paper_main_symmetric_dimension n)
    (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs) *
               matrix_trace n (paper_main_symmetric_gaussian n xs)) /\
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs) *
               matrix_trace n (paper_main_symmetric_gaussian n xs)) = INR (S n).
Proof.
pose proof (gaussian_vector_linear_form_moment (goe_vector_index n)
  (paper_main_symmetric_trace_coefficient n)) as [HD1 HE1].
pose proof (gaussian_vector_linear_forms_covariance (goe_vector_index n)
  (paper_main_symmetric_trace_coefficient n) (paper_main_symmetric_trace_coefficient n))
  as [HF HE2].
apply Forall_inv_tail in HF; apply Forall_inv_tail in HF; apply Forall_inv in HF.
assert (Hfun : (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs)) =
  (fun xs => coordinate_sum (goe_vector_index n) (fun i =>
    paper_main_symmetric_trace_coefficient n i *
    vector_entry (goe_vector_index n) (vector_of_list (goe_vector_index n) xs) i))).
{ apply functional_extensionality; intros xs; apply paper_main_symmetric_trace_linear_form. }
assert (Hfun2 : (fun xs => matrix_trace n (paper_main_symmetric_gaussian n xs) *
    matrix_trace n (paper_main_symmetric_gaussian n xs)) =
  (fun xs => coordinate_sum (goe_vector_index n) (fun i =>
    paper_main_symmetric_trace_coefficient n i *
    vector_entry (goe_vector_index n) (vector_of_list (goe_vector_index n) xs) i) *
    coordinate_sum (goe_vector_index n) (fun i =>
    paper_main_symmetric_trace_coefficient n i *
    vector_entry (goe_vector_index n) (vector_of_list (goe_vector_index n) xs) i))).
{ apply functional_extensionality; intros xs; rewrite paper_main_symmetric_trace_linear_form;
    reflexivity. }
rewrite Hfun; rewrite Hfun2.
unfold paper_main_symmetric_dimension.
split; [exact HD1|].
split; [exact HE1|].
split; [exact HF|].
unfold gaussian_vector_expectation in HE2; cbv beta in HE2; rewrite HE2.
rewrite <- (paper_main_symmetric_trace_coefficient_squares n).
rewrite paper_main_feature_coordinate_sum; reflexivity.
Qed.

(* Sign symmetry. *)

Theorem paper_main_symmetric_gaussian_sign_symmetry n (Phi : matrix n -> R) C p :
  finite_joint_continuous (paper_main_symmetric_dimension n)
    (fun xs => Phi (paper_main_symmetric_gaussian n xs)) ->
  finite_polynomial_bound (paper_main_symmetric_dimension n) C p
    (fun xs => Phi (paper_main_symmetric_gaussian n xs)) ->
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (matrix_scale n (-1) (paper_main_symmetric_gaussian n xs))) =
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (paper_main_symmetric_gaussian n xs)).
Proof.
intros HC HB.
rewrite <- (paper_main_gaussian_iterated_reflect _ _ C p HC HB).
apply gaussian_iterated_expectation_ext; intros xs _.
cbv beta; rewrite paper_main_symmetric_gaussian_neg; reflexivity.
Qed.

Theorem paper_main_symmetric_gaussian_lipschitz_transfer n (Phi : matrix n -> R) L :
  (forall A B : matrix n, Rabs (Phi A - Phi B) <= L * (`|A - B|)%R) ->
  forall xs ys, List.length xs = paper_main_symmetric_dimension n ->
    List.length ys = paper_main_symmetric_dimension n ->
    Rabs (Phi (paper_main_symmetric_gaussian n xs) - Phi (paper_main_symmetric_gaussian n ys)) <=
      L * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
intros HPhi xs ys _ _.
rewrite <- paper_main_symmetric_gaussian_isometry; apply HPhi.
Qed.

Theorem paper_main_symmetric_gaussian_lipschitz_sign_symmetry n (Phi : matrix n -> R) L :
  0 <= L -> (forall A B : matrix n, Rabs (Phi A - Phi B) <= L * (`|A - B|)%R) ->
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (matrix_scale n (-1) (paper_main_symmetric_gaussian n xs))) =
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => Phi (paper_main_symmetric_gaussian n xs)).
Proof.
intros HL HPhi.
pose proof (paper_main_symmetric_gaussian_lipschitz_transfer n Phi L HPhi) as HLip.
exact (paper_main_symmetric_gaussian_sign_symmetry n Phi _ 2
  (paper_main_gaussian_lipschitz_continuous _ _ L HL HLip)
  (paper_main_gaussian_lipschitz_polynomial_bound _ _ L HL HLip)).
Qed.
