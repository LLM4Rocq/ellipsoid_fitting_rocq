(* Gordon's expectation bound for the escape statistic. For N > 0 and a
   nonempty set T of unit vectors of R^M,
     E ||g_N|| - w(T) <= E inf_(v in T) ||A v||,
   where A is an N-by-M standard Gaussian matrix in row-major coordinates,
   g_N is a standard Gaussian vector of R^N and w(T) is the genuine set
   width paper_main_gordon_set_width M T. The exact Gaussian norm mean is
   kept. No compactness of T and no attained infimum is assumed.

   The checked finite comparison paper_main_gordon_matrix_comparison has its
   minimizing vectors on the left of the matrix. Here the minimizing index
   is a net v of T in R^M and the maximizing index a net z of the unit
   sphere of R^N, so the comparison is applied to the M-by-N matrix
   (TRANSPOSED convention, labelled below). Its auxiliary process is
   min_t <v_t, g> + max_y <z_y, h>; the reflection
   paper_main_gaussian_iterated_reflect identifies the mean of the first
   term as -w(v), and the sphere net gives max_y <z_y, h> >= (1-eps) ||h||.
   The transport back to the N-by-M convention is the proved coordinate
   permutation paper_main_gordon_transpose_expectation. Both nets are passed
   with the Frobenius error, as for the min-max bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality Epsilon.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateSteinDomains
  GaussianFiniteSums GaussianCovarianceDefinitions GaussianCovarianceSums
  MaximumRadiusMoments GaussianExpectationContinuity PaperMainGordonFinite
  PaperMainGordonProcessCovariance PaperMainGordonProcesses PaperMainGordonScalar
  PaperMainGaussianNorm PaperMainGordonWidth PaperMainGordonSetWidth PaperMainGordonNets
  PaperMainGordonNetExistence PaperMainGordonBilinear PaperMainGordonNetToAll
  PaperMainGordonOperatorNet PaperMainGordonOperatorContinuity PaperMainGordonLipschitz
  PaperMainGaussianLipschitzClip PaperMainGaussianLipschitzApproximation
  PaperMainGaussianSymmetricLawReflection PaperMainGordonCompactMinmax
  PaperMainGordonCompactExpectation PaperMainGordonEscapeReindex PaperMainGordonEscape.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_escape_nth_neg (xs : list R) k :
  List.nth k (List.map Ropp xs) 0 = - List.nth k xs 0.
Proof.
revert k; induction xs as [|x xs IH]; intros [|k]; simpl; try ring.
apply IH.
Qed.

Lemma paper_main_gordon_escape_seq_nonempty n : (0 < n)%nat -> List.seq 0 n <> [].
Proof.
intros Hn H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H;
  simpl in H; lia.
Qed.

Lemma paper_main_gordon_escape_support_bound d v S :
  S <> [] -> (forall t, In t S -> paper_main_gordon_dot d (v t) (v t) = 1) ->
  finite_polynomial_bound d (1 + INR d) 2 (paper_main_gordon_support d v S).
Proof.
intros HS Hv.
destruct (paper_main_gaussian_norm_polynomial d) as [HC HB]; split; [exact HC|].
intros xs Hxs.
pose proof (paper_main_gordon_support_abs_bound d v S xs HS Hxs Hv) as H.
specialize (HB xs Hxs); rewrite Rabs_pos_eq in HB by apply paper_main_gaussian_norm_nonnegative.
lra.
Qed.

(* The auxiliary process with the index families exchanged. *)

Lemma paper_main_gordon_escape_auxiliary_lower s r N M v z eps zs :
  (0 < s)%nat -> (0 < r)%nat -> (0 < N)%nat -> 0 <= eps ->
  List.length zs = (M + N)%nat ->
  paper_main_gordon_finite_net N (fun u => paper_main_gordon_dot N u u = 1) z
    (List.seq 0 r) eps ->
  -1 * paper_main_gordon_support M v (List.seq 0 s) (List.map Ropp (List.firstn M zs)) +
    (1 - eps) * paper_main_gaussian_norm (List.skipn M zs) <=
  finite_minimax (fun t y => paper_main_gordon_auxiliary M N (v t) (z y) zs)
    (List.seq 0 s) (List.seq 0 r).
Proof.
intros Hs Hr HN He Hzs Hznet.
pose proof (paper_main_gordon_escape_seq_nonempty s Hs) as HS.
pose proof (paper_main_gordon_escape_seq_nonempty r Hr) as HY.
assert (HE : (fun t y => paper_main_gordon_auxiliary M N (v t) (z y) zs) =
  (fun t y => paper_main_gordon_dot M (v t) (fun j => List.nth j (List.firstn M zs) 0) +
    paper_main_gordon_dot N (z y) (fun i => List.nth i (List.skipn M zs) 0))).
{ extensionality t; extensionality y; apply paper_main_gordon_auxiliary_blocks. }
rewrite HE, paper_main_gordon_minimax_separable by assumption.
assert (Hmin : finite_min (fun t => paper_main_gordon_dot M (v t)
    (fun j => List.nth j (List.firstn M zs) 0)) (List.seq 0 s) =
  -1 * paper_main_gordon_support M v (List.seq 0 s) (List.map Ropp (List.firstn M zs))).
{ unfold finite_min, paper_main_gordon_support.
  rewrite (paper_main_gordon_finite_max_ext _ (fun t => paper_main_gordon_dot M (v t)
    (fun j => List.nth j (List.map Ropp (List.firstn M zs)) 0))); [ring|].
  intros t _; unfold paper_main_gordon_dot.
  rewrite <- finite_sum_opp; apply finite_sum_ext; intros j _.
  rewrite paper_main_gordon_escape_nth_neg; ring. }
assert (Hh : List.length (List.skipn M zs) = N) by (rewrite length_skipn, Hzs; lia).
destruct (paper_main_gordon_escape_vector_attained N
  (fun i => List.nth i (List.skipn M zs) 0) HN) as [u [Hu Huh]].
assert (Hnorm : euclidean_norm (fun i => List.nth i (List.skipn M zs) 0) (List.seq 0 N) =
  paper_main_gaussian_norm (List.skipn M zs)).
{ unfold euclidean_norm, squared_norm, paper_main_gaussian_norm.
  rewrite (paper_main_gaussian_squares_coordinates N _ Hh); reflexivity. }
rewrite Hnorm in Huh.
destruct (proj2 Hznet u Hu) as [y [Hy Hdy]].
pose proof (paper_main_gordon_coefficient_dot_bound N (fun i => u i - z y i)
  (List.skipn M zs) eps Hh He Hdy) as Herr.
assert (Hsplit : paper_main_gordon_dot N (z y) (fun i => List.nth i (List.skipn M zs) 0) =
  paper_main_gordon_dot N u (fun i => List.nth i (List.skipn M zs) 0) -
  paper_main_gordon_dot N (fun i => u i - z y i) (fun i => List.nth i (List.skipn M zs) 0)).
{ unfold paper_main_gordon_dot; rewrite <- finite_sum_minus; apply finite_sum_ext; intros; ring. }
pose proof (finite_max_member (fun y => paper_main_gordon_dot N (z y)
  (fun i => List.nth i (List.skipn M zs) 0)) (List.seq 0 r) y Hy) as Hmax.
cbv beta in Hmax.
pose proof (Rle_abs (paper_main_gordon_dot N (fun i => u i - z y i)
  (fun i => List.nth i (List.skipn M zs) 0))) as Habs.
rewrite Hmin; lra.
Qed.

(* The finite margin, in the TRANSPOSED convention: the matrix has M rows
   indexed by the net v of T and N columns indexed by the sphere net z, and
   its M*N coordinates are row-major for that M-by-N matrix. *)

Theorem paper_main_gordon_escape_finite_margin s r N M v z eps :
  (0 < s)%nat -> (0 < r)%nat -> (0 < N)%nat -> 0 <= eps ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  paper_main_gordon_finite_net N (fun u => paper_main_gordon_dot N u u = 1) z
    (List.seq 0 r) eps ->
  (1 - eps) * gaussian_iterated_expectation N paper_main_gaussian_norm -
    paper_main_gordon_width M v (List.seq 0 s) <=
  gaussian_iterated_expectation (M * N) (fun ys => finite_minimax
    (fun t y => paper_main_gordon_matrix_value M N (v t) (z y) ys)
    (List.seq 0 s) (List.seq 0 r)).
Proof.
intros Hs Hr HN He Hv Hznet.
assert (Hz : forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1).
{ intros y Hy; apply (proj1 Hznet); apply in_seq; lia. }
destruct (paper_main_gordon_matrix_comparison s r M N v z Hs Hr Hv Hz) as [HD [HQ HC]].
pose proof (paper_main_gordon_escape_seq_nonempty s Hs) as HS.
assert (HV : forall t, In t (List.seq 0 s) -> paper_main_gordon_dot M (v t) (v t) = 1).
{ intros t Ht; apply Hv; apply in_seq_lt; exact Ht. }
pose proof (paper_main_gordon_support_continuous M v (List.seq 0 s)) as HSc.
pose proof (paper_main_gordon_escape_support_bound M v (List.seq 0 s) HS HV) as HSb.
pose proof (paper_main_gaussian_neg_continuous M _ HSc) as HNc.
pose proof (paper_main_gaussian_neg_polynomial_bound M _ _ _ HSb) as HNb.
destruct (gaussian_coordinate_polynomial_domain M _ _ _ HNc HNb) as [HNI _].
pose proof (paper_main_gaussian_iterated_reflect M _ _ _ HSc HSb) as HRefl.
destruct (gaussian_iterated_prefix_lift M N _ HNI) as [HPI HPE].
destruct (gaussian_iterated_suffix_lift M N paper_main_gaussian_norm
  (proj1 (paper_main_gaussian_norm_domain N))) as [HSI HSE].
destruct (gaussian_iterated_scale (M + N) _ (-1) HPI) as [HI1 HE1].
destruct (gaussian_iterated_scale (M + N) _ (1 - eps) HSI) as [HI2 HE2].
destruct (gaussian_iterated_add (M + N) _ _ HI1 HI2) as [HI3 HE3].
pose proof (gaussian_iterated_monotone (M + N) _ _ HI3 (proj1 HQ)
  (fun zs Hzs => paper_main_gordon_escape_auxiliary_lower s r N M v z eps zs
    Hs Hr HN He Hzs Hznet)) as HM.
rewrite HE3, HE1, HE2, HPE, HSE, HRefl in HM.
unfold paper_main_gordon_width; lra.
Qed.

(* The finite statistic is 1-Lipschitz, hence regular. *)

Lemma paper_main_gordon_escape_minimax_le (H H' : nat -> nat -> R) Y S L :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> H y s <= H' y s + L) ->
  finite_minimax H Y S <= finite_minimax H' Y S + L.
Proof.
intros HY HS Hle; unfold finite_minimax.
destruct (finite_min_attained (fun y => finite_max (H' y) S) Y HY) as [y0 [Hy0 He]].
rewrite He.
apply (Rle_trans _ (finite_max (H y0) S)).
- apply (finite_min_member (fun y => finite_max (H y) S) Y y0 Hy0).
- apply (finite_max_upper (H y0) S); [exact HS|].
  intros s Hs.
  pose proof (Hle y0 s Hy0 Hs).
  pose proof (finite_max_member (H' y0) S s Hs).
  lra.
Qed.

Theorem paper_main_gordon_escape_finite_lipschitz s r N M v z :
  (0 < s)%nat -> (0 < r)%nat ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  forall ys ys', List.length ys = (M * N)%nat -> List.length ys' = (M * N)%nat ->
    Rabs (finite_minimax (fun t y => paper_main_gordon_matrix_value M N (v t) (z y) ys)
            (List.seq 0 s) (List.seq 0 r) -
          finite_minimax (fun t y => paper_main_gordon_matrix_value M N (v t) (z y) ys')
            (List.seq 0 s) (List.seq 0 r)) <=
      1 * paper_main_gordon_distance (M * N) ys ys'.
Proof.
intros Hs Hr Hv Hz ys ys' _ _.
pose proof (paper_main_gordon_escape_seq_nonempty s Hs) as HS.
pose proof (paper_main_gordon_escape_seq_nonempty r Hr) as HY.
assert (Hle : forall a b,
  finite_minimax (fun t y => paper_main_gordon_matrix_value M N (v t) (z y) a)
    (List.seq 0 s) (List.seq 0 r) <=
  finite_minimax (fun t y => paper_main_gordon_matrix_value M N (v t) (z y) b)
    (List.seq 0 s) (List.seq 0 r) + paper_main_gordon_distance (M * N) a b).
{ intros a b; apply paper_main_gordon_escape_minimax_le; [exact HS|exact HY|].
  intros t y Ht Hy; apply in_seq in Ht; apply in_seq in Hy.
  pose proof (paper_main_gordon_matrix_value_lipschitz M N (v t) (z y) a b
    (Hv t ltac:(lia)) (Hz y ltac:(lia))) as H.
  pose proof (Rle_abs (paper_main_gordon_matrix_value M N (v t) (z y) a -
    paper_main_gordon_matrix_value M N (v t) (z y) b)); lra. }
pose proof (Hle ys ys') as H1.
pose proof (Hle ys' ys) as H2.
rewrite (paper_main_gordon_distance_symmetric (M * N) ys' ys) in H2.
apply Rabs_le; split; lra.
Qed.

Theorem paper_main_gordon_escape_finite_regular s r N M v z :
  (0 < s)%nat -> (0 < r)%nat ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  finite_joint_continuous (M * N) (fun ys => finite_minimax
    (fun t y => paper_main_gordon_matrix_value M N (v t) (z y) ys)
    (List.seq 0 s) (List.seq 0 r)) /\
  exists C, finite_polynomial_bound (M * N) C 2 (fun ys => finite_minimax
    (fun t y => paper_main_gordon_matrix_value M N (v t) (z y) ys)
    (List.seq 0 s) (List.seq 0 r)).
Proof.
intros Hs Hr Hv Hz.
pose proof (paper_main_gordon_escape_finite_lipschitz s r N M v z Hs Hr Hv Hz) as HL.
split; [exact (paper_main_gaussian_lipschitz_continuous _ _ 1 Rle_0_1 HL)|].
eexists; exact (paper_main_gaussian_lipschitz_polynomial_bound _ _ 1 Rle_0_1 HL).
Qed.

(* From the transposed convention back to the N-by-M matrix. *)

Lemma paper_main_gordon_matrix_value_transpose N M u v xs :
  paper_main_gordon_matrix_value M N v u (paper_main_gordon_transpose N M xs) =
  paper_main_gordon_matrix_value N M u v xs.
Proof.
unfold paper_main_gordon_matrix_value.
transitivity (finite_sum (fun i => finite_sum (fun j =>
  v j * u i * List.nth (j * N + i)%nat (paper_main_gordon_transpose N M xs) 0)
  (List.seq 0 M)) (List.seq 0 N)).
- apply (finite_sum_swap (fun j i =>
    v j * u i * List.nth (j * N + i)%nat (paper_main_gordon_transpose N M xs) 0)).
- apply finite_sum_ext; intros i Hi; apply in_seq in Hi.
  apply finite_sum_ext; intros j Hj; apply in_seq in Hj.
  rewrite paper_main_gordon_transpose_nth by lia; ring.
Qed.

Lemma paper_main_gordon_escape_net_lower s r N M T v z eps xs :
  (0 < N)%nat -> (0 < s)%nat -> (0 < r)%nat -> 0 <= eps ->
  List.length xs = (N * M)%nat ->
  (exists u, T u) -> (forall u, T u -> paper_main_gordon_dot M u u = 1) ->
  paper_main_gordon_finite_net M T v (List.seq 0 s) eps ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  finite_minimax (fun t y => paper_main_gordon_matrix_value M N (v t) (z y)
      (paper_main_gordon_transpose N M xs)) (List.seq 0 s) (List.seq 0 r) -
    eps * paper_main_gaussian_norm xs <=
  paper_main_gordon_escape N M T xs.
Proof.
intros HN Hs Hr He Hxs HT HU Hnet Hz.
pose proof (paper_main_gordon_escape_seq_nonempty r Hr) as HY.
apply paper_main_gordon_escape_ge; [exact HT|].
intros u Hu.
destruct (proj2 Hnet u Hu) as [t [Ht Hdt]].
assert (H1 : finite_minimax (fun t y => paper_main_gordon_matrix_value M N (v t) (z y)
      (paper_main_gordon_transpose N M xs)) (List.seq 0 s) (List.seq 0 r) <=
    finite_max (fun y => paper_main_gordon_matrix_value N M (z y) (v t) xs) (List.seq 0 r)).
{ unfold finite_minimax.
  eapply Rle_trans; [exact (finite_min_member (fun t => finite_max
    (fun y => paper_main_gordon_matrix_value M N (v t) (z y)
      (paper_main_gordon_transpose N M xs)) (List.seq 0 r)) (List.seq 0 s) t Ht)|].
  apply Req_le; apply paper_main_gordon_finite_max_ext; intros y _.
  apply paper_main_gordon_matrix_value_transpose. }
assert (H2 : finite_max (fun y => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) <=
  paper_main_gordon_escape_norm N M u xs + eps * paper_main_gaussian_norm xs).
{ apply finite_max_upper; [exact HY|].
  intros y Hy; apply in_seq in Hy.
  pose proof (Hz y ltac:(lia)) as Hzy.
  assert (Hzy1 : paper_main_gordon_dot N (z y) (z y) <= 1 ^ 2) by (rewrite Hzy; lra).
  pose proof (paper_main_gordon_bilinear_right_error N M xs (paper_main_gaussian_norm xs)
    (z y) u (v t) 1 eps (paper_main_gordon_operator_frobenius N M xs Hxs) Rle_0_1 He
    Hzy1 Hdt) as Herr.
  pose proof (paper_main_gordon_escape_dot_le N M (z y) u xs Hzy) as Hc.
  pose proof (Rle_abs (paper_main_gordon_matrix_value N M (z y) (v t) xs -
    paper_main_gordon_matrix_value N M (z y) u xs)) as Ha.
  rewrite Rabs_minus_sym in Ha.
  lra. }
lra.
Qed.

(* The expectation bound. *)

Theorem paper_main_gordon_escape_expectation N M T :
  (0 < N)%nat -> (exists v, T v) ->
  (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  gaussian_iterated_expectation N paper_main_gaussian_norm -
    paper_main_gordon_set_width M T <=
  gaussian_iterated_expectation (N * M) (paper_main_gordon_escape N M T).
Proof.
intros HN HT HU.
destruct (paper_main_gordon_escape_domain N M T HN HT HU) as [HIe _].
destruct (gaussian_coordinate_polynomial_domain (N * M) paper_main_gaussian_norm
  (1 + INR (N * M)) 2 (paper_main_gaussian_norm_continuous (N * M))
  (paper_main_gaussian_norm_polynomial (N * M))) as [HIn _].
destruct (paper_main_gaussian_norm_expectation N) as [HEN0 _].
destruct (paper_main_gaussian_norm_expectation (N * M)) as [HEn0 _].
apply (paper_main_gordon_le_of_forall_eps _ _
  (gaussian_iterated_expectation N paper_main_gaussian_norm +
    gaussian_iterated_expectation (N * M) paper_main_gaussian_norm)); [lra|].
intros eps Heps.
destruct (paper_main_gordon_finite_net_exists M T eps Heps HT HU) as [s [v [Hs Hnet]]].
destruct (paper_main_gordon_finite_net_exists N
  (fun u => paper_main_gordon_dot N u u = 1) eps Heps
  (paper_main_gordon_unit_sphere_nonempty N HN) (fun u Hu => Hu)) as [r [z [Hr Hznet]]].
assert (Hz : forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1).
{ intros y Hy; apply (proj1 Hznet); apply in_seq; lia. }
assert (Hv : forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1).
{ intros t Ht; apply HU; apply (proj1 Hnet); apply in_seq; lia. }
pose proof (paper_main_gordon_escape_finite_margin s r N M v z eps Hs Hr HN
  (Rlt_le _ _ Heps) Hv Hznet) as Hfin.
destruct (paper_main_gordon_net_width_error M T v (List.seq 0 s) eps
  (Rlt_le _ _ Heps) HT HU Hnet) as [Hwe _].
destruct (paper_main_gordon_escape_finite_regular s r N M v z Hs Hr Hv Hz) as [HGc [CG HGb]].
pose proof (paper_main_gordon_transpose_expectation N M _ CG 2 HN HGc HGb) as Htr.
destruct (paper_main_gordon_transpose_regular N M _ CG 2 HN HGc HGb) as [HGtc HGtb].
destruct (gaussian_coordinate_polynomial_domain (N * M) _ CG 2 HGtc HGtb) as [HIG _].
destruct (gaussian_iterated_scale (N * M) paper_main_gaussian_norm eps HIn) as [HIs HEs].
destruct (gaussian_iterated_difference (N * M) _
  (fun xs => eps * paper_main_gaussian_norm xs) HIG HIs) as [HId HEd].
pose proof (gaussian_iterated_monotone (N * M) _ (paper_main_gordon_escape N M T) HId HIe
  (fun xs Hxs => paper_main_gordon_escape_net_lower s r N M T v z eps xs HN Hs Hr
    (Rlt_le _ _ Heps) Hxs HT HU Hnet Hz)) as Hmono.
rewrite HEd, HEs, Htr in Hmono.
lra.
Qed.
