(* Gordon's expectation bound for the genuine set-index min-max. For N > 0
   and a nonempty set T of unit vectors of R^M,
     w(T) - E ||g_N|| <= E minmax_T(A),
   where w(T) is the Gaussian width of T (a genuine supremum), g_N is a
   standard Gaussian vector of R^N, and A is an N x M standard Gaussian
   matrix. The exact Gaussian norm mean is kept; the sqrt N form follows.
   The proof uses the checked finite comparison through a new exact-mean
   helper, finite nets inside T and inside the unit sphere, and the
   Frobenius bound for the bilinear error; it needs no compactness of T and
   assumes no attained extremum. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality Epsilon.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateSteinDomains
  GaussianFiniteSums GaussianCovarianceDefinitions GaussianCovarianceSums
  MaximumRadiusMoments GaussianExpectationContinuity PaperMainGordonFinite PaperMainGordonProcessCovariance
  PaperMainGordonProcesses PaperMainGordonScalar PaperMainGaussianNorm
  PaperMainGordonWidth PaperMainGordonSetWidth PaperMainGordonNets
  PaperMainGordonNetExistence PaperMainGordonBilinear PaperMainGordonNetToAll
  PaperMainGordonOperatorNet PaperMainGordonCompactMinmax.
Import ListNotations.
Open Scope R_scope.

(* The argument of paper_main_gordon_finite_width_margin, stopped before
   its final bound E ||g_N|| <= sqrt N, so the exact mean is kept. *)
Theorem paper_main_gordon_compact_finite_exact_margin r s N M z v :
  (0 < r)%nat -> (0 < s)%nat ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  paper_main_gordon_width M v (List.seq 0 s) -
    gaussian_iterated_expectation N paper_main_gaussian_norm <=
  gaussian_iterated_expectation (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs Hz Hv.
destruct (paper_main_gordon_matrix_comparison r s N M z v Hr Hs Hz Hv) as [HD [HQ HC]].
assert (HY : List.seq 0 r <> []).
{ intro H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HS : List.seq 0 s <> []).
{ intro H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HV : forall t, In t (List.seq 0 s) -> paper_main_gordon_dot M (v t) (v t) = 1).
{ intros t Ht; apply Hv; apply in_seq_lt; exact Ht. }
assert (HZ : forall y, In y (List.seq 0 r) -> paper_main_gordon_dot N (z y) (z y) = 1).
{ intros y Hy; apply Hz; apply in_seq_lt; exact Hy. }
destruct (gaussian_iterated_prefix_lift N M paper_main_gaussian_norm
  (proj1 (paper_main_gaussian_norm_domain N))) as [HNI HNE].
destruct (gaussian_iterated_suffix_lift N M (paper_main_gordon_support M v (List.seq 0 s))
  (proj1 (paper_main_gordon_support_domain M v (List.seq 0 s) HS HV))) as [HSI HSE].
destruct (gaussian_iterated_scale (N + M)
  (fun xs => paper_main_gaussian_norm (List.firstn N xs)) (-1) HNI) as [Hneg HnegE].
destruct (gaussian_iterated_add (N + M)
  (fun xs => paper_main_gordon_support M v (List.seq 0 s) (List.skipn N xs))
  (fun xs => -1 * paper_main_gaussian_norm (List.firstn N xs)) HSI Hneg) as [HG HGE].
pose proof (gaussian_iterated_monotone (N + M)
  (fun xs => paper_main_gordon_support M v (List.seq 0 s) (List.skipn N xs) +
    -1 * paper_main_gaussian_norm (List.firstn N xs))
  (fun xs => finite_minimax (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) HG (proj1 HQ)
  ltac:(intros xs Hxs; pose proof (paper_main_gordon_auxiliary_lower N M z v
    (List.seq 0 r) (List.seq 0 s) xs HY HS Hxs HZ); lra)) as HM.

rewrite HGE in HM; rewrite HnegE in HM; rewrite HNE in HM; rewrite HSE in HM.
unfold paper_main_gordon_width; lra.
Qed.

Lemma paper_main_gordon_le_of_forall_eps (a b c : R) :
  0 <= c -> (forall eps, 0 < eps -> a - eps * c <= b) -> a <= b.
Proof.
intros Hc H; apply Rnot_lt_le; intros Hlt.
assert (Hpos : 0 < (a - b) / (2 * (c + 1))) by (apply Rdiv_lt_0_compat; lra).
specialize (H _ Hpos).
assert (Hlt2 : (a - b) / (2 * (c + 1)) * c < a - b).
{ apply (Rmult_lt_reg_r (2 * (c + 1))); [lra|].
  replace ((a - b) / (2 * (c + 1)) * c * (2 * (c + 1))) with ((a - b) * c)
    by (field; lra).
  nra. }
lra.
Qed.

Theorem paper_main_gordon_compact_expectation N M T :
  (0 < N)%nat -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot M u u = 1) ->
  paper_main_gordon_set_width M T -
    gaussian_iterated_expectation N paper_main_gaussian_norm <=
  gaussian_iterated_expectation (N * M) (paper_main_gordon_compact_minmax N M T).
Proof.
intros HN HT HU.
destruct (paper_main_gordon_compact_minmax_domain N M T HN HT HU) as [HIm _].
destruct (gaussian_coordinate_polynomial_domain (N * M) paper_main_gaussian_norm
  (1 + INR (N * M)) 2 (paper_main_gaussian_norm_continuous (N * M))
  (paper_main_gaussian_norm_polynomial (N * M))) as [HIn _].
destruct (paper_main_gaussian_norm_expectation (N * M)) as [HEn0 _].
apply (paper_main_gordon_le_of_forall_eps _ _
  (sqrt (INR M) + gaussian_iterated_expectation (N * M) paper_main_gaussian_norm)).
{ pose proof (sqrt_pos (INR M)); lra. }
intros eps Heps.
destruct (paper_main_gordon_finite_net_exists M T eps Heps HT HU) as [s [v [Hs Hnet]]].
destruct (paper_main_gordon_finite_net_exists N
  (fun u => paper_main_gordon_dot N u u = 1) eps Heps
  (paper_main_gordon_unit_sphere_nonempty N HN) (fun u Hu => Hu)) as [r [z [Hr Hznet]]].
assert (Hz : forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1).
{ intros y Hy; apply (proj1 Hznet); apply in_seq; lia. }
assert (Hv : forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1).
{ intros t Ht; apply HU; apply (proj1 Hnet); apply in_seq; lia. }
destruct (paper_main_gordon_finite_width_margin r s N M z v Hr Hs Hz Hv) as [HD _].
pose proof (paper_main_gordon_compact_finite_exact_margin r s N M z v Hr Hs Hz Hv) as Hex.
destruct (paper_main_gordon_net_width_error M T v (List.seq 0 s) eps
  (Rlt_le _ _ Heps) HT HU Hnet) as [_ Hwe].
assert (HS : List.seq 0 s <> []).
{ intro H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H;
    simpl in H; lia. }
assert (Hpt : forall xs, List.length xs = (N * M)%nat ->
  finite_minimax (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s) - eps * paper_main_gaussian_norm xs <=
  paper_main_gordon_compact_minmax N M T xs).
{ intros xs Hxs.
  apply paper_main_gordon_compact_minmax_ge; [exact HN|exact Hxs|exact HT|exact HU|].
  intros u Hu.
  destruct (proj2 Hznet u Hu) as [y [Hy Hdy]].
  assert (H1 : finite_minimax (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
      (List.seq 0 r) (List.seq 0 s) <=
    finite_max (fun t => paper_main_gordon_matrix_value N M (z y) (v t) xs) (List.seq 0 s)).
  { unfold finite_minimax.
    exact (finite_min_member (fun y0 => finite_max
      (fun t => paper_main_gordon_matrix_value N M (z y0) (v t) xs) (List.seq 0 s))
      (List.seq 0 r) y Hy). }
  assert (H2 : finite_max (fun t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
      (List.seq 0 s) <=
    paper_main_gordon_compact_inner N M T u xs + eps * paper_main_gaussian_norm xs).
  { apply finite_max_upper; [exact HS|].
    intros t Ht.
    assert (Hvt : T (v t)) by (apply (proj1 Hnet); exact Ht).
    assert (Hv1 : paper_main_gordon_dot M (v t) (v t) <= 1 ^ 2)
      by (rewrite (HU _ Hvt); lra).
    pose proof (paper_main_gordon_bilinear_left_error N M xs (paper_main_gaussian_norm xs)
      u (z y) (v t) eps 1 (paper_main_gordon_operator_frobenius N M xs Hxs)
      (Rlt_le _ _ Heps) Rle_0_1 Hdy Hv1) as He.
    pose proof (paper_main_gordon_compact_inner_member N M T u (v t) xs Hxs Hu HU Hvt)
      as Hm.
    pose proof (Rle_abs (paper_main_gordon_matrix_value N M (z y) (v t) xs -
      paper_main_gordon_matrix_value N M u (v t) xs)) as Ha.
    rewrite Rabs_minus_sym in Ha.
    lra. }
  lra. }
destruct (gaussian_iterated_scale (N * M) paper_main_gaussian_norm eps HIn) as [HIs HEs].
destruct (gaussian_iterated_difference (N * M)
  (fun xs => finite_minimax (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s))
  (fun xs => eps * paper_main_gaussian_norm xs) (proj1 HD) HIs) as [HId HEd].
pose proof (gaussian_iterated_monotone (N * M) _
  (paper_main_gordon_compact_minmax N M T) HId HIm Hpt) as Hmono.
rewrite HEd in Hmono; rewrite HEs in Hmono.
lra.
Qed.

Corollary paper_main_gordon_compact_expectation_sqrt N M T :
  (0 < N)%nat -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot M u u = 1) ->
  paper_main_gordon_set_width M T - sqrt (INR N) <=
  gaussian_iterated_expectation (N * M) (paper_main_gordon_compact_minmax N M T).
Proof.
intros HN HT HU.
pose proof (paper_main_gordon_compact_expectation N M T HN HT HU) as H.
destruct (paper_main_gaussian_norm_expectation N) as [_ HNs].
lra.
Qed.
