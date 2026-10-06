(* The escape statistic of Gordon's escape through the mesh. An N-by-M
   matrix A is given by its row-major list coordinates xs: entry (i, j) is
   at position i*M + j, as in paper_main_gordon_matrix_value. For a vector v
   of R^M, paper_main_gordon_escape_image N M v xs is A v and
   paper_main_gordon_escape_norm N M v xs is ||A v||. For a nonempty set T
   of unit vectors of R^M, paper_main_gordon_escape N M T xs is
   inf_(v in T) ||A v||, a genuine infimum chosen by epsilon and
   characterized by completeness. No minimizer is assumed. For N > 0 the
   norm is attained by a unit vector z, so ||A v|| = max_(z unit) z^T A v.
   The statistic is 1-Lipschitz for the coordinate (Frobenius) distance,
   bounded by the Frobenius norm, jointly continuous and Gaussian
   integrable. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gaussian.Iterated.Definitions
  Gaussian.Iterated.Expectation Gaussian.Iterated.PolynomialDomain
  Gaussian.Coordinate.Weights Analysis.FiniteSumAlgebra
  Gordon.ProcessCovariance Gordon.Scalar Gordon.Lipschitz Gordon.Bilinear
  Gordon.NetToAll Gordon.OperatorNet Gordon.OperatorContinuity
  Gaussian.Lipschitz.EuclideanNorm Gaussian.Smooth.Calculus
  Gaussian.Lipschitz.Clip Gordon.UnitValueBound.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_escape_image (N M : nat) (v : nat -> R) (xs : list R) (i : nat) : R :=
  finite_sum (fun j => v j * List.nth (i * M + j)%nat xs 0) (List.seq 0 M).

Definition paper_main_gordon_escape_norm N M (v : nat -> R) (xs : list R) : R :=
  euclidean_norm (paper_main_gordon_escape_image N M v xs) (List.seq 0 N).

Definition paper_main_gordon_escape N M (T : (nat -> R) -> Prop) (xs : list R) : R :=
  - epsilon (inhabits 0) (fun b => is_lub
    (fun a => exists v, T v /\ a = - paper_main_gordon_escape_norm N M v xs) b).

(* The norm of A v and its dual form. *)

Lemma paper_main_gordon_escape_matrix_value N M z v xs :
  paper_main_gordon_matrix_value N M z v xs =
    paper_main_gordon_dot N z (paper_main_gordon_escape_image N M v xs).
Proof.
unfold paper_main_gordon_matrix_value, paper_main_gordon_dot, paper_main_gordon_escape_image.
apply finite_sum_ext; intros i _.
rewrite <- finite_sum_scale; apply finite_sum_ext; intros j _; ring.
Qed.

Lemma paper_main_gordon_escape_norm_nonnegative N M v xs :
  0 <= paper_main_gordon_escape_norm N M v xs.
Proof. unfold paper_main_gordon_escape_norm, euclidean_norm; apply sqrt_pos. Qed.

Lemma paper_main_gordon_escape_dot_le N M z v xs :
  paper_main_gordon_dot N z z = 1 ->
  paper_main_gordon_matrix_value N M z v xs <= paper_main_gordon_escape_norm N M v xs.
Proof.
intros Hz.
rewrite paper_main_gordon_escape_matrix_value.
pose proof (paper_main_gordon_sum_cauchy z (paper_main_gordon_escape_image N M v xs)
  (List.seq 0 N)) as HC.
assert (Hz2 : finite_sum (fun i => z i ^ 2) (List.seq 0 N) = 1).
{ rewrite <- Hz; unfold paper_main_gordon_dot; apply finite_sum_ext; intros; ring. }
rewrite Hz2, Rmult_1_l in HC.
apply (Rle_trans _ (Rabs (paper_main_gordon_dot N z (paper_main_gordon_escape_image N M v xs))));
  [apply Rle_abs|].
unfold paper_main_gordon_escape_norm, euclidean_norm, squared_norm.
rewrite <- sqrt_Rsqr_abs; apply sqrt_le_1_alt; rewrite Rsqr_pow2; exact HC.
Qed.

Theorem paper_main_gordon_escape_vector_attained N (w : nat -> R) :
  (0 < N)%nat ->
  exists z, paper_main_gordon_dot N z z = 1 /\
    paper_main_gordon_dot N z w = euclidean_norm w (List.seq 0 N).
Proof.
intros HN.
set (S := finite_sum (fun i => w i ^ 2) (List.seq 0 N)).
assert (HS : 0 <= S) by (apply finite_sum_nonneg; intros; apply pow2_ge_0).
assert (Hr : euclidean_norm w (List.seq 0 N) = sqrt S) by reflexivity.
destruct (Req_dec S 0) as [HS0|HS0].
- destruct (paper_main_gordon_unit_sphere_nonempty N HN) as [z Hz].
  exists z; split; [exact Hz|].
  rewrite Hr, HS0, sqrt_0.
  pose proof (paper_main_gordon_sum_cauchy z w (List.seq 0 N)) as HC.
  change (finite_sum (fun i => w i ^ 2) (List.seq 0 N)) with S in HC.
  rewrite HS0, Rmult_0_r in HC.
  unfold paper_main_gordon_dot; nra.
- assert (HSp : 0 < S) by lra.
  set (r := sqrt S).
  assert (Hrp : 0 < r) by (apply sqrt_lt_R0; exact HSp).
  assert (Hr2 : r * r = S) by (apply sqrt_sqrt; lra).
  exists (fun i => w i / r); split.
  + unfold paper_main_gordon_dot.
    transitivity (finite_sum (fun i => / (r * r) * w i ^ 2) (List.seq 0 N)).
    * apply finite_sum_ext; intros i _; field; lra.
    * rewrite finite_sum_scale; fold S; rewrite <- Hr2; field; lra.
  + rewrite Hr; fold r.
    unfold paper_main_gordon_dot.
    transitivity (finite_sum (fun i => / r * w i ^ 2) (List.seq 0 N)).
    * apply finite_sum_ext; intros i _; field; lra.
    * rewrite finite_sum_scale; fold S; rewrite <- Hr2; field; lra.
Qed.

Theorem paper_main_gordon_escape_norm_attained N M v xs :
  (0 < N)%nat ->
  exists z, paper_main_gordon_dot N z z = 1 /\
    paper_main_gordon_matrix_value N M z v xs = paper_main_gordon_escape_norm N M v xs.
Proof.
intros HN.
destruct (paper_main_gordon_escape_vector_attained N
  (paper_main_gordon_escape_image N M v xs) HN) as [z [Hz Hzw]].
exists z; split; [exact Hz|].
rewrite paper_main_gordon_escape_matrix_value; exact Hzw.
Qed.

Lemma paper_main_gordon_escape_norm_bound N M v xs :
  (0 < N)%nat -> List.length xs = (N * M)%nat -> paper_main_gordon_dot M v v = 1 ->
  paper_main_gordon_escape_norm N M v xs <= paper_main_gaussian_norm xs.
Proof.
intros HN Hxs Hv.
destruct (paper_main_gordon_escape_norm_attained N M v xs HN) as [z [Hz HE]].
rewrite <- HE.
pose proof (paper_main_gordon_unit_matrix_value_bound N M z v xs Hxs Hz Hv) as H.
pose proof (Rle_abs (paper_main_gordon_matrix_value N M z v xs)); lra.
Qed.

Lemma paper_main_gordon_escape_norm_lipschitz N M v xs ys :
  (0 < N)%nat -> paper_main_gordon_dot M v v = 1 ->
  paper_main_gordon_escape_norm N M v xs <=
    paper_main_gordon_escape_norm N M v ys + paper_main_gordon_distance (N * M) xs ys.
Proof.
intros HN Hv.
destruct (paper_main_gordon_escape_norm_attained N M v xs HN) as [z [Hz HE]].
rewrite <- HE.
pose proof (paper_main_gordon_matrix_value_lipschitz N M z v xs ys Hz Hv) as H1.
pose proof (paper_main_gordon_escape_dot_le N M z v ys Hz) as H2.
pose proof (Rle_abs (paper_main_gordon_matrix_value N M z v xs -
  paper_main_gordon_matrix_value N M z v ys)); lra.
Qed.

(* The genuine infimum over T. *)

Lemma paper_main_gordon_escape_lub N M T xs :
  (exists v, T v) ->
  is_lub (fun a => exists v, T v /\ a = - paper_main_gordon_escape_norm N M v xs)
    (- paper_main_gordon_escape N M T xs).
Proof.
intros HT; unfold paper_main_gordon_escape; rewrite Ropp_involutive.
apply epsilon_spec.
assert (HB : bound (fun a => exists v, T v /\ a = - paper_main_gordon_escape_norm N M v xs)).
{ exists 0; intros a [v [Hv ->]].
  pose proof (paper_main_gordon_escape_norm_nonnegative N M v xs); lra. }
assert (HNe : exists a, exists v, T v /\ a = - paper_main_gordon_escape_norm N M v xs).
{ destruct HT as [v Hv]; exists (- paper_main_gordon_escape_norm N M v xs); exists v; auto. }
destruct (completeness _ HB HNe) as [b Hb]; exists b; exact Hb.
Qed.

Theorem paper_main_gordon_escape_le N M T v xs :
  T v -> paper_main_gordon_escape N M T xs <= paper_main_gordon_escape_norm N M v xs.
Proof.
intros Hv.
destruct (paper_main_gordon_escape_lub N M T xs (ex_intro _ v Hv)) as [Hup _].
assert (H : - paper_main_gordon_escape_norm N M v xs <= - paper_main_gordon_escape N M T xs)
  by (apply Hup; exists v; auto).
lra.
Qed.

Theorem paper_main_gordon_escape_ge N M T xs c :
  (exists v, T v) ->
  (forall v, T v -> c <= paper_main_gordon_escape_norm N M v xs) ->
  c <= paper_main_gordon_escape N M T xs.
Proof.
intros HT Hc.
destruct (paper_main_gordon_escape_lub N M T xs HT) as [_ Hleast].
assert (H : - paper_main_gordon_escape N M T xs <= - c).
{ apply Hleast; intros a [v [Hv ->]]; pose proof (Hc v Hv); lra. }
lra.
Qed.

Lemma paper_main_gordon_escape_nonnegative N M T xs :
  (exists v, T v) -> 0 <= paper_main_gordon_escape N M T xs.
Proof.
intros HT; apply paper_main_gordon_escape_ge; [exact HT|].
intros v _; apply paper_main_gordon_escape_norm_nonnegative.
Qed.

Theorem paper_main_gordon_escape_abs N M T xs :
  (0 < N)%nat -> List.length xs = (N * M)%nat ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  Rabs (paper_main_gordon_escape N M T xs) <= paper_main_gaussian_norm xs.
Proof.
intros HN Hxs HT HU.
pose proof (paper_main_gordon_escape_nonnegative N M T xs HT) as H0.
rewrite Rabs_pos_eq by exact H0.
destruct HT as [v Hv].
pose proof (paper_main_gordon_escape_le N M T v xs Hv) as H1.
pose proof (paper_main_gordon_escape_norm_bound N M v xs HN Hxs (HU v Hv)) as H2.
lra.
Qed.

(* Lipschitz bound, continuity and Gaussian domain. *)

Theorem paper_main_gordon_escape_lipschitz N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  forall xs ys, List.length xs = (N * M)%nat -> List.length ys = (N * M)%nat ->
    Rabs (paper_main_gordon_escape N M T xs - paper_main_gordon_escape N M T ys) <=
      1 * paper_main_gordon_distance (N * M) xs ys.
Proof.
intros HN HT HU xs ys Hxs Hys.
assert (Hone : forall ps qs,
  paper_main_gordon_escape N M T ps - paper_main_gordon_distance (N * M) ps qs <=
    paper_main_gordon_escape N M T qs).
{ intros ps qs.
  apply paper_main_gordon_escape_ge; [exact HT|].
  intros v Hv.
  pose proof (paper_main_gordon_escape_le N M T v ps Hv) as H1.
  pose proof (paper_main_gordon_escape_norm_lipschitz N M v ps qs HN (HU v Hv)) as H2.
  lra. }
pose proof (Hone xs ys) as H1.
pose proof (Hone ys xs) as H2.
rewrite (paper_main_gordon_distance_symmetric (N * M) ys xs) in H2.
apply Rabs_le; split; lra.
Qed.

Theorem paper_main_gordon_escape_continuous N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  finite_joint_continuous (N * M) (paper_main_gordon_escape N M T).
Proof.
intros HN HT HU.
exact (paper_main_gaussian_lipschitz_continuous (N * M) _ 1 Rle_0_1
  (paper_main_gordon_escape_lipschitz N M T HN HT HU)).
Qed.

Theorem paper_main_gordon_escape_polynomial_bound N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  finite_polynomial_bound (N * M) (1 + INR (N * M)) 2 (paper_main_gordon_escape N M T).
Proof.
intros HN HT HU.
destruct (paper_main_gaussian_norm_polynomial (N * M)) as [HC Hn].
split; [exact HC|].
intros xs Hxs.
pose proof (paper_main_gordon_escape_abs N M T xs HN Hxs HT HU) as H1.
pose proof (Hn xs Hxs) as H2.
pose proof (Rle_abs (paper_main_gaussian_norm xs)); lra.
Qed.

Theorem paper_main_gordon_escape_domain N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  gaussian_iterated_integrable (N * M) (paper_main_gordon_escape N M T) /\
  gaussian_iterated_absolutely_integrable (N * M) (paper_main_gordon_escape N M T).
Proof.
intros HN HT HU.
destruct (gaussian_coordinate_polynomial_domain (N * M) _ _ 2
  (paper_main_gordon_escape_continuous N M T HN HT HU)
  (paper_main_gordon_escape_polynomial_bound N M T HN HT HU)) as [HI [HA _]].
split; [exact HI|exact HA].
Qed.
