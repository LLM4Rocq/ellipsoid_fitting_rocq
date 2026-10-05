(* The genuine set-index Gordon min-max. For a matrix A given by its
   N*M list coordinates and a nonempty set T of unit vectors of R^M,
   minmax(A) is the infimum over the unit sphere of R^N of the supremum
   over T of z^T A v. Both extrema are genuine least upper bounds chosen by
   epsilon; their existence is proved by completeness from the Frobenius
   bound, and no extremum is assumed attained. For N > 0, minmax is
   1-Lipschitz in A for the Euclidean (Frobenius) distance, jointly
   continuous and Gaussian integrable. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateSteinDomains GaussianCoordinateWeights GaussianCovarianceSums
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonLipschitz
  PaperMainGordonBilinear PaperMainGordonNetToAll PaperMainGordonOperatorNet
  PaperMainGordonOperatorContinuity
  PaperMainGaussianNorm PaperMainGaussianSmoothCalculus PaperMainGaussianLipschitzClip.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_compact_inner N M (T : (nat -> R) -> Prop)
    (u : nat -> R) (xs : list R) : R :=
  epsilon (inhabits 0) (fun b => is_lub
    (fun a => exists v, T v /\ a = paper_main_gordon_matrix_value N M u v xs) b).

Definition paper_main_gordon_compact_minmax N M (T : (nat -> R) -> Prop)
    (xs : list R) : R :=
  - epsilon (inhabits 0) (fun b => is_lub
    (fun a => exists u, paper_main_gordon_dot N u u = 1 /\
       a = - paper_main_gordon_compact_inner N M T u xs) b).

Lemma paper_main_gordon_unit_matrix_value_bound N M u v xs :
  List.length xs = (N * M)%nat ->
  paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M v v = 1 ->
  Rabs (paper_main_gordon_matrix_value N M u v xs) <= paper_main_gaussian_norm xs.
Proof.
intros Hxs Hu Hv.
assert (Hu1 : paper_main_gordon_dot N u u <= 1 ^ 2) by (rewrite Hu; lra).
assert (Hv1 : paper_main_gordon_dot M v v <= 1 ^ 2) by (rewrite Hv; lra).
pose proof (paper_main_gordon_bilinear_ball_bound N M xs (paper_main_gaussian_norm xs)
  u v 1 1 (paper_main_gordon_operator_frobenius N M xs Hxs) Rle_0_1 Rle_0_1 Hu1 Hv1) as H.
lra.
Qed.

Lemma paper_main_gordon_compact_inner_lub N M T u xs :
  List.length xs = (N * M)%nat -> paper_main_gordon_dot N u u = 1 ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  is_lub (fun a => exists v, T v /\ a = paper_main_gordon_matrix_value N M u v xs)
    (paper_main_gordon_compact_inner N M T u xs).
Proof.
intros Hxs Hu HT HU; unfold paper_main_gordon_compact_inner.
apply epsilon_spec.
assert (HB : bound (fun a => exists v, T v /\
  a = paper_main_gordon_matrix_value N M u v xs)).
{ exists (paper_main_gaussian_norm xs).
  intros a [v [Hv ->]].
  pose proof (paper_main_gordon_unit_matrix_value_bound N M u v xs Hxs Hu (HU v Hv)).
  pose proof (Rle_abs (paper_main_gordon_matrix_value N M u v xs)); lra. }
assert (HN : exists a, exists v, T v /\ a = paper_main_gordon_matrix_value N M u v xs).
{ destruct HT as [v Hv].
  exists (paper_main_gordon_matrix_value N M u v xs); exists v; auto. }
destruct (completeness _ HB HN) as [b Hb]; exists b; exact Hb.
Qed.

Lemma paper_main_gordon_compact_inner_member N M T u v xs :
  List.length xs = (N * M)%nat -> paper_main_gordon_dot N u u = 1 ->
  (forall v, T v -> paper_main_gordon_dot M v v = 1) -> T v ->
  paper_main_gordon_matrix_value N M u v xs <= paper_main_gordon_compact_inner N M T u xs.
Proof.
intros Hxs Hu HU Hv.
destruct (paper_main_gordon_compact_inner_lub N M T u xs Hxs Hu (ex_intro _ v Hv) HU)
  as [Hup _].
apply Hup; exists v; auto.
Qed.

Lemma paper_main_gordon_compact_inner_le N M T u xs b :
  List.length xs = (N * M)%nat -> paper_main_gordon_dot N u u = 1 ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  (forall v, T v -> paper_main_gordon_matrix_value N M u v xs <= b) ->
  paper_main_gordon_compact_inner N M T u xs <= b.
Proof.
intros Hxs Hu HT HU Hb.
destruct (paper_main_gordon_compact_inner_lub N M T u xs Hxs Hu HT HU) as [_ Hleast].
apply Hleast; intros a [v [Hv ->]]; apply Hb; exact Hv.
Qed.

Lemma paper_main_gordon_compact_inner_abs N M T u xs :
  List.length xs = (N * M)%nat -> paper_main_gordon_dot N u u = 1 ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  Rabs (paper_main_gordon_compact_inner N M T u xs) <= paper_main_gaussian_norm xs.
Proof.
intros Hxs Hu HT HU; apply Rabs_le; split.
- destruct HT as [v Hv].
  pose proof (paper_main_gordon_compact_inner_member N M T u v xs Hxs Hu HU Hv).
  pose proof (paper_main_gordon_unit_matrix_value_bound N M u v xs Hxs Hu (HU v Hv)).
  pose proof (Rle_abs (- paper_main_gordon_matrix_value N M u v xs)) as Hn0.
  rewrite Rabs_Ropp in Hn0; lra.
- apply paper_main_gordon_compact_inner_le; [exact Hxs|exact Hu|exact HT|exact HU|].
  intros v Hv.
  pose proof (paper_main_gordon_unit_matrix_value_bound N M u v xs Hxs Hu (HU v Hv)).
  pose proof (Rle_abs (paper_main_gordon_matrix_value N M u v xs)); lra.
Qed.

Lemma paper_main_gordon_compact_outer_lub N M T xs :
  (0 < N)%nat -> List.length xs = (N * M)%nat ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  is_lub (fun a => exists u, paper_main_gordon_dot N u u = 1 /\
      a = - paper_main_gordon_compact_inner N M T u xs)
    (- paper_main_gordon_compact_minmax N M T xs).
Proof.
intros HN Hxs HT HU; unfold paper_main_gordon_compact_minmax.
rewrite Ropp_involutive.
apply epsilon_spec.
assert (HB : bound (fun a => exists u, paper_main_gordon_dot N u u = 1 /\
  a = - paper_main_gordon_compact_inner N M T u xs)).
{ exists (paper_main_gaussian_norm xs).
  intros a [u [Hu ->]].
  pose proof (paper_main_gordon_compact_inner_abs N M T u xs Hxs Hu HT HU).
  pose proof (Rle_abs (- paper_main_gordon_compact_inner N M T u xs)) as Hn0.
  rewrite Rabs_Ropp in Hn0; lra. }
assert (HNe : exists a, exists u, paper_main_gordon_dot N u u = 1 /\
  a = - paper_main_gordon_compact_inner N M T u xs).
{ destruct (paper_main_gordon_unit_sphere_nonempty N HN) as [u Hu].
  exists (- paper_main_gordon_compact_inner N M T u xs); exists u; auto. }
destruct (completeness _ HB HNe) as [b Hb]; exists b; exact Hb.
Qed.

Lemma paper_main_gordon_compact_minmax_le_inner N M T u xs :
  (0 < N)%nat -> List.length xs = (N * M)%nat ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  paper_main_gordon_dot N u u = 1 ->
  paper_main_gordon_compact_minmax N M T xs <= paper_main_gordon_compact_inner N M T u xs.
Proof.
intros HN Hxs HT HU Hu.
destruct (paper_main_gordon_compact_outer_lub N M T xs HN Hxs HT HU) as [Hup _].
assert (H : - paper_main_gordon_compact_inner N M T u xs <=
  - paper_main_gordon_compact_minmax N M T xs) by (apply Hup; exists u; auto).
lra.
Qed.

Lemma paper_main_gordon_compact_minmax_ge N M T xs c :
  (0 < N)%nat -> List.length xs = (N * M)%nat ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  (forall u, paper_main_gordon_dot N u u = 1 ->
    c <= paper_main_gordon_compact_inner N M T u xs) ->
  c <= paper_main_gordon_compact_minmax N M T xs.
Proof.
intros HN Hxs HT HU Hc.
destruct (paper_main_gordon_compact_outer_lub N M T xs HN Hxs HT HU) as [_ Hleast].
assert (H : - paper_main_gordon_compact_minmax N M T xs <= - c).
{ apply Hleast; intros a [u [Hu ->]]; pose proof (Hc u Hu); lra. }
lra.
Qed.

Lemma paper_main_gordon_compact_minmax_abs N M T xs :
  (0 < N)%nat -> List.length xs = (N * M)%nat ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  Rabs (paper_main_gordon_compact_minmax N M T xs) <= paper_main_gaussian_norm xs.
Proof.
intros HN Hxs HT HU; apply Rabs_le; split.
- apply paper_main_gordon_compact_minmax_ge; [exact HN|exact Hxs|exact HT|exact HU|].
  intros u Hu.
  pose proof (paper_main_gordon_compact_inner_abs N M T u xs Hxs Hu HT HU).
  pose proof (Rle_abs (- paper_main_gordon_compact_inner N M T u xs)) as Hn0.
  rewrite Rabs_Ropp in Hn0; lra.
- destruct (paper_main_gordon_unit_sphere_nonempty N HN) as [u Hu].
  pose proof (paper_main_gordon_compact_minmax_le_inner N M T u xs HN Hxs HT HU Hu).
  pose proof (paper_main_gordon_compact_inner_abs N M T u xs Hxs Hu HT HU).
  pose proof (Rle_abs (paper_main_gordon_compact_inner N M T u xs)); lra.
Qed.

Lemma paper_main_gordon_compact_inner_lipschitz N M T u xs ys :
  List.length xs = (N * M)%nat -> List.length ys = (N * M)%nat ->
  paper_main_gordon_dot N u u = 1 ->
  (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  paper_main_gordon_compact_inner N M T u xs <=
    paper_main_gordon_compact_inner N M T u ys + paper_main_gordon_distance (N * M) xs ys.
Proof.
intros Hxs Hys Hu HT HU.
apply paper_main_gordon_compact_inner_le; [exact Hxs|exact Hu|exact HT|exact HU|].
intros v Hv.
pose proof (paper_main_gordon_matrix_value_lipschitz N M u v xs ys Hu (HU v Hv)) as H1.
pose proof (paper_main_gordon_compact_inner_member N M T u v ys Hys Hu HU Hv) as H2.
pose proof (Rle_abs (paper_main_gordon_matrix_value N M u v xs -
  paper_main_gordon_matrix_value N M u v ys)); lra.
Qed.

Theorem paper_main_gordon_compact_minmax_lipschitz N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  forall xs ys, List.length xs = (N * M)%nat -> List.length ys = (N * M)%nat ->
    Rabs (paper_main_gordon_compact_minmax N M T xs -
          paper_main_gordon_compact_minmax N M T ys) <=
      1 * paper_main_gordon_distance (N * M) xs ys.
Proof.
intros HN HT HU xs ys Hxs Hys.
assert (Hone : forall ps qs, List.length ps = (N * M)%nat -> List.length qs = (N * M)%nat ->
  paper_main_gordon_compact_minmax N M T ps - paper_main_gordon_distance (N * M) ps qs <=
    paper_main_gordon_compact_minmax N M T qs).
{ intros ps qs Hps Hqs.
  apply paper_main_gordon_compact_minmax_ge; [exact HN|exact Hqs|exact HT|exact HU|].
  intros u Hu.
  pose proof (paper_main_gordon_compact_minmax_le_inner N M T u ps HN Hps HT HU Hu).
  pose proof (paper_main_gordon_compact_inner_lipschitz N M T u ps qs Hps Hqs Hu HT HU).
  lra. }
pose proof (Hone xs ys Hxs Hys) as H1.
pose proof (Hone ys xs Hys Hxs) as H2.
rewrite (paper_main_gordon_distance_symmetric (N * M) ys xs) in H2.
apply Rabs_le; split; lra.
Qed.

Theorem paper_main_gordon_compact_minmax_continuous N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  finite_joint_continuous (N * M) (paper_main_gordon_compact_minmax N M T).
Proof.
intros HN HT HU.
exact (paper_main_gaussian_lipschitz_continuous (N * M) _ 1 Rle_0_1
  (paper_main_gordon_compact_minmax_lipschitz N M T HN HT HU)).
Qed.

Theorem paper_main_gordon_compact_minmax_polynomial_bound N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  finite_polynomial_bound (N * M) (1 + INR (N * M)) 2
    (paper_main_gordon_compact_minmax N M T).
Proof.
intros HN HT HU.
destruct (paper_main_gaussian_norm_polynomial (N * M)) as [HC Hn].
split; [exact HC|].
intros xs Hxs.
pose proof (paper_main_gordon_compact_minmax_abs N M T xs HN Hxs HT HU) as H1.
pose proof (Hn xs Hxs) as H2.
pose proof (Rle_abs (paper_main_gaussian_norm xs)); lra.
Qed.

Theorem paper_main_gordon_compact_minmax_domain N M T :
  (0 < N)%nat -> (exists v, T v) -> (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  gaussian_iterated_integrable (N * M) (paper_main_gordon_compact_minmax N M T) /\
  gaussian_iterated_absolutely_integrable (N * M) (paper_main_gordon_compact_minmax N M T).
Proof.
intros HN HT HU.
destruct (gaussian_coordinate_polynomial_domain (N * M) _ _ 2
  (paper_main_gordon_compact_minmax_continuous N M T HN HT HU)
  (paper_main_gordon_compact_minmax_polynomial_bound N M T HN HT HU)) as [HI [HA _]].
split; [exact HI|exact HA].
Qed.
