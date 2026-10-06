(* Expected finite Gaussian margin. This module proves no tail inequality. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.CoordinatePolynomialContinuity Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Gaussian.CoordinatePolynomialDomain
  Gaussian.FiniteSums Gaussian.CovarianceDefinitions Analysis.FiniteSumAlgebra
  Radius.ExponentialMoments Gordon.Finite Gordon.ProcessCovariance
  Gordon.Processes Gordon.Scalar Gaussian.Norm.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_support d (v : nat -> nat -> R) S xs :=
  finite_max (fun t => paper_main_gordon_dot d (v t) (fun j => List.nth j xs 0)) S.

Definition paper_main_gordon_width d (v : nat -> nat -> R) S :=
  gaussian_iterated_expectation d (paper_main_gordon_support d v S).

Lemma paper_main_gordon_dot_continuous d u :
  finite_joint_continuous d (fun xs => paper_main_gordon_dot d u (fun j => List.nth j xs 0)).
Proof.
unfold paper_main_gordon_dot.
apply finite_joint_continuous_sum; intros i Hi.
apply finite_joint_continuous_scale, finite_joint_continuous_nth.
apply in_seq_lt; exact Hi.
Qed.

Lemma paper_main_gordon_support_continuous d v S :
  finite_joint_continuous d (paper_main_gordon_support d v S).
Proof.
unfold paper_main_gordon_support.
apply paper_main_gordon_finite_max_continuous; intros t Ht.
apply paper_main_gordon_dot_continuous.
Qed.

Lemma paper_main_gordon_support_abs_bound d v S xs :
  S <> [] -> List.length xs = d ->
  (forall t, In t S -> paper_main_gordon_dot d (v t) (v t) = 1) ->
  Rabs (paper_main_gordon_support d v S xs) <= paper_main_gaussian_norm xs.
Proof.
intros HS Hxs Hv.
unfold paper_main_gordon_support.
destruct (finite_max_attained (fun t => paper_main_gordon_dot d (v t) (fun j => List.nth j xs 0))
  S HS) as [t [Ht HE]].
rewrite HE; apply paper_main_gaussian_unit_dot_bound; [exact Hxs|apply Hv; exact Ht].
Qed.

Lemma paper_main_gordon_support_domain d v S :
  S <> [] -> (forall t, In t S -> paper_main_gordon_dot d (v t) (v t) = 1) ->
  gaussian_covariance_domain d (paper_main_gordon_support d v S).
Proof.
intros HS Hv.
apply (gaussian_coordinate_polynomial_domain d (paper_main_gordon_support d v S) (1 + INR d) 2).
- apply paper_main_gordon_support_continuous.
- destruct (paper_main_gaussian_norm_polynomial d) as [HC HB]; split; [exact HC|].
  intros xs Hxs.
  pose proof (paper_main_gordon_support_abs_bound d v S xs HS Hxs Hv) as H.
  specialize (HB xs Hxs); rewrite Rabs_pos_eq in HB by apply paper_main_gaussian_norm_nonnegative.
  lra.
Qed.

Lemma paper_main_gordon_auxiliary_blocks N M u v xs :
  paper_main_gordon_auxiliary N M u v xs =
  paper_main_gordon_dot N u (fun i => List.nth i (List.firstn N xs) 0) +
  paper_main_gordon_dot M v (fun j => List.nth j (List.skipn N xs) 0).
Proof.
unfold paper_main_gordon_auxiliary, paper_main_gordon_dot; f_equal.
- apply finite_sum_ext; intros i Hi.
  rewrite nth_firstn_lt by (apply in_seq_lt; exact Hi); reflexivity.
- apply finite_sum_ext; intros j Hj.
  rewrite nth_skipn_add; reflexivity.
Qed.

Lemma paper_main_gordon_minimax_separable (f g : nat -> R) Y S :
  Y <> [] -> S <> [] ->
  finite_minimax (fun y t => f y + g t) Y S = finite_min f Y + finite_max g S.
Proof.
intros HY HS; unfold finite_minimax.
assert (HE : (fun y => finite_max (fun t => f y + g t) S) =
  (fun y => f y + finite_max g S)).
{ extensionality y.
  transitivity (finite_max (fun t => g t + f y) S).
  - apply paper_main_gordon_finite_max_ext; intros; ring.
  - rewrite paper_main_gordon_max_shift by exact HS; ring. }
rewrite HE; apply paper_main_gordon_min_shift; exact HY.
Qed.

Lemma paper_main_gordon_auxiliary_lower N M z v Y S xs :
  Y <> [] -> S <> [] -> List.length xs = (N + M)%nat ->
  (forall y, In y Y -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  paper_main_gordon_support M v S (List.skipn N xs) -
    paper_main_gaussian_norm (List.firstn N xs) <=
  finite_minimax (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs) Y S.
Proof.
intros HY HS Hxs Hz.
assert (HE : (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs) =
  (fun y t => paper_main_gordon_dot N (z y) (fun i => List.nth i (List.firstn N xs) 0) +
    paper_main_gordon_dot M (v t) (fun j => List.nth j (List.skipn N xs) 0))).
{ extensionality y; extensionality t; apply paper_main_gordon_auxiliary_blocks. }
rewrite HE, paper_main_gordon_minimax_separable by assumption.
assert (HL : - paper_main_gaussian_norm (List.firstn N xs) <=
  finite_min (fun y => paper_main_gordon_dot N (z y) (fun i => List.nth i (List.firstn N xs) 0)) Y).
{ apply finite_min_lower; [exact HY|].
  intros y Hy.
  assert (HP : List.length (List.firstn N xs) = N).
  { rewrite length_firstn, Hxs, Nat.min_l by lia; reflexivity. }
  pose proof (paper_main_gaussian_unit_dot_bound N (z y) (List.firstn N xs) HP (Hz y Hy)) as HB.
  pose proof (Rle_abs (- paper_main_gordon_dot N (z y) (fun i => List.nth i (List.firstn N xs) 0))) as H.
  rewrite Rabs_Ropp in H; lra. }
unfold paper_main_gordon_support; lra.
Qed.

Theorem paper_main_gordon_finite_width_margin r s N M z v :
  (0 < r)%nat -> (0 < s)%nat ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  gaussian_covariance_domain (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  paper_main_gordon_width M v (List.seq 0 s) - sqrt (INR N) <=
  gaussian_iterated_expectation (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs Hz Hv.
destruct (paper_main_gordon_matrix_comparison r s N M z v Hr Hs Hz Hv) as [HD [HQ HC]].
split; [exact HD|].
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
rewrite HGE, HnegE, HNE, HSE in HM.
pose proof (paper_main_gaussian_norm_expectation N) as HN.
unfold paper_main_gordon_width; lra.
Qed.
