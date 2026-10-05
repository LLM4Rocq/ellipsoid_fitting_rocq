(* Dimension-independent input bounds for finite Gaussian min-max values. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceDefinitions
  GaussianCovarianceSums PaperMainGordonProcessCovariance PaperMainGordonProcesses
  PaperMainGordonScalar.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_distance d (xs ys : list R) :=
  sqrt (finite_sum (fun k => (List.nth k xs 0 - List.nth k ys 0)^2) (List.seq 0 d)).

Lemma paper_main_gordon_sum_cauchy (f g : nat -> R) I :
  (finite_sum (fun i => f i * g i) I)^2 <=
  finite_sum (fun i => (f i)^2) I * finite_sum (fun i => (g i)^2) I.
Proof.
set (A := finite_sum (fun i => (f i)^2) I).
set (B := finite_sum (fun i => (g i)^2) I).
set (C := finite_sum (fun i => f i * g i) I).
assert (Hpos : 0 <= finite_sum (fun i => finite_sum
  (fun j => (f i * g j - f j * g i)^2) I) I).
{ apply finite_sum_nonneg; intros i Hi; apply finite_sum_nonneg; intros j Hj; apply pow2_ge_0. }
assert (Hinner : forall i, finite_sum (fun j => (f i * g j - f j * g i)^2) I =
  (f i)^2 * B + (g i)^2 * A - (2 * f i * g i) * C).
{ intros i.
  transitivity (finite_sum (fun j => (f i)^2 * (g j)^2 + (g i)^2 * (f j)^2 -
    (2 * f i * g i) * (f j * g j)) I).
  - apply finite_sum_ext; intros; ring.
  - rewrite finite_sum_minus, finite_sum_plus, !finite_sum_scale; reflexivity. }
assert (HE : finite_sum (fun i => finite_sum (fun j => (f i * g j - f j * g i)^2) I) I =
  A * B + B * A - 2 * C^2).
{ transitivity (finite_sum (fun i => (f i)^2 * B + (g i)^2 * A - (2 * f i * g i) * C) I).
  - apply finite_sum_ext; intros; apply Hinner.
  - rewrite finite_sum_minus, finite_sum_plus, !finite_sum_scale_r.
    assert (HC : finite_sum (fun i => 2 * f i * g i) I = 2 * C).
    { unfold C; rewrite <- finite_sum_scale; apply finite_sum_ext; intros; ring. }
    rewrite HC; fold A B; ring. }
rewrite HE in Hpos; change (C^2 <= A * B); nra.
Qed.

Lemma paper_main_gordon_distance_nonnegative d xs ys :
  0 <= paper_main_gordon_distance d xs ys.
Proof.
unfold paper_main_gordon_distance; apply sqrt_pos.
Qed.

Lemma paper_main_gordon_distance_squared d xs ys :
  (paper_main_gordon_distance d xs ys)^2 =
  finite_sum (fun k => (List.nth k xs 0 - List.nth k ys 0)^2) (List.seq 0 d).
Proof.
unfold paper_main_gordon_distance.
apply pow2_sqrt.
apply finite_sum_nonneg; intros; apply pow2_ge_0.
Qed.

Lemma paper_main_gordon_row_lipschitz d P a xs ys L :
  0 <= L -> gaussian_covariance_entry d P a a <= L^2 ->
  Rabs (gaussian_covariance_row d P a xs - gaussian_covariance_row d P a ys) <=
  L * paper_main_gordon_distance d xs ys.
Proof.
intros HL Hcov.
pose proof (paper_main_gordon_sum_cauchy (P a)
  (fun k => List.nth k xs 0 - List.nth k ys 0) (List.seq 0 d)) as HC.
assert (HP : finite_sum (fun k => (P a k)^2) (List.seq 0 d) =
  gaussian_covariance_entry d P a a).
{ unfold gaussian_covariance_entry; apply finite_sum_ext; intros; ring. }
assert (HE : finite_sum (fun k => P a k * (List.nth k xs 0 - List.nth k ys 0))
  (List.seq 0 d) = gaussian_covariance_row d P a xs - gaussian_covariance_row d P a ys).
{ unfold gaussian_covariance_row; rewrite <- finite_sum_minus.
  apply finite_sum_ext; intros; ring. }
rewrite HP, HE, <- paper_main_gordon_distance_squared in HC.
pose proof (Rmult_le_compat_r ((paper_main_gordon_distance d xs ys)^2)
  (gaussian_covariance_entry d P a a) (L^2)
  (pow2_ge_0 (paper_main_gordon_distance d xs ys)) Hcov) as Hmul.
pose proof (paper_main_gordon_distance_nonnegative d xs ys) as HD.
pose proof (Rsqr_abs (gaussian_covariance_row d P a xs - gaussian_covariance_row d P a ys)) as HA.
pose proof (Rabs_pos (gaussian_covariance_row d P a xs - gaussian_covariance_row d P a ys)) as HAP.
unfold Rsqr in HA.
assert (Hprod : 0 <= L * paper_main_gordon_distance d xs ys) by (apply Rmult_le_pos; assumption).
nra.
Qed.

Lemma paper_main_gordon_raw_matrix_covariance N M Z V a b :
  gaussian_covariance_entry (N * M)
    (paper_main_gordon_matrix_loading N M Z V) a b =
  paper_main_gordon_dot N (Z a) (Z b) * paper_main_gordon_dot M (V a) (V b).
Proof.
pose proof (paper_main_gordon_matrix_covariance N M Z V a b) as H.
unfold gaussian_covariance_entry in H; rewrite finite_sum_seq_S in H.
unfold paper_main_gordon_matrix_loading in H; rewrite Nat.ltb_irrefl in H.
unfold gaussian_covariance_entry, paper_main_gordon_matrix_loading; lra.
Qed.

Lemma paper_main_gordon_matrix_value_lipschitz N M u v xs ys :
  paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M v v = 1 ->
  Rabs (paper_main_gordon_matrix_value N M u v xs -
    paper_main_gordon_matrix_value N M u v ys) <=
  paper_main_gordon_distance (N * M) xs ys.
Proof.
intros Hu Hv.
set (P := paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v)).
assert (HC : gaussian_covariance_entry (N * M) P 0 0 <= 1^2).
{ unfold P; rewrite paper_main_gordon_raw_matrix_covariance; rewrite Hu, Hv; lra. }
pose proof (paper_main_gordon_row_lipschitz (N * M) P 0 xs ys 1 ltac:(lra) HC) as H.
unfold P in H; rewrite !paper_main_gordon_raw_matrix_row, Rmult_1_l in H; exact H.
Qed.
