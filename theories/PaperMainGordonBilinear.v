(* Rectangular bilinear forms and Euclidean operator bounds. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceDefinitions
  GaussianCovarianceSums PaperMainGordonProcessCovariance PaperMainGordonScalar
  PaperMainGordonLipschitz PaperMainGordonSetWidth PaperMainGaussianNorm.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_operator_bound N M xs L :=
  0 <= L /\ forall u v,
    Rabs (paper_main_gordon_matrix_value N M u v xs) <=
    L * euclidean_norm u (List.seq 0 N) * euclidean_norm v (List.seq 0 M).

Lemma paper_main_gordon_squared_norm_dot d u :
  squared_norm u (List.seq 0 d) = paper_main_gordon_dot d u u.
Proof.
unfold squared_norm, paper_main_gordon_dot; apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gordon_euclidean_nonnegative d u :
  0 <= euclidean_norm u (List.seq 0 d).
Proof.
unfold euclidean_norm; apply sqrt_pos.
Qed.

Lemma paper_main_gordon_euclidean_squared d u :
  (euclidean_norm u (List.seq 0 d))^2 = paper_main_gordon_dot d u u.
Proof.
rewrite <- paper_main_gordon_squared_norm_dot; unfold euclidean_norm.
apply pow2_sqrt; unfold squared_norm; apply finite_sum_nonneg; intros; apply pow2_ge_0.
Qed.

Lemma paper_main_gordon_euclidean_bound d u b :
  0 <= b -> paper_main_gordon_dot d u u <= b^2 ->
  euclidean_norm u (List.seq 0 d) <= b.
Proof.
intros Hb Hu; pose proof (paper_main_gordon_euclidean_squared d u); nra.
Qed.

Lemma paper_main_gordon_dot_scale d u c :
  paper_main_gordon_dot d (fun i => c*u i) (fun i => c*u i) =
  c^2 * paper_main_gordon_dot d u u.
Proof.
unfold paper_main_gordon_dot; rewrite <- finite_sum_scale.
apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gordon_normalized_unit d u :
  0 < euclidean_norm u (List.seq 0 d) ->
  paper_main_gordon_dot d (fun i => /euclidean_norm u (List.seq 0 d) * u i)
    (fun i => /euclidean_norm u (List.seq 0 d) * u i) = 1.
Proof.
intros H; rewrite paper_main_gordon_dot_scale, <- paper_main_gordon_euclidean_squared.
field; lra.
Qed.

Lemma paper_main_gordon_matrix_minus_left N M u u' v xs :
  paper_main_gordon_matrix_value N M (fun i => u i-u' i) v xs =
  paper_main_gordon_matrix_value N M u v xs - paper_main_gordon_matrix_value N M u' v xs.
Proof.
unfold paper_main_gordon_matrix_value; rewrite <- finite_sum_minus.
apply finite_sum_ext; intros i Hi; rewrite <- finite_sum_minus.
apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gordon_matrix_minus_right N M u v v' xs :
  paper_main_gordon_matrix_value N M u (fun i => v i-v' i) xs =
  paper_main_gordon_matrix_value N M u v xs - paper_main_gordon_matrix_value N M u v' xs.
Proof.
unfold paper_main_gordon_matrix_value; rewrite <- finite_sum_minus.
apply finite_sum_ext; intros i Hi; rewrite <- finite_sum_minus.
apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gordon_matrix_scale_left N M u v xs c :
  paper_main_gordon_matrix_value N M (fun i => c*u i) v xs =
  c * paper_main_gordon_matrix_value N M u v xs.
Proof.
unfold paper_main_gordon_matrix_value; rewrite <- finite_sum_scale.
apply finite_sum_ext; intros i Hi; rewrite <- finite_sum_scale.
apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gordon_matrix_scale_right N M u v xs c :
  paper_main_gordon_matrix_value N M u (fun i => c*v i) xs =
  c * paper_main_gordon_matrix_value N M u v xs.
Proof.
unfold paper_main_gordon_matrix_value; rewrite <- finite_sum_scale.
apply finite_sum_ext; intros i Hi; rewrite <- finite_sum_scale.
apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gordon_matrix_frobenius N M u v xs :
  List.length xs = (N*M)%nat ->
  Rabs (paper_main_gordon_matrix_value N M u v xs) <=
    paper_main_gaussian_norm xs * euclidean_norm u (List.seq 0 N) *
    euclidean_norm v (List.seq 0 M).
Proof.
intros Hxs.
set (P := paper_main_gordon_matrix_loading N M (fun _ => u) (fun _ => v)).
set (a := euclidean_norm u (List.seq 0 N)).
set (b := euclidean_norm v (List.seq 0 M)).
assert (Ha : 0 <= a) by (apply paper_main_gordon_euclidean_nonnegative).
assert (Hb : 0 <= b) by (apply paper_main_gordon_euclidean_nonnegative).
assert (HA : a^2 = paper_main_gordon_dot N u u) by (apply paper_main_gordon_euclidean_squared).
assert (HB : b^2 = paper_main_gordon_dot M v v) by (apply paper_main_gordon_euclidean_squared).
assert (HP : paper_main_gordon_dot (N*M) (P 0%nat) (P 0%nat) <= (a*b)^2).
{ change (gaussian_covariance_entry (N*M) P 0 0 <= (a*b)^2).
  unfold P; rewrite paper_main_gordon_raw_matrix_covariance; cbn beta.
  rewrite <- HA, <- HB; nra. }
pose proof (paper_main_gordon_coefficient_dot_bound (N*M) (P 0%nat) xs (a*b)
  Hxs ltac:(nra) HP) as H.
change (Rabs (gaussian_covariance_row (N*M) P 0 xs) <= (a*b)*paper_main_gaussian_norm xs) in H.
unfold P in H; rewrite paper_main_gordon_raw_matrix_row in H; fold a b; nra.
Qed.

Lemma paper_main_gordon_operator_frobenius N M xs :
  List.length xs = (N*M)%nat ->
  paper_main_gordon_operator_bound N M xs (paper_main_gaussian_norm xs).
Proof.
intros Hxs; split; [apply paper_main_gaussian_norm_nonnegative|].
intros u v; apply paper_main_gordon_matrix_frobenius; exact Hxs.
Qed.

Lemma paper_main_gordon_operator_from_units N M xs L :
  List.length xs = (N*M)%nat -> 0 <= L ->
  (forall u v, paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M v v = 1 ->
    Rabs (paper_main_gordon_matrix_value N M u v xs) <= L) ->
  paper_main_gordon_operator_bound N M xs L.
Proof.
intros Hxs HL HU; split; [exact HL|]; intros u v.
set (a := euclidean_norm u (List.seq 0 N)).
set (b := euclidean_norm v (List.seq 0 M)).
assert (Ha : 0 <= a) by (apply paper_main_gordon_euclidean_nonnegative).
assert (Hb : 0 <= b) by (apply paper_main_gordon_euclidean_nonnegative).
pose proof (paper_main_gordon_matrix_frobenius N M u v xs Hxs) as HF; fold a b in HF |- *.
destruct (Req_dec a 0) as [HA|HA]; [rewrite HA in *; nra|].
destruct (Req_dec b 0) as [HB|HB]; [rewrite HB in *; nra|].
set (un := fun i => /a*u i).
set (vn := fun i => /b*v i).
assert (HUn : paper_main_gordon_dot N un un = 1).
{ apply paper_main_gordon_normalized_unit; fold a; lra. }
assert (HVn : paper_main_gordon_dot M vn vn = 1).
{ apply paper_main_gordon_normalized_unit; fold b; lra. }
pose proof (HU un vn HUn HVn) as H.
assert (HE : paper_main_gordon_matrix_value N M u v xs =
  (a*b)*paper_main_gordon_matrix_value N M un vn xs).
{ unfold un, vn; rewrite paper_main_gordon_matrix_scale_left, paper_main_gordon_matrix_scale_right.
  field; auto. }
rewrite HE, Rabs_mult, Rabs_pos_eq by nra.
pose proof (Rmult_le_compat_l (a*b) _ _ ltac:(nra) H); nra.
Qed.
