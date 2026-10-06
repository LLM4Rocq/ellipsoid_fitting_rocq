(* Explicit Gaussian loading matrices for the processes in paper section 2.2. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceDefinitions
  GaussianCovarianceSums.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_dot n (u v : nat -> R) :=
  finite_sum (fun i => u i * v i) (List.seq 0 n).

Definition paper_main_gordon_matrix_loading N M (Z V : nat -> nat -> R) a k :=
  if (k <? N * M)%nat then Z a (k / M)%nat * V a (k mod M)%nat else 1.

Definition paper_main_gordon_vector_loading N (Z V : nat -> nat -> R) a k :=
  if (k <? N)%nat then Z a k else V a (k - N)%nat.

Lemma paper_main_gordon_row_major_div i j M :
  (j < M)%nat -> ((i * M + j) / M = i)%nat.
Proof.
intros Hj.
rewrite Nat.div_add_l by lia.
rewrite Nat.div_small by lia; lia.
Qed.

Lemma paper_main_gordon_row_major_mod i j M :
  (j < M)%nat -> ((i * M + j) mod M = j)%nat.
Proof.
intros Hj.
rewrite (Nat.add_comm (i * M) j).
rewrite Nat.Div0.mod_add.
apply Nat.mod_small; exact Hj.
Qed.

Lemma paper_main_gordon_sum_rectangle N M f :
  finite_sum f (List.seq 0 (N * M)) =
  finite_sum (fun i => finite_sum (fun j => f (i * M + j)%nat)
    (List.seq 0 M)) (List.seq 0 N).
Proof.
induction N as [|N IH].
- reflexivity.
- rewrite Nat.mul_succ_l, finite_sum_seq_split, IH, finite_sum_seq_S.
  reflexivity.
Qed.

Lemma paper_main_gordon_tensor_dot N M u u' v v' :
  finite_sum (fun k =>
    (u (k / M)%nat * v (k mod M)%nat) *
    (u' (k / M)%nat * v' (k mod M)%nat)) (List.seq 0 (N * M)) =
  paper_main_gordon_dot N u u' * paper_main_gordon_dot M v v'.
Proof.
rewrite paper_main_gordon_sum_rectangle; unfold paper_main_gordon_dot.
transitivity (finite_sum (fun i => u i * u' i *
  finite_sum (fun j => v j * v' j) (List.seq 0 M)) (List.seq 0 N)).
- apply finite_sum_ext; intros i Hi.
  rewrite <- finite_sum_scale.
  apply finite_sum_ext; intros j Hj; apply in_seq_lt in Hj.
  rewrite !paper_main_gordon_row_major_div, !paper_main_gordon_row_major_mod by exact Hj; ring.
- apply finite_sum_scale_r.
Qed.

Lemma paper_main_gordon_matrix_covariance N M Z V a b :
  gaussian_covariance_entry (S (N * M))
    (paper_main_gordon_matrix_loading N M Z V) a b =
  1 + paper_main_gordon_dot N (Z a) (Z b) * paper_main_gordon_dot M (V a) (V b).
Proof.
unfold gaussian_covariance_entry.
rewrite finite_sum_seq_S.
unfold paper_main_gordon_matrix_loading; rewrite Nat.ltb_irrefl.
assert (HE : finite_sum (fun k =>
  (if (k <? N * M)%nat then Z a (k / M)%nat * V a (k mod M)%nat else 1) *
  (if (k <? N * M)%nat then Z b (k / M)%nat * V b (k mod M)%nat else 1))
  (List.seq 0 (N * M)) =
  finite_sum (fun k => (Z a (k / M)%nat * V a (k mod M)%nat) *
    (Z b (k / M)%nat * V b (k mod M)%nat)) (List.seq 0 (N * M))).
{ apply finite_sum_ext; intros k Hk; apply in_seq_lt in Hk.
  assert (E : (k <? N * M)%nat = true) by (apply Nat.ltb_lt; exact Hk).
  rewrite E; reflexivity. }
rewrite HE, paper_main_gordon_tensor_dot; ring.
Qed.

Lemma paper_main_gordon_vector_covariance N M Z V a b :
  gaussian_covariance_entry (N + M)
    (paper_main_gordon_vector_loading N Z V) a b =
  paper_main_gordon_dot N (Z a) (Z b) + paper_main_gordon_dot M (V a) (V b).
Proof.
unfold gaussian_covariance_entry; rewrite finite_sum_seq_split.
unfold paper_main_gordon_vector_loading, paper_main_gordon_dot; f_equal.
- apply finite_sum_ext; intros k Hk; apply in_seq_lt in Hk.
  assert (E : (k <? N)%nat = true) by (apply Nat.ltb_lt; exact Hk).
  rewrite E; reflexivity.
- apply finite_sum_ext; intros k Hk.
  assert (E : ((N + k) <? N)%nat = false) by (apply Nat.ltb_ge; lia).
  rewrite E; replace (N + k - N)%nat with k by lia; reflexivity.
Qed.

Lemma paper_main_gordon_unit_dot_le n u v :
  paper_main_gordon_dot n u u = 1 -> paper_main_gordon_dot n v v = 1 ->
  paper_main_gordon_dot n u v <= 1.
Proof.
intros Hu Hv.
assert (Hnonneg : 0 <= finite_sum (fun i => (u i - v i)^2) (List.seq 0 n)).
{ apply finite_sum_nonneg; intros; apply pow2_ge_0. }
assert (HE : finite_sum (fun i => (u i - v i)^2) (List.seq 0 n) =
  paper_main_gordon_dot n u u + paper_main_gordon_dot n v v -
  2 * paper_main_gordon_dot n u v).
{ transitivity (finite_sum (fun i => u i * u i + v i * v i - 2 * (u i * v i)) (List.seq 0 n)).
  - apply finite_sum_ext; intros; ring.
  - rewrite finite_sum_minus, finite_sum_plus, finite_sum_scale; reflexivity. }
rewrite HE, Hu, Hv in Hnonneg; lra.
Qed.

Lemma paper_main_gordon_process_covariance_difference N M Z V a b :
  gaussian_covariance_entry (S (N * M))
    (paper_main_gordon_matrix_loading N M Z V) a b -
  gaussian_covariance_entry (N + M)
    (paper_main_gordon_vector_loading N Z V) a b =
  (1 - paper_main_gordon_dot N (Z a) (Z b)) *
  (1 - paper_main_gordon_dot M (V a) (V b)).
Proof.
rewrite paper_main_gordon_matrix_covariance, paper_main_gordon_vector_covariance; ring.
Qed.

Lemma paper_main_gordon_process_covariance_order N M Z V a b :
  paper_main_gordon_dot N (Z a) (Z a) = 1 ->
  paper_main_gordon_dot N (Z b) (Z b) = 1 ->
  paper_main_gordon_dot M (V a) (V a) = 1 ->
  paper_main_gordon_dot M (V b) (V b) = 1 ->
  gaussian_covariance_entry (N + M)
    (paper_main_gordon_vector_loading N Z V) a b <=
  gaussian_covariance_entry (S (N * M))
    (paper_main_gordon_matrix_loading N M Z V) a b.
Proof.
intros HZa HZb HVa HVb.
pose proof (paper_main_gordon_unit_dot_le N (Z a) (Z b) HZa HZb) as HZ.
pose proof (paper_main_gordon_unit_dot_le M (V a) (V b) HVa HVb) as HV.
pose proof (paper_main_gordon_process_covariance_difference N M Z V a b) as HE.
assert (Hprod : 0 <= (1 - paper_main_gordon_dot N (Z a) (Z b)) *
  (1 - paper_main_gordon_dot M (V a) (V b))) by (apply Rmult_le_pos; lra).
lra.
Qed.

Lemma paper_main_gordon_process_covariance_same_row N M Z V a b :
  paper_main_gordon_dot N (Z a) (Z a) = 1 ->
  (forall i, (i < N)%nat -> Z a i = Z b i) ->
  gaussian_covariance_entry (S (N * M))
    (paper_main_gordon_matrix_loading N M Z V) a b =
  gaussian_covariance_entry (N + M)
    (paper_main_gordon_vector_loading N Z V) a b.
Proof.
intros HZ Hsame.
assert (HE : paper_main_gordon_dot N (Z a) (Z b) = 1).
{ transitivity (paper_main_gordon_dot N (Z a) (Z a)); [|exact HZ].
  unfold paper_main_gordon_dot; apply finite_sum_ext; intros i Hi; apply in_seq_lt in Hi.
  rewrite <- (Hsame i Hi); reflexivity. }
rewrite paper_main_gordon_matrix_covariance, paper_main_gordon_vector_covariance, HE; ring.
Qed.
