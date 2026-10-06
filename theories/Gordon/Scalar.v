(* The bilinear form z^T A v of a Gaussian matrix A in row-major
   coordinates (paper_main_gordon_matrix_value), and Gordon's comparison of
   its min-max with the min-max of the auxiliary process
   (paper_main_gordon_matrix_comparison), proved from the library in
   Gordon.Processes. *)
From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From EllipsoidFitting Require Import Soft.Definitions GaussianDefinitions
  Gaussian.Line.Expectation Gaussian.Iterated.Definitions
  Gaussian.Iterated.Expectation Gaussian.Iterated.SuffixMarginalDefinitions
  Gaussian.Iterated.LastIntegration Gaussian.Line.Moments Gaussian.Line.Mass
  Gaussian.Covariance.Definitions Analysis.FiniteSumAlgebra Gordon.Coordinates
  Gordon.Finite Gordon.ProcessCovariance Gordon.Processes.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_matrix_value N M (u v : nat -> R) xs :=
  finite_sum (fun i => finite_sum (fun j =>
    u i * v j * List.nth (i * M + j)%nat xs 0) (List.seq 0 M)) (List.seq 0 N).

Lemma paper_main_gordon_max_shift f I c :
  I <> [] -> finite_max (fun i => f i + c) I = finite_max f I + c.
Proof.
induction I as [|i I IH]; intros HI; [contradiction|].
destruct I as [|j I]; [reflexivity|].
change (Rmax (f i + c) (finite_max (fun k => f k + c) (j :: I)) =
  Rmax (f i) (finite_max f (j :: I)) + c).
rewrite IH by discriminate.
unfold Rmax; destruct (Rle_dec (f i + c) (finite_max f (j :: I) + c));
  destruct (Rle_dec (f i) (finite_max f (j :: I))); lra.
Qed.

Lemma paper_main_gordon_min_shift f I c :
  I <> [] -> finite_min (fun i => f i + c) I = finite_min f I + c.
Proof.
intros HI; unfold finite_min.
assert (HE : (fun i => - (f i + c)) = (fun i => - f i + -c)) by (extensionality i; ring).
rewrite HE, paper_main_gordon_max_shift by exact HI; ring.
Qed.

Lemma paper_main_gordon_raw_matrix_row N M Z V a xs :
  gaussian_covariance_row (N * M)
    (paper_main_gordon_matrix_loading N M Z V) a xs =
  paper_main_gordon_matrix_value N M (Z a) (V a) xs.
Proof.
unfold gaussian_covariance_row, paper_main_gordon_matrix_loading, paper_main_gordon_matrix_value.
transitivity (finite_sum (fun k => Z a (k / M)%nat * V a (k mod M)%nat *
  List.nth k xs 0) (List.seq 0 (N * M))).
- apply finite_sum_ext; intros k Hk; apply in_seq_lt in Hk.
  assert (E : (k <? N * M)%nat = true) by (apply Nat.ltb_lt; exact Hk).
  rewrite E; reflexivity.
- rewrite paper_main_gordon_sum_rectangle.
  apply finite_sum_ext; intros i Hi; apply finite_sum_ext; intros j Hj; apply in_seq_lt in Hj.
  rewrite paper_main_gordon_row_major_div, paper_main_gordon_row_major_mod by exact Hj.
  reflexivity.
Qed.

Lemma paper_main_gordon_raw_matrix_domain r s N M z v :
  (0 < r)%nat -> (0 < s)%nat ->
  gaussian_covariance_domain (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs.
set (J := fun y t => (y * s + t)%nat).
set (Z := fun a => z (a / s)%nat).
set (V := fun a => v (a mod s)%nat).
set (P := paper_main_gordon_matrix_loading N M Z V).
assert (HY : List.seq 0 r <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HS : List.seq 0 s <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HJ : forall y t, In y (List.seq 0 r) -> In t (List.seq 0 s) -> (J y t < r * s)%nat).
{ intros y t Hy Ht; apply in_seq_lt in Hy; apply in_seq_lt in Ht; unfold J; nia. }
pose proof (paper_main_gordon_finite_domain (r * s) (N * M) P J
  (List.seq 0 r) (List.seq 0 s) HY HS HJ) as HD.
assert (HP : (fun xs => paper_main_gordon_finite J (List.seq 0 r) (List.seq 0 s)
  (gaussian_covariance_image (r * s) (N * M) P xs)) =
  (fun xs => finite_minimax (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s))).
{ extensionality xs.
  unfold paper_main_gordon_finite, paper_main_gordon_scores, gaussian_covariance_image.
  apply paper_main_gordon_finite_minimax_ext; intros y t Hy Ht.
  rewrite nth_map_seq by (apply HJ; assumption).
  unfold P; rewrite paper_main_gordon_raw_matrix_row.
  unfold Z, V, J.
  rewrite paper_main_gordon_row_major_div, paper_main_gordon_row_major_mod by (apply in_seq_lt; exact Ht).
  reflexivity. }
rewrite HP in HD; exact HD.
Qed.

Theorem paper_main_gordon_matrix_comparison r s N M z v :
  (0 < r)%nat -> (0 < s)%nat ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  gaussian_covariance_domain (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  gaussian_covariance_domain (N + M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  gaussian_iterated_expectation (N + M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) <=
  gaussian_iterated_expectation (N * M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs Hz Hv.
pose proof (paper_main_gordon_raw_matrix_domain r s N M z v Hr Hs) as HD.
pose proof (paper_main_gordon_auxiliary_domain r s N M z v Hr Hs) as HA.
split; [exact HD|]; split; [exact HA|].
exact (paper_main_gordon_process_comparison r s N M z v Hr Hs Hz Hv HA HD).
Qed.
