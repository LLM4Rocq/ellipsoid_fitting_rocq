(* Finite unit-vector families in the Gaussian processes of paper section 2.2. *)
From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions
  GaussianCovarianceDefinitions GaussianCovarianceSums PaperMainGordonCoordinates
  PaperMainGordonFinite PaperMainGordonProcessCovariance.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_bilinear N M (u v : nat -> R) xs :=
  finite_sum (fun i => finite_sum (fun j =>
    u i * v j * List.nth (i * M + j)%nat xs 0) (List.seq 0 M)) (List.seq 0 N)
  + List.nth (N * M)%nat xs 0.

Definition paper_main_gordon_auxiliary N M (u v : nat -> R) xs :=
  paper_main_gordon_dot N u (fun i => List.nth i xs 0) +
  paper_main_gordon_dot M v (fun j => List.nth (N + j)%nat xs 0).

Lemma paper_main_gordon_matrix_row N M Z V a xs :
  gaussian_covariance_row (S (N * M))
    (paper_main_gordon_matrix_loading N M Z V) a xs =
  paper_main_gordon_bilinear N M (Z a) (V a) xs.
Proof.
unfold gaussian_covariance_row, paper_main_gordon_bilinear.
rewrite finite_sum_seq_S.
unfold paper_main_gordon_matrix_loading; rewrite Nat.ltb_irrefl, Rmult_1_l.
f_equal.
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

Lemma paper_main_gordon_vector_row N M Z V a xs :
  gaussian_covariance_row (N + M)
    (paper_main_gordon_vector_loading N Z V) a xs =
  paper_main_gordon_auxiliary N M (Z a) (V a) xs.
Proof.
unfold gaussian_covariance_row, paper_main_gordon_auxiliary, paper_main_gordon_dot.
rewrite finite_sum_seq_split.
unfold paper_main_gordon_vector_loading; f_equal.
- apply finite_sum_ext; intros k Hk; apply in_seq_lt in Hk.
  assert (E : (k <? N)%nat = true) by (apply Nat.ltb_lt; exact Hk).
  rewrite E; reflexivity.
- apply finite_sum_ext; intros k Hk.
  assert (E : ((N + k) <? N)%nat = false) by (apply Nat.ltb_ge; lia).
  rewrite E; replace (N + k - N)%nat with k by lia; reflexivity.
Qed.

Lemma paper_main_gordon_finite_max_ext f g I :
  (forall i, In i I -> f i = g i) -> finite_max f I = finite_max g I.
Proof.
induction I as [|i I IH]; intros H; [reflexivity|].
destruct I as [|j I].
- simpl; apply H; simpl; auto.
- change (Rmax (f i) (finite_max f (j :: I)) = Rmax (g i) (finite_max g (j :: I))).
  rewrite (H i (or_introl eq_refl)).
  f_equal; apply IH; intros k Hk; apply H; right; exact Hk.
Qed.

Lemma paper_main_gordon_finite_minimax_ext F G Y S :
  (forall y s, In y Y -> In s S -> F y s = G y s) ->
  finite_minimax F Y S = finite_minimax G Y S.
Proof.
intros H; unfold finite_minimax, finite_min.
f_equal; apply paper_main_gordon_finite_max_ext; intros y Hy.
f_equal; apply paper_main_gordon_finite_max_ext; intros s Hs.
apply H; assumption.
Qed.

Theorem paper_main_gordon_unit_process_comparison r s N M z v :
  (0 < r)%nat -> (0 < s)%nat ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  gaussian_covariance_domain (S (N * M)) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_bilinear N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  gaussian_covariance_domain (N + M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  gaussian_iterated_expectation (N + M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) <=
  gaussian_iterated_expectation (S (N * M)) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_bilinear N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs Hz Hv.
set (J := fun y t => (y * s + t)%nat).
set (Z := fun a => z (a / s)%nat).
set (V := fun a => v (a mod s)%nat).
set (P := paper_main_gordon_matrix_loading N M Z V).
set (Q := paper_main_gordon_vector_loading N Z V).
assert (HY : List.seq 0 r <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite seq_length in H; simpl in H; lia. }
assert (HS : List.seq 0 s <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite seq_length in H; simpl in H; lia. }
assert (HJ : forall y t, In y (List.seq 0 r) -> In t (List.seq 0 s) -> (J y t < r * s)%nat).
{ intros y t Hy Ht; apply in_seq_lt in Hy; apply in_seq_lt in Ht; unfold J; nia. }
assert (HZdecode : forall y t, (t < s)%nat -> Z (J y t) = z y).
{ intros y t Ht; unfold Z, J; rewrite paper_main_gordon_row_major_div by exact Ht; reflexivity. }
assert (HVdecode : forall y t, (t < s)%nat -> V (J y t) = v t).
{ intros y t Ht; unfold V, J; rewrite paper_main_gordon_row_major_mod by exact Ht; reflexivity. }
assert (Hsame : forall y t t', In y (List.seq 0 r) -> In t (List.seq 0 s) -> In t' (List.seq 0 s) ->
  gaussian_covariance_entry (S (N * M)) P (J y t) (J y t') =
  gaussian_covariance_entry (N + M) Q (J y t) (J y t')).
{ intros y t t' Hy Ht Ht'; apply in_seq_lt in Hy; apply in_seq_lt in Ht; apply in_seq_lt in Ht'.
  apply paper_main_gordon_process_covariance_same_row.
  - rewrite HZdecode by exact Ht; apply Hz; exact Hy.
  - intros i Hi; rewrite !HZdecode by assumption; reflexivity. }
assert (Hcross : forall y y' t t', In y (List.seq 0 r) -> In y' (List.seq 0 r) ->
  In t (List.seq 0 s) -> In t' (List.seq 0 s) -> y <> y' ->
  gaussian_covariance_entry (N + M) Q (J y t) (J y' t') <=
  gaussian_covariance_entry (S (N * M)) P (J y t) (J y' t')).
{ intros y y' t t' Hy Hy' Ht Ht' Hne; apply in_seq_lt in Hy; apply in_seq_lt in Hy';
    apply in_seq_lt in Ht; apply in_seq_lt in Ht'.
  apply paper_main_gordon_process_covariance_order.
  - rewrite HZdecode by exact Ht; apply Hz; exact Hy.
  - rewrite HZdecode by exact Ht'; apply Hz; exact Hy'.
  - rewrite HVdecode by exact Ht; apply Hv; exact Ht.
  - rewrite HVdecode by exact Ht'; apply Hv; exact Ht'. }
pose proof (paper_main_gordon_finite_comparison (r * s) (S (N * M)) (N + M)
  P Q J (List.seq 0 r) (List.seq 0 s) HY HS HJ Hsame Hcross) as HC.
assert (HP : (fun xs => paper_main_gordon_finite J (List.seq 0 r) (List.seq 0 s)
  (gaussian_covariance_image (r * s) (S (N * M)) P xs)) =
  (fun xs => finite_minimax (fun y t => paper_main_gordon_bilinear N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s))).
{ extensionality xs.
  unfold paper_main_gordon_finite, paper_main_gordon_scores, gaussian_covariance_image.
  apply paper_main_gordon_finite_minimax_ext; intros y t Hy Ht.
  rewrite nth_map_seq by (apply HJ; assumption).
  unfold P; rewrite paper_main_gordon_matrix_row.
  rewrite HZdecode, HVdecode by (apply in_seq_lt; exact Ht); reflexivity. }
assert (HQ : (fun xs => paper_main_gordon_finite J (List.seq 0 r) (List.seq 0 s)
  (gaussian_covariance_image (r * s) (N + M) Q xs)) =
  (fun xs => finite_minimax (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s))).
{ extensionality xs.
  unfold paper_main_gordon_finite, paper_main_gordon_scores, gaussian_covariance_image.
  apply paper_main_gordon_finite_minimax_ext; intros y t Hy Ht.
  rewrite nth_map_seq by (apply HJ; assumption).
  unfold Q; rewrite paper_main_gordon_vector_row.
  rewrite HZdecode, HVdecode by (apply in_seq_lt; exact Ht); reflexivity. }
rewrite HP, HQ in HC; exact HC.
Qed.
