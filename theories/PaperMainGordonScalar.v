(* Removing the auxiliary scalar in expectation, not in a tail probability. *)
From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GaussianDefinitions GaussianExpectation
  GaussianProductDefinitions GaussianProduct GaussianLastDefinitions GaussianLastIntegration
  GaussianMoments GaussianMass GaussianCovarianceDefinitions GaussianCovarianceSums
  PaperMainGordonCoordinates PaperMainGordonFinite
  PaperMainGordonProcessCovariance PaperMainGordonProcesses.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_scalar_mean :
  gaussian_integral_exists (fun x => x) /\ gaussian_expectation (fun x => x) = 0.
Proof.
destruct (gaussian_first_raw_moment _ gaussian_kernel_mass_integral) as [HI HV].
split; [exact HI|].
unfold gaussian_expectation, gaussian_integral; rewrite HV; unfold Rdiv; ring.
Qed.

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

Lemma paper_main_gordon_minimax_shift H Y S c :
  Y <> [] -> S <> [] ->
  finite_minimax (fun y s => H y s + c) Y S = finite_minimax H Y S + c.
Proof.
intros HY HS; unfold finite_minimax.
assert (HE : (fun y => finite_max (fun s => H y s + c) S) =
  (fun y => finite_max (H y) S + c)).
{ extensionality y; apply paper_main_gordon_max_shift; exact HS. }
rewrite HE; apply paper_main_gordon_min_shift; exact HY.
Qed.

Lemma paper_main_gordon_bilinear_append N M u v xs t :
  List.length xs = (N * M)%nat ->
  paper_main_gordon_bilinear N M u v (xs ++ [t]) =
  paper_main_gordon_matrix_value N M u v xs + t.
Proof.
intros Hxs; unfold paper_main_gordon_bilinear, paper_main_gordon_matrix_value.
assert (Hlast : List.nth (N * M)%nat (xs ++ [t]) 0 = t).
{ rewrite app_nth2 by lia.
  rewrite Hxs, Nat.sub_diag; reflexivity. }
rewrite Hlast; f_equal.
apply finite_sum_ext; intros i Hi; apply in_seq_lt in Hi.
apply finite_sum_ext; intros j Hj; apply in_seq_lt in Hj.
rewrite app_nth1 by (rewrite Hxs; nia); reflexivity.
Qed.

Lemma paper_main_gordon_scalar_marginal N M z v Y S xs :
  Y <> [] -> S <> [] -> List.length xs = (N * M)%nat ->
  gaussian_last_marginal (fun zs => finite_minimax
    (fun y s => paper_main_gordon_bilinear N M (z y) (v s) zs) Y S) xs =
  finite_minimax (fun y s => paper_main_gordon_matrix_value N M (z y) (v s) xs) Y S.
Proof.
intros HY HS Hxs.
unfold gaussian_last_marginal.
assert (HE : (fun t => finite_minimax
  (fun y s => paper_main_gordon_bilinear N M (z y) (v s) (xs ++ [t])) Y S) =
  (fun t => finite_minimax (fun y s => paper_main_gordon_matrix_value N M (z y) (v s) xs) Y S + t)).
{ extensionality t.
  transitivity (finite_minimax
    (fun y s => paper_main_gordon_matrix_value N M (z y) (v s) xs + t) Y S).
  - apply paper_main_gordon_finite_minimax_ext; intros y s Hy Hs.
    apply paper_main_gordon_bilinear_append; exact Hxs.
  - apply paper_main_gordon_minimax_shift; assumption. }
rewrite HE.
rewrite gaussian_expectation_add by
  (first [apply gaussian_integral_exists_constant | exact (proj1 paper_main_gordon_scalar_mean)]).
rewrite gaussian_expectation_of_constant, (proj2 paper_main_gordon_scalar_mean); ring.
Qed.

Lemma paper_main_gordon_scalar_expectation N M z v Y S :
  Y <> [] -> S <> [] ->
  gaussian_iterated_expectation (Datatypes.S (N * M)) (fun xs => finite_minimax
    (fun y s => paper_main_gordon_bilinear N M (z y) (v s) xs) Y S) =
  gaussian_iterated_expectation (N * M) (fun xs => finite_minimax
    (fun y s => paper_main_gordon_matrix_value N M (z y) (v s) xs) Y S).
Proof.
intros HY HS.
rewrite gaussian_iterated_last_expectation.
apply gaussian_iterated_expectation_ext; intros xs Hxs.
apply paper_main_gordon_scalar_marginal; assumption.
Qed.

Lemma paper_main_gordon_scalar_integrable N M z v Y S :
  Y <> [] -> S <> [] ->
  gaussian_iterated_integrable (Datatypes.S (N * M)) (fun xs => finite_minimax
    (fun y s => paper_main_gordon_bilinear N M (z y) (v s) xs) Y S) ->
  gaussian_iterated_integrable (N * M) (fun xs => finite_minimax
    (fun y s => paper_main_gordon_matrix_value N M (z y) (v s) xs) Y S).
Proof.
intros HY HS HI.
pose proof (proj2 (proj1 (gaussian_iterated_last_integrable (N * M) _) HI)) as HM.
eapply gaussian_iterated_integrable_ext; [|exact HM].
intros xs Hxs; apply paper_main_gordon_scalar_marginal; assumption.
Qed.

Theorem paper_main_gordon_unaugmented_comparison r s N M z v :
  (0 < r)%nat -> (0 < s)%nat ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  gaussian_iterated_integrable (N * M) (fun xs => finite_minimax
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
assert (HY : List.seq 0 r <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HS : List.seq 0 s <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
destruct (paper_main_gordon_unit_process_comparison r s N M z v Hr Hs Hz Hv)
  as [HP [HQ HC]].
split.
- apply paper_main_gordon_scalar_integrable; [exact HY|exact HS|exact (proj1 HP)].
- split; [exact HQ|].
  rewrite (paper_main_gordon_scalar_expectation N M z v _ _ HY HS) in HC; exact HC.
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
intros Hr Hs Hz Hv; split.
- apply paper_main_gordon_raw_matrix_domain; assumption.
- exact (proj2 (paper_main_gordon_unaugmented_comparison r s N M z v Hr Hs Hz Hv)).
Qed.
