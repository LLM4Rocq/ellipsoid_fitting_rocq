(* Finite Gaussian soft margin with explicit outer entropy error. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Gaussian.Covariance.Definitions Analysis.FiniteSumAlgebra Gordon.Coordinates
  Gordon.Comparison Gordon.ProcessCovariance Gordon.Scalar Gordon.Width.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_soft_minimax_ext beta gamma F G Y S :
  (forall y t, In y Y -> In t S -> F y t = G y t) ->
  soft_minimax beta gamma F Y S = soft_minimax beta gamma G Y S.
Proof.
intros HE.
unfold soft_minimax, soft_min, soft_max.
f_equal; f_equal; f_equal.
apply finite_sum_ext; intros y Hy.
f_equal; f_equal; f_equal; f_equal; f_equal.
apply finite_sum_ext; intros t Ht.
rewrite (HE y t Hy Ht); reflexivity.
Qed.

Lemma paper_main_gordon_soft_matrix_domain r s N M z v beta gamma :
  (0 < r)%nat -> (0 < s)%nat -> 0 < beta -> 0 < gamma ->
  gaussian_covariance_domain (N * M) (fun xs => soft_minimax beta gamma
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs Hb Hg.
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
pose proof (paper_main_gordon_image_domain (r * s) (N * M) P beta gamma J
  (List.seq 0 r) (List.seq 0 s) Hb Hg HY HS HJ) as HD.
assert (HP : (fun xs => paper_main_gordon_value beta gamma J (List.seq 0 r) (List.seq 0 s)
  (gaussian_covariance_image (r * s) (N * M) P xs)) =
  (fun xs => soft_minimax beta gamma (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s))).
{ extensionality xs.
  unfold paper_main_gordon_value, paper_main_gordon_scores, gaussian_covariance_image.
  apply paper_main_gordon_soft_minimax_ext; intros y t Hy Ht.
  rewrite nth_map_seq by (apply HJ; assumption).
  unfold P; rewrite paper_main_gordon_raw_matrix_row.
  unfold Z, V, J.
  rewrite paper_main_gordon_row_major_div, paper_main_gordon_row_major_mod by (apply in_seq_lt; exact Ht).
  reflexivity. }
rewrite HP in HD; exact HD.
Qed.

Theorem paper_main_gordon_soft_width_margin r s N M z v beta gamma :
  (0 < r)%nat -> (0 < s)%nat -> 0 < beta -> 0 < gamma ->
  (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  gaussian_covariance_domain (N * M) (fun xs => soft_minimax beta gamma
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) /\
  paper_main_gordon_width M v (List.seq 0 s) - sqrt (INR N) - Rpower.ln (INR r) / beta <=
  gaussian_iterated_expectation (N * M) (fun xs => soft_minimax beta gamma
    (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs Hb Hg Hz Hv.
pose proof (paper_main_gordon_soft_matrix_domain r s N M z v beta gamma Hr Hs Hb Hg) as HD.
split; [exact HD|].
destruct (paper_main_gordon_finite_width_margin r s N M z v Hr Hs Hz Hv) as [HF Hmargin].
assert (HY : List.seq 0 r <> []).
{ intro H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HS : List.seq 0 s <> []).
{ intro H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
set (c := - (Rpower.ln (INR r) / beta)).
destruct (gaussian_iterated_constant (N * M) c) as [HCI HCE].
destruct (gaussian_iterated_add (N * M)
  (fun xs => finite_minimax (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s))
  (fun _ => c) (proj1 HF) HCI) as [HGI HGE].
pose proof (gaussian_iterated_monotone (N * M)
  (fun xs => finite_minimax (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s) + c)
  (fun xs => soft_minimax beta gamma (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) HGI (proj1 HD)
  ltac:(intros xs Hxs;
    pose proof (proj1 (soft_minimax_bounds beta gamma
      (fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs)
      (List.seq 0 r) (List.seq 0 s) Hb Hg HY HS)) as H;
    rewrite length_seq in H; unfold c; lra)) as HM.
rewrite HGE, HCE in HM; unfold c in HM; lra.
Qed.
