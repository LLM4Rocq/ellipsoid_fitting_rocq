(* Deterministic passage from a finite soft margin to all outer vectors. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.FiniteSumAlgebra Gordon.ProcessCovariance Gordon.Scalar Gordon.Nets
  Gordon.Bilinear.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_bilinear_ball_bound N M xs L u v a b :
  paper_main_gordon_operator_bound N M xs L -> 0 <= a -> 0 <= b ->
  paper_main_gordon_dot N u u <= a^2 -> paper_main_gordon_dot M v v <= b^2 ->
  Rabs (paper_main_gordon_matrix_value N M u v xs) <= L*a*b.
Proof.
intros [HL HB] Ha Hb Hu Hv.
pose proof (paper_main_gordon_euclidean_bound N u a Ha Hu) as Hnu.
pose proof (paper_main_gordon_euclidean_bound M v b Hb Hv) as Hnv.
pose proof (paper_main_gordon_euclidean_nonnegative N u) as Hup.
pose proof (paper_main_gordon_euclidean_nonnegative M v) as Hvp.
eapply Rle_trans; [apply HB|].
apply Rmult_le_compat; [nra|exact Hvp|nra|exact Hnv].
Qed.

Lemma paper_main_gordon_bilinear_left_error N M xs L u u' v eps b :
  paper_main_gordon_operator_bound N M xs L -> 0 <= eps -> 0 <= b ->
  paper_main_gordon_dot N (fun i => u i-u' i) (fun i => u i-u' i) <= eps^2 ->
  paper_main_gordon_dot M v v <= b^2 ->
  Rabs (paper_main_gordon_matrix_value N M u v xs -
    paper_main_gordon_matrix_value N M u' v xs) <= L*eps*b.
Proof.
intros HL Ha Hb Hu Hv.
rewrite <- paper_main_gordon_matrix_minus_left.
apply paper_main_gordon_bilinear_ball_bound; assumption.
Qed.

Lemma paper_main_gordon_bilinear_right_error N M xs L u v v' a eps :
  paper_main_gordon_operator_bound N M xs L -> 0 <= a -> 0 <= eps ->
  paper_main_gordon_dot N u u <= a^2 ->
  paper_main_gordon_dot M (fun i => v i-v' i) (fun i => v i-v' i) <= eps^2 ->
  Rabs (paper_main_gordon_matrix_value N M u v xs -
    paper_main_gordon_matrix_value N M u v' xs) <= L*a*eps.
Proof.
intros HL Ha Hb Hu Hv.
rewrite <- paper_main_gordon_matrix_minus_right.
apply paper_main_gordon_bilinear_ball_bound; assumption.
Qed.
