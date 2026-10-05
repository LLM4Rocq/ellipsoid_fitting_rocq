(* Deterministic passage from a finite soft margin to all outer vectors. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonNets
  PaperMainGordonBilinear.
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

Theorem paper_main_gordon_soft_net_to_all r s N M Y T z v xs eps b L beta gamma :
  (0 < r)%nat -> (0 < s)%nat -> 0 <= eps -> 0 <= b ->
  0 < beta -> 0 < gamma -> paper_main_gordon_operator_bound N M xs L ->
  paper_main_gordon_finite_net N Y z (List.seq 0 r) eps ->
  (forall t, (t < s)%nat -> T (v t)) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) <= b^2) ->
  forall u, Y u -> exists t, (t < s)%nat /\ T (v t) /\
    soft_minimax beta gamma (fun y k => paper_main_gordon_matrix_value N M (z y) (v k) xs)
      (List.seq 0 r) (List.seq 0 s) - ln (INR s)/gamma - L*eps*b <=
    paper_main_gordon_matrix_value N M u (v t) xs.
Proof.
intros Hr Hs He Hb Hbeta Hgamma HL Hnet HV Hnorm u Hu.
assert (HY : List.seq 0 r <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HS : List.seq 0 s <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
destruct (proj2 Hnet u Hu) as [y [Hy Hdist]].
set (F := fun y t => paper_main_gordon_matrix_value N M (z y) (v t) xs).
destruct (finite_max_attained (F y) (List.seq 0 s) HS) as [t [Ht HE]].
pose proof (finite_min_member (fun k => finite_max (F k) (List.seq 0 s)) (List.seq 0 r) y Hy) as HM.
pose proof (proj2 (soft_minimax_bounds beta gamma F (List.seq 0 r) (List.seq 0 s)
  Hbeta Hgamma HY HS)) as Hsoft.
rewrite length_seq in Hsoft.
assert (HtS : (t<s)%nat) by (apply in_seq_lt; exact Ht).
pose proof (paper_main_gordon_bilinear_left_error N M xs L u (z y) (v t) eps b
  HL He Hb Hdist (Hnorm t HtS)) as HEv.
pose proof (Rle_abs (paper_main_gordon_matrix_value N M (z y) (v t) xs -
  paper_main_gordon_matrix_value N M u (v t) xs)) as HD.
rewrite Rabs_minus_sym in HD.
exists t; split; [exact HtS|]; split; [apply HV; exact HtS|].
fold F; change (finite_minimax F (List.seq 0 r) (List.seq 0 s) <= finite_max (F y) (List.seq 0 s)) in HM.
rewrite HE in HM; unfold F in *; lra.
Qed.

Corollary paper_main_gordon_uniform_margin r s N M Y T z v xs eps b L beta gamma c :
  (0 < r)%nat -> (0 < s)%nat -> 0 <= eps -> 0 <= b ->
  0 < beta -> 0 < gamma -> paper_main_gordon_operator_bound N M xs L ->
  paper_main_gordon_finite_net N Y z (List.seq 0 r) eps ->
  (forall t, (t < s)%nat -> T (v t)) ->
  (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) <= b^2) ->
  c <= soft_minimax beta gamma (fun y k => paper_main_gordon_matrix_value N M (z y) (v k) xs)
      (List.seq 0 r) (List.seq 0 s) ->
  forall u, Y u -> exists w, T w /\
    c - ln (INR s)/gamma - L*eps*b <= paper_main_gordon_matrix_value N M u w xs.
Proof.
intros Hr Hs He Hb Hbeta Hgamma HL Hnet HV Hnorm HC u Hu.
destruct (paper_main_gordon_soft_net_to_all r s N M Y T z v xs eps b L beta gamma
  Hr Hs He Hb Hbeta Hgamma HL Hnet HV Hnorm u Hu) as [t [Ht [HT HM]]].
exists (v t); split; [exact HT|lra].
Qed.
