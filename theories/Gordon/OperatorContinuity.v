(* Continuity of the genuine rectangular operator supremum. *)
From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.Tuples Gaussian.Coordinate.WeightDefinitions
  Analysis.FiniteSumAlgebra Gordon.Scalar Gordon.Lipschitz Gordon.SetWidth
  Gordon.Bilinear Gordon.OperatorNet.
Open Scope R_scope.

Lemma paper_main_gordon_distance_symmetric d xs ys :
  paper_main_gordon_distance d xs ys = paper_main_gordon_distance d ys xs.
Proof.
unfold paper_main_gordon_distance; f_equal.
apply finite_sum_ext; intros; ring.
Qed.

Lemma paper_main_gordon_operator_perturbation N M xs ys :
  List.length xs = (N*M)%nat -> List.length ys = (N*M)%nat ->
  paper_main_gordon_operator_norm N M xs <= paper_main_gordon_operator_norm N M ys +
    paper_main_gordon_distance (N*M) xs ys.
Proof.
intros Hxs Hys.
apply paper_main_gordon_operator_norm_le; [exact Hxs|].
apply paper_main_gordon_operator_from_units; [exact Hxs| |].
- pose proof (paper_main_gordon_operator_norm_nonnegative N M ys Hys).
  pose proof (paper_main_gordon_distance_nonnegative (N*M) xs ys); lra.
- intros u v Hu Hv.
  pose proof (paper_main_gordon_matrix_value_lipschitz N M u v xs ys Hu Hv) as HL.
  assert (HY : Rabs (paper_main_gordon_matrix_value N M u v ys) <=
    paper_main_gordon_operator_norm N M ys).
  { apply (proj1 (paper_main_gordon_operator_norm_lub N M ys Hys)).
    exists u, v; rewrite Hu, Hv; repeat split; lra. }
  replace (paper_main_gordon_matrix_value N M u v xs) with
    ((paper_main_gordon_matrix_value N M u v xs - paper_main_gordon_matrix_value N M u v ys) +
      paper_main_gordon_matrix_value N M u v ys) by ring.
  eapply Rle_trans; [apply Rabs_triang|lra].
Qed.

Lemma paper_main_gordon_operator_lipschitz N M xs ys :
  List.length xs = (N*M)%nat -> List.length ys = (N*M)%nat ->
  Rabs (paper_main_gordon_operator_norm N M xs - paper_main_gordon_operator_norm N M ys) <=
    paper_main_gordon_distance (N*M) xs ys.
Proof.
intros Hxs Hys.
pose proof (paper_main_gordon_operator_perturbation N M xs ys Hxs Hys) as Hxy.
pose proof (paper_main_gordon_operator_perturbation N M ys xs Hys Hxs) as Hyx.
rewrite paper_main_gordon_distance_symmetric in Hyx.
apply Rabs_le; lra.
Qed.

Lemma paper_main_gordon_operator_continuous N M :
  finite_joint_continuous (N*M) (paper_main_gordon_operator_norm N M).
Proof.
intros z eps.
set (a := sqrt (INR (N*M))).
assert (Ha : 0 <= a) by (unfold a; apply sqrt_pos).
set (delta := eps / (a+1)).
assert (Hd : 0 < delta) by (unfold delta; apply Rdiv_lt_0_compat; [apply cond_pos|lra]).
exists (mkposreal delta Hd); intros w Hw.
pose proof (paper_main_gordon_operator_lipschitz N M
  (coordinates_to_list (N*M) w) (coordinates_to_list (N*M) z)
  (coordinates_to_list_length (N*M) w) (coordinates_to_list_length (N*M) z)) as HL.
assert (HB : paper_main_gordon_distance (N*M) (coordinates_to_list (N*M) w) (coordinates_to_list (N*M) z) <= a*delta).
{ unfold a; apply paper_main_gordon_distance_coordinate_bound; [lra|].
  intros i Hi.
  pose proof (proj1 (coordinates_close_iff (N*M) (mkposreal delta Hd) w z) Hw i Hi) as H.
  simpl in H; lra. }
assert (HE : (a+1)*delta = eps) by (unfold delta; field; lra).
lra.
Qed.
