(* The truncated Gaussian expectation in the last coordinate of a jointly
   continuous function is jointly continuous in the other coordinates. If
   0 <= A and F is a jointly continuous function of d + 1 coordinates, then
   xs |-> gaussian_cutoff_expectation (fun t => F (xs ++ [t])) A is a
   jointly continuous function of d coordinates
   (gaussian_last_cutoff_continuous). The proof uses the uniform continuity
   of F on a box (finite_joint_uniform_list_box of
   Analysis.CoordinateTopology) and the bound of
   gaussian_cutoff_local_difference (Gaussian.CutoffBounds). *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.CutoffDefinitions Analysis.CoordinateContinuityDefinitions
  Gaussian.CoordinateTuples Analysis.CoordinateTopology
  Analysis.CoordinateBoxes Gaussian.CutoffBounds.
Import ListNotations.
Open Scope R_scope.

Theorem gaussian_last_cutoff_continuous d F A :
  0 <= A -> finite_joint_continuous (S d) F ->
  finite_joint_continuous d
    (fun xs => gaussian_cutoff_expectation (fun t => F (xs ++ [t])) A).
Proof.
  intros HA HF z eps.
  destruct (coordinates_box_neighborhood d z) as [R [HR [Hz Hnear]]].
  assert (Hhalf : 0 < eps/2) by (pose proof (cond_pos eps); lra).
  destruct (finite_joint_uniform_list_box (S d) F (R+A) HF (mkposreal (eps/2) Hhalf))
    as [delta Hd].
  assert (Hmin : 0 < Rmin 1 delta).
  { apply Rmin_pos; [lra|apply cond_pos]. }
  exists (mkposreal (Rmin 1 delta) Hmin); intros w Hw.
  assert (Hw1 : close_n d 1 w z).
  { apply (coordinates_close_mono d (Rmin 1 delta) 1 w z); [apply Rmin_l|exact Hw]. }
  assert (Hwd : close_n d delta w z).
  { apply (coordinates_close_mono d (Rmin 1 delta) delta w z); [apply Rmin_r|exact Hw]. }
  assert (Hwb : forall x, In x (coordinates_to_list d w) -> Rabs x <= R).
  { exact (Hnear w Hw1). }
  assert (Hb : forall t, Rabs t <= A ->
    Rabs (F (coordinates_to_list d w ++ [t])-F (coordinates_to_list d z ++ [t])) <= eps/2).
  { intros t Ht; apply Rlt_le.
    apply (Hd (coordinates_to_list d z ++ [t]) (coordinates_to_list d w ++ [t])).
    - rewrite length_app, coordinates_to_list_length; simpl; lia.
    - rewrite length_app, coordinates_to_list_length; simpl; lia.
    - intros x Hx; apply in_app_or in Hx; destruct Hx as [Hx|[Hx|Hx]].
      + specialize (Hz x Hx); lra.
      + subst x; lra.
      + contradiction.
    - intros x Hx; apply in_app_or in Hx; destruct Hx as [Hx|[Hx|Hx]].
      + specialize (Hwb x Hx); lra.
      + subst x; lra.
      + contradiction.
    - apply coordinates_close_snoc; try apply coordinates_to_list_length.
      + rewrite !coordinates_roundtrip; exact Hwd.
      + rewrite Rminus_diag_eq, Rabs_R0; [apply cond_pos|reflexivity]. }
  pose proof (gaussian_cutoff_local_difference
    (fun t => F (coordinates_to_list d w ++ [t]))
    (fun t => F (coordinates_to_list d z ++ [t])) A (eps/2)
    HA ltac:(lra)
    (finite_joint_continuous_last_section d F (coordinates_to_list d w)
      HF (coordinates_to_list_length d w))
    (finite_joint_continuous_last_section d F (coordinates_to_list d z)
      HF (coordinates_to_list_length d z)) Hb) as Hbound.
  apply Rle_lt_trans with (eps/2); [exact Hbound|].
  pose proof (cond_pos eps); lra.
Qed.
