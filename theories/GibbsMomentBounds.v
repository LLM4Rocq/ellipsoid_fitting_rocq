From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions Cumulants
  MomentDefinitions FiniteMoments.
Import ListNotations.
Open Scope R_scope.

(* Bounds on the averages and covariances of a finite Gibbs law on a
   nonempty index list, which is a probability on the list
   (gibbs_finite_probability). Below, <u> is gibbs_average c f I u and
   cov(u, v) is gibbs_covariance c f I u v.
   - gibbs_mean_uniform_bound: |u| <= K on the list gives |<u>| <= K.
   - gibbs_covariance_absolute_bound:
     |cov(u, v)| <= <|u| |v|> + <|u|> <|v|>.
   - gibbs_covariance_cubic_bound: if r >= 0, |u| <= A r^2 and |v| <= B r,
     then |cov(u, v)| <= 2 A B <r^3>. *)

Lemma gibbs_finite_probability c f I :
  I <> [] -> finite_probability (gibbs_weight c f I) I.
Proof.
  intros HI; split.
  - intros; apply gibbs_weight_nonnegative; exact HI.
  - apply gibbs_weights_normalized; exact HI.
Qed.

Lemma gibbs_average_abs_bound c f I u :
  I <> [] ->
  Rabs (gibbs_average c f I u) <= gibbs_average c f I (fun i => Rabs (u i)).
Proof.
  intros HI; apply weighted_average_abs, gibbs_finite_probability; exact HI.
Qed.

Lemma gibbs_average_monotone c f I u v :
  I <> [] -> (forall i, In i I -> u i <= v i) ->
  gibbs_average c f I u <= gibbs_average c f I v.
Proof.
  intros HI H; apply weighted_average_monotone; [apply gibbs_finite_probability|]; assumption.
Qed.

Theorem gibbs_mean_uniform_bound c f I u K :
  I <> [] -> (forall i, In i I -> Rabs (u i) <= K) ->
  Rabs (gibbs_average c f I u) <= K.
Proof.
  intros HI Hu.
  eapply Rle_trans; [apply gibbs_average_abs_bound; exact HI|].
  rewrite <- (gibbs_average_const c f I K HI).
  apply gibbs_average_monotone; assumption.
Qed.

Theorem gibbs_covariance_absolute_bound c f I u v :
  I <> [] ->
  Rabs (gibbs_covariance c f I u v) <=
  gibbs_average c f I (fun i => Rabs (u i) * Rabs (v i)) +
  gibbs_average c f I (fun i => Rabs (u i)) *
  gibbs_average c f I (fun i => Rabs (v i)).
Proof.
  intros HI.
  pose proof (gibbs_average_abs_bound c f I u HI) as Hu.
  pose proof (gibbs_average_abs_bound c f I v HI) as Hv.
  pose proof (gibbs_average_abs_bound c f I (fun i => u i * v i) HI) as Huv.
  assert (HE : gibbs_average c f I (fun i => Rabs (u i * v i)) =
    gibbs_average c f I (fun i => Rabs (u i) * Rabs (v i))).
  { apply gibbs_average_ext; intros; apply Rabs_mult. }
  cbv beta in Huv; rewrite HE in Huv.
  unfold gibbs_covariance.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp, Rabs_mult.
  pose proof (Rabs_pos (gibbs_average c f I u)).
  pose proof (Rabs_pos (gibbs_average c f I v)).
  assert (HM : Rabs (gibbs_average c f I u) * Rabs (gibbs_average c f I v) <=
    gibbs_average c f I (fun i => Rabs (u i)) *
    gibbs_average c f I (fun i => Rabs (v i))) by (apply Rmult_le_compat; assumption).
  lra.
Qed.

Theorem gibbs_covariance_cubic_bound c f I u v r A B :
  I <> [] -> 0 <= A -> 0 <= B ->
  (forall i, In i I -> 0 <= r i) ->
  (forall i, In i I -> Rabs (u i) <= A * r i ^ 2) ->
  (forall i, In i I -> Rabs (v i) <= B * r i) ->
  Rabs (gibbs_covariance c f I u v) <=
  2 * A * B * gibbs_average c f I (fun i => r i ^ 3).
Proof.
  intros HI HA HB Hr Hu Hv.
  assert (Hm : gibbs_average c f I (fun i => r i ^ 2) * gibbs_average c f I r <=
    gibbs_average c f I (fun i => r i ^ 3)).
  { apply weighted_moment_product; [apply gibbs_finite_probability; exact HI|exact Hr]. }
  assert (Hu' : gibbs_average c f I (fun i => Rabs (u i)) <=
    A * gibbs_average c f I (fun i => r i ^ 2)).
  { rewrite <- gibbs_average_scale; apply gibbs_average_monotone; assumption. }
  assert (Hv' : gibbs_average c f I (fun i => Rabs (v i)) <= B * gibbs_average c f I r).
  { rewrite <- gibbs_average_scale; apply gibbs_average_monotone; assumption. }
  assert (Huv : gibbs_average c f I (fun i => Rabs (u i) * Rabs (v i)) <=
    A * B * gibbs_average c f I (fun i => r i ^ 3)).
  { rewrite <- gibbs_average_scale; apply gibbs_average_monotone; [exact HI|].
    intros i Hi.
    pose proof (Rmult_le_compat (Rabs (u i)) (A * r i ^ 2)
      (Rabs (v i)) (B * r i) (Rabs_pos (u i)) (Rabs_pos (v i)) (Hu i Hi) (Hv i Hi)) as H.
    nra. }
  assert (Hprod : gibbs_average c f I (fun i => Rabs (u i)) *
    gibbs_average c f I (fun i => Rabs (v i)) <=
    (A * gibbs_average c f I (fun i => r i ^ 2)) * (B * gibbs_average c f I r)).
  { apply Rmult_le_compat; try assumption; apply gibbs_average_nonnegative;
      [exact HI|intros; apply Rabs_pos|exact HI|intros; apply Rabs_pos]. }
  assert (Hm' : A * B * (gibbs_average c f I (fun i => r i ^ 2) * gibbs_average c f I r) <=
    A * B * gibbs_average c f I (fun i => r i ^ 3)).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption|exact Hm]. }
  pose proof (gibbs_covariance_absolute_bound c f I u v HI); nra.
Qed.
