(* Derivatives of the soft min-max along arbitrary score curves. These
   connect the covariance contraction to actual first and second derivatives. *)
From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Gibbs.CurveDerivatives Gibbs.MomentBounds Gordon.Covariance.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_mean (beta gamma : R) (H U : nat -> nat -> R)
    (Y S : list nat) : R :=
  paper_main_gordon_outer beta gamma H Y S
    (fun y => paper_main_gordon_inner gamma H S y (U y)).

Definition paper_main_gordon_hessian (beta gamma : R)
    (H U V : nat -> nat -> R) (Y S : list nat) : R :=
  gamma * paper_main_gordon_outer beta gamma H Y S
    (fun y => gibbs_covariance gamma (H y) S (U y) (V y)) -
  beta * gibbs_covariance (-beta) (fun y => soft_max gamma (H y) S) Y
    (fun y => paper_main_gordon_inner gamma H S y (U y))
    (fun y => paper_main_gordon_inner gamma H S y (V y)).

Lemma paper_main_gordon_mean_bound beta gamma H U Y S M :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> Rabs (U y s) <= M) ->
  Rabs (paper_main_gordon_mean beta gamma H U Y S) <= M.
Proof.
intros HY HS HU.
unfold paper_main_gordon_mean, paper_main_gordon_outer, paper_main_gordon_inner.
apply gibbs_mean_uniform_bound; [exact HY|]; intros y Hy.
apply gibbs_mean_uniform_bound; [exact HS|]; intros s Hs; apply HU; assumption.
Qed.

Lemma paper_main_gordon_covariance_bound c f I u v A B :
  I <> [] -> 0 <= A -> 0 <= B ->
  (forall i, In i I -> Rabs (u i) <= A) ->
  (forall i, In i I -> Rabs (v i) <= B) ->
  Rabs (gibbs_covariance c f I u v) <= 2 * A * B.
Proof.
intros HI HA HB Hu Hv.
pose proof (gibbs_covariance_cubic_bound c f I u v (fun _ => 1) A B HI HA HB
  (fun i Hi => Rle_0_1)) as H.
assert (Hu' : forall i, In i I -> Rabs (u i) <= A * 1 ^ 2).
{ intros i Hi; specialize (Hu i Hi); simpl; nra. }
assert (Hv' : forall i, In i I -> Rabs (v i) <= B * 1).
{ intros i Hi; specialize (Hv i Hi); nra. }
specialize (H Hu' Hv').
cbv beta in H.
rewrite gibbs_average_const in H by exact HI.
simpl in H; nra.
Qed.

Lemma paper_main_gordon_hessian_bound beta gamma H U V Y S A B :
  0 <= beta -> 0 <= gamma -> Y <> [] -> S <> [] -> 0 <= A -> 0 <= B ->
  (forall y s, In y Y -> In s S -> Rabs (U y s) <= A) ->
  (forall y s, In y Y -> In s S -> Rabs (V y s) <= B) ->
  Rabs (paper_main_gordon_hessian beta gamma H U V Y S) <=
    2 * (beta + gamma) * A * B.
Proof.
intros Hb Hg HY HS HA HB HU HV.
assert (Hi : Rabs (paper_main_gordon_outer beta gamma H Y S
  (fun y => gibbs_covariance gamma (H y) S (U y) (V y))) <= 2 * A * B).
{ unfold paper_main_gordon_outer; apply gibbs_mean_uniform_bound; [exact HY|].
  intros y Hy; apply paper_main_gordon_covariance_bound; try assumption.
  - intros s Hs; apply HU; assumption.
  - intros s Hs; apply HV; assumption. }
assert (Ho : Rabs (gibbs_covariance (-beta) (fun y => soft_max gamma (H y) S) Y
  (fun y => paper_main_gordon_inner gamma H S y (U y))
  (fun y => paper_main_gordon_inner gamma H S y (V y))) <= 2 * A * B).
{ apply paper_main_gordon_covariance_bound; try assumption.
  - intros y Hy; unfold paper_main_gordon_inner.
    apply gibbs_mean_uniform_bound; [exact HS|]; intros s Hs; apply HU; assumption.
  - intros y Hy; unfold paper_main_gordon_inner.
    apply gibbs_mean_uniform_bound; [exact HS|]; intros s Hs; apply HV; assumption. }
unfold paper_main_gordon_hessian.
eapply Rle_trans; [apply Rabs_triang|].
rewrite Rabs_Ropp, !Rabs_mult, (Rabs_pos_eq gamma Hg), (Rabs_pos_eq beta Hb).
nra.
Qed.
