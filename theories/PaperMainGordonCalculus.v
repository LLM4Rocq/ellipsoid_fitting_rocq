(* Derivatives of the soft min-max along arbitrary score curves. These
   connect the covariance contraction to actual first and second derivatives. *)
From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights
  GibbsDerivatives GibbsNested GibbsMomentBounds PaperMainGordonCovariance.
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

Lemma paper_main_gordon_hessian_diagonal beta gamma H U Y S :
  paper_main_gordon_hessian beta gamma H U U Y S =
  nested_gibbs_curvature beta gamma H U Y S 0.
Proof. symmetry; apply paper_main_gordon_curvatureE. Qed.

Lemma paper_main_gordon_meanE beta gamma H U Y S :
  paper_main_gordon_mean beta gamma H U Y S =
  nested_gibbs_mean beta gamma H U Y S 0.
Proof.
assert (H0 : affine_scores H U 0 = H).
{ extensionality y; extensionality s; unfold affine_scores; ring. }
unfold nested_gibbs_mean, inner_scores, inner_means, paper_main_gordon_mean,
  paper_main_gordon_outer, paper_main_gordon_inner.
rewrite H0; reflexivity.
Qed.

Theorem paper_main_gordon_curve_derivative beta gamma
    (F : R -> nat -> nat -> R) (D : nat -> nat -> R) Y S x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S ->
    derivable_pt_lim (fun t => F t y s) x (D y s)) ->
  derivable_pt_lim (fun t => soft_minimax beta gamma (F t) Y S) x
    (paper_main_gordon_mean beta gamma (F x) D Y S).
Proof.
intros Hb Hg HY HS HD.
unfold soft_minimax, paper_main_gordon_mean, paper_main_gordon_outer,
  paper_main_gordon_inner.
apply (soft_min_curve_derivative beta
  (fun y t => soft_max gamma (F t y) S)
  (fun y => gibbs_average gamma (F x y) S (D y)) Y x).
- lra.
- exact HY.
- intros y Hy.
  apply (soft_max_curve_derivative gamma (fun s t => F t y s) (D y) S x).
  + lra.
  + exact HS.
  + intros s Hs; apply HD; assumption.
Qed.

Theorem paper_main_gordon_mean_curve_derivative beta gamma
    (F U : R -> nat -> nat -> R) (D V : nat -> nat -> R) Y S x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S ->
    derivable_pt_lim (fun t => F t y s) x (D y s)) ->
  (forall y s, In y Y -> In s S ->
    derivable_pt_lim (fun t => U t y s) x (V y s)) ->
  derivable_pt_lim (fun t => paper_main_gordon_mean beta gamma (F t) (U t) Y S) x
    (paper_main_gordon_mean beta gamma (F x) V Y S +
      paper_main_gordon_hessian beta gamma (F x) (U x) D Y S).
Proof.
intros Hb Hg HY HS HD HV.
assert (HF : forall y, In y Y -> derivable_pt_lim
  (fun t => soft_max gamma (F t y) S) x
  (gibbs_average gamma (F x y) S (D y))).
{ intros y Hy; apply (soft_max_curve_derivative gamma
    (fun s t => F t y s) (D y) S x); try lra; try assumption.
  intros s Hs; apply HD; assumption. }
assert (HU : forall y, In y Y -> derivable_pt_lim
  (fun t => gibbs_average gamma (F t y) S (U t y)) x
  (gibbs_average gamma (F x y) S (V y) +
    gamma * gibbs_covariance gamma (F x y) S (U x y) (D y))).
{ intros y Hy; apply (gibbs_average_derivative gamma
    (fun s t => F t y s) (D y) (fun s t => U t y s) (V y) S x).
  - exact HS.
  - intros s Hs; apply HD; assumption.
  - intros s Hs; apply HV; assumption. }
pose proof (gibbs_average_derivative (-beta)
  (fun y t => soft_max gamma (F t y) S)
  (fun y => gibbs_average gamma (F x y) S (D y))
  (fun y t => gibbs_average gamma (F t y) S (U t y))
  (fun y => gibbs_average gamma (F x y) S (V y) +
    gamma * gibbs_covariance gamma (F x y) S (U x y) (D y)) Y x HY HF HU) as HH.
rewrite gibbs_average_add, gibbs_average_scale in HH.
unfold paper_main_gordon_mean, paper_main_gordon_hessian,
  paper_main_gordon_outer, paper_main_gordon_inner.
replace (gibbs_average (- beta) (fun y => soft_max gamma (F x y) S) Y
  (fun y => gibbs_average gamma (F x y) S (V y)) +
  (gamma * gibbs_average (- beta) (fun y => soft_max gamma (F x y) S) Y
    (fun y => gibbs_covariance gamma (F x y) S (U x y) (D y)) -
   beta * gibbs_covariance (- beta) (fun y => soft_max gamma (F x y) S) Y
    (fun y => gibbs_average gamma (F x y) S (U x y))
    (fun y => gibbs_average gamma (F x y) S (D y))))
with ((gibbs_average (- beta) (fun y => soft_max gamma (F x y) S) Y
  (fun y => gibbs_average gamma (F x y) S (V y)) +
  gamma * gibbs_average (- beta) (fun y => soft_max gamma (F x y) S) Y
    (fun y => gibbs_covariance gamma (F x y) S (U x y) (D y))) +
   (- beta) * gibbs_covariance (- beta) (fun y => soft_max gamma (F x y) S) Y
    (fun y => gibbs_average gamma (F x y) S (U x y))
    (fun y => gibbs_average gamma (F x y) S (D y))) by ring.
exact HH.
Qed.

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
