From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights GibbsDerivatives.
Import ListNotations.
Open Scope R_scope.

Lemma affine_curve_derivative (a b x : R) :
  derivable_pt_lim (fun t => a + t * b) x b.
Proof.
  assert (H0 : derivable_pt_lim (fun _ => a) x 0)
    by apply derivable_pt_lim_const.
  assert (H1 : derivable_pt_lim (fun t => t * b) x (1 * b)).
  { apply derivable_pt_lim_scal_right, derivable_pt_lim_id. }
  pose proof (derivable_pt_lim_plus (fun _ => a) (fun t => t * b)
    x 0 (1 * b) H0 H1) as HD.
  rewrite Rmult_1_l, Rplus_0_l in HD; exact HD.
Qed.

(* A fixed observable changes along an affine score direction by covariance.
   The inverse temperature may have either sign. *)
Theorem affine_gibbs_average_derivative (c : R) (a b u : nat -> R)
    (I : list nat) (x : R) :
  I <> [] ->
  derivable_pt_lim
    (fun t => gibbs_average c (fun i => a i + t * b i) I u) x
    (c * gibbs_covariance c (fun i => a i + x * b i) I u b).
Proof.
  intros HI.
  pose proof (gibbs_average_derivative c (fun i t => a i + t * b i) b
    (fun i _ => u i) (fun _ => 0) I x HI) as HD.
  assert (HA : forall i, In i I ->
    derivable_pt_lim (fun t => a i + t * b i) x (b i)).
  { intros; apply affine_curve_derivative. }
  assert (HU : forall i, In i I -> derivable_pt_lim (fun _ => u i) x 0).
  { intros; apply derivable_pt_lim_const. }
  specialize (HD HA HU).
  rewrite gibbs_average_const in HD by exact HI.
  rewrite Rplus_0_l in HD; exact HD.
Qed.

Theorem inner_scores_derivative (gamma : R) (a b : nat -> nat -> R)
    (S : list nat) (x : R) (y : nat) :
  0 < gamma -> S <> [] ->
  derivable_pt_lim (fun t => inner_scores gamma a b S t y) x
    (inner_means gamma a b S x y).
Proof.
  intros Hg HS; unfold inner_scores, inner_means.
  apply (soft_max_curve_derivative gamma
    (fun s t => affine_scores a b t y s) (b y) S x).
  - lra.
  - exact HS.
  - intros; unfold affine_scores; apply affine_curve_derivative.
Qed.

Theorem inner_means_derivative (gamma : R) (a b : nat -> nat -> R)
    (S : list nat) (x : R) (y : nat) :
  S <> [] ->
  derivable_pt_lim (fun t => inner_means gamma a b S t y) x
    (gamma * inner_variances gamma a b S x y).
Proof.
  intros HS; unfold inner_means, inner_variances, gibbs_variance, affine_scores.
  apply affine_gibbs_average_derivative; exact HS.
Qed.

Theorem nested_soft_minimax_derivative (beta gamma : R)
    (a b : nat -> nat -> R) (Y S : list nat) (x : R) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  derivable_pt_lim
    (fun t => soft_minimax beta gamma (affine_scores a b t) Y S) x
    (nested_gibbs_mean beta gamma a b Y S x).
Proof.
  intros Hb Hg HY HS; unfold soft_minimax, nested_gibbs_mean.
  change (derivable_pt_lim
    (fun t => soft_min beta (inner_scores gamma a b S t) Y) x
    (gibbs_average (- beta) (inner_scores gamma a b S x) Y
      (inner_means gamma a b S x))).
  apply (soft_min_curve_derivative beta
    (fun y t => inner_scores gamma a b S t y)
    (inner_means gamma a b S x) Y x).
  - lra.
  - exact HY.
  - intros; apply inner_scores_derivative; assumption.
Qed.

Theorem nested_gibbs_mean_derivative (beta gamma : R)
    (a b : nat -> nat -> R) (Y S : list nat) (x : R) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  derivable_pt_lim (nested_gibbs_mean beta gamma a b Y S) x
    (nested_gibbs_curvature beta gamma a b Y S x).
Proof.
  intros Hb Hg HY HS.
  pose proof (gibbs_average_derivative (- beta)
    (fun y t => inner_scores gamma a b S t y)
    (inner_means gamma a b S x)
    (fun y t => inner_means gamma a b S t y)
    (fun y => gamma * inner_variances gamma a b S x y) Y x HY) as HD.
  assert (HF : forall y, In y Y ->
    derivable_pt_lim (fun t => inner_scores gamma a b S t y) x
      (inner_means gamma a b S x y)).
  { intros; apply inner_scores_derivative; assumption. }
  assert (HU : forall y, In y Y ->
    derivable_pt_lim (fun t => inner_means gamma a b S t y) x
      (gamma * inner_variances gamma a b S x y)).
  { intros; apply inner_means_derivative; exact HS. }
  specialize (HD HF HU).
  rewrite gibbs_average_scale in HD.
  unfold nested_gibbs_mean, nested_gibbs_curvature, gibbs_variance.
  replace (gamma * gibbs_average (- beta) (inner_scores gamma a b S x) Y
    (inner_variances gamma a b S x) -
    beta * gibbs_covariance (- beta) (inner_scores gamma a b S x) Y
      (inner_means gamma a b S x) (inner_means gamma a b S x)) with
    (gamma * gibbs_average (- beta) (inner_scores gamma a b S x) Y
      (inner_variances gamma a b S x) +
     (- beta) * gibbs_covariance (- beta) (inner_scores gamma a b S x) Y
      (inner_means gamma a b S x) (inner_means gamma a b S x)) by ring.
  exact HD.
Qed.

Theorem nested_soft_minimax_derivatives (beta gamma : R)
    (a b : nat -> nat -> R) (Y S : list nat) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  forall x,
  derivable_pt_lim
    (fun t => soft_minimax beta gamma (affine_scores a b t) Y S) x
    (nested_gibbs_mean beta gamma a b Y S x) /\
  derivable_pt_lim (nested_gibbs_mean beta gamma a b Y S) x
    (nested_gibbs_curvature beta gamma a b Y S x).
Proof.
  intros Hb Hg HY HS x; split.
  - apply nested_soft_minimax_derivative; assumption.
  - apply nested_gibbs_mean_derivative; assumption.
Qed.
