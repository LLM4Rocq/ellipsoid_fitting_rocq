From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions.
Open Scope R_scope.

Definition gibbs_cumulant3 (c : R) (f : nat -> R) (I : list nat)
    (u v w : nat -> R) : R :=
  gibbs_average c f I (fun i =>
    (u i - gibbs_average c f I u) *
    (v i - gibbs_average c f I v) *
    (w i - gibbs_average c f I w)).

Definition gibbs_third_central (c : R) (f : nat -> R) (I : list nat)
    (u : nat -> R) : R := gibbs_cumulant3 c f I u u u.

Definition curve_gibbs_mean (c : R) (F D : nat -> R -> R)
    (I : list nat) (t : R) : R :=
  gibbs_average c (fun i => F i t) I (fun i => D i t).

Definition curve_gibbs_curvature (c : R) (F D B : nat -> R -> R)
    (I : list nat) (t : R) : R :=
  gibbs_average c (fun i => F i t) I (fun i => B i t) +
  c * gibbs_variance c (fun i => F i t) I (fun i => D i t).

Definition curve_gibbs_third (c : R) (F D B : nat -> R -> R)
    (C : nat -> R) (I : list nat) (x : R) : R :=
  gibbs_average c (fun i => F i x) I C +
  3 * c * gibbs_covariance c (fun i => F i x) I
    (fun i => D i x) (fun i => B i x) +
  c ^ 2 * gibbs_third_central c (fun i => F i x) I (fun i => D i x).

Definition inner_third_moments (gamma : R) (a b : nat -> nat -> R)
    (S : list nat) (t : R) (y : nat) : R :=
  gibbs_third_central gamma (affine_scores a b t y) S (b y).

Definition nested_gibbs_third (beta gamma : R) (a b : nat -> nat -> R)
    (Y S : list nat) (t : R) : R :=
  gamma ^ 2 * gibbs_average (- beta) (inner_scores gamma a b S t) Y
    (inner_third_moments gamma a b S t) -
  3 * beta * gamma * gibbs_covariance (- beta) (inner_scores gamma a b S t) Y
    (inner_means gamma a b S t) (inner_variances gamma a b S t) +
  beta ^ 2 * gibbs_third_central (- beta) (inner_scores gamma a b S t) Y
    (inner_means gamma a b S t).
