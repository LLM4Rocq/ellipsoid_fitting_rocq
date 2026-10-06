From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions.
Open Scope R_scope.

(* Finite Gibbs laws. The law at inverse temperature c of scores f on a
   list I gives the index i the weight exp (c * f i) / partition c f I
   (gibbs_weight); gibbs_average, gibbs_covariance and gibbs_variance are
   the mean, covariance and variance under it. For the scores
   a y s + t * b y s (affine_scores), inner_scores is the soft maximum over
   s in S, and inner_means and inner_variances are the Gibbs mean and
   variance of b y. nested_gibbs_curvature is gamma times the outer average
   of the inner variances minus beta times the outer variance of the inner
   means, the outer law being that of inner_scores over Y at inverse
   temperature - beta. *)

(* A signed inverse temperature treats the inner soft maximum (c > 0)
   and the outer soft minimum (c < 0) with the same finite Gibbs law. *)
Definition partition (c : R) (f : nat -> R) (I : list nat) : R :=
  finite_sum (fun i => exp (c * f i)) I.

Definition gibbs_weight (c : R) (f : nat -> R) (I : list nat) (i : nat) : R :=
  exp (c * f i) / partition c f I.

Definition gibbs_average (c : R) (f : nat -> R) (I : list nat)
    (h : nat -> R) : R :=
  finite_sum (fun i => gibbs_weight c f I i * h i) I.

Definition gibbs_covariance (c : R) (f : nat -> R) (I : list nat)
    (u v : nat -> R) : R :=
  gibbs_average c f I (fun i => u i * v i) -
  gibbs_average c f I u * gibbs_average c f I v.

Definition gibbs_variance (c : R) (f : nat -> R) (I : list nat)
    (u : nat -> R) : R := gibbs_covariance c f I u u.

Definition affine_scores (a b : nat -> nat -> R) (t : R) (y s : nat) : R :=
  a y s + t * b y s.

Definition inner_scores (gamma : R) (a b : nat -> nat -> R)
    (S : list nat) (t : R) (y : nat) : R :=
  soft_max gamma (affine_scores a b t y) S.

Definition inner_means (gamma : R) (a b : nat -> nat -> R)
    (S : list nat) (t : R) (y : nat) : R :=
  gibbs_average gamma (affine_scores a b t y) S (b y).

Definition inner_variances (gamma : R) (a b : nat -> nat -> R)
    (S : list nat) (t : R) (y : nat) : R :=
  gibbs_variance gamma (affine_scores a b t y) S (b y).

Definition nested_gibbs_curvature (beta gamma : R) (a b : nat -> nat -> R)
    (Y S : list nat) (t : R) : R :=
  gamma * gibbs_average (- beta) (inner_scores gamma a b S t) Y
    (inner_variances gamma a b S t) -
  beta * gibbs_variance (- beta) (inner_scores gamma a b S t) Y
    (inner_means gamma a b S t).
