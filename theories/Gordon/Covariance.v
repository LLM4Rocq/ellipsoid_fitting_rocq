(* Finite covariance algebra for Gordon's Gaussian min-max comparison.
   The score, weights and curvature are the already differentiated Gibbs
   functions. *)
From Stdlib Require Import Reals List Lra FunctionalExtensionality.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Gibbs.MomentBounds Chaos.CubicMassBounds.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_outer (beta gamma : R) (H : nat -> nat -> R)
    (Y S : list nat) (f : nat -> R) : R :=
  gibbs_average (-beta) (fun y => soft_max gamma (H y) S) Y f.

Definition paper_main_gordon_inner (gamma : R) (H : nat -> nat -> R)
    (S : list nat) (y : nat) (f : nat -> R) : R :=
  gibbs_average gamma (H y) S f.
