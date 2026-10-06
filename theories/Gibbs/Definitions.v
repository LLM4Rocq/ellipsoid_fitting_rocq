From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions.
Open Scope R_scope.

(* Finite Gibbs laws. The law at inverse temperature c of scores f on a
   list I gives the index i the weight exp (c * f i) / partition c f I
   (gibbs_weight); gibbs_average and gibbs_covariance are the mean of an
   observable and the covariance of two observables under it. *)

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
