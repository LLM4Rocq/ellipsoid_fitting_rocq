From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions.
Open Scope R_scope.

(* The third joint cumulant of a finite Gibbs law (Gibbs.Definitions):
   gibbs_cumulant3 c f I u v w is the Gibbs average of the product of the
   centred functions u - E u, v - E v and w - E w, where E is the Gibbs
   average. *)

Definition gibbs_cumulant3 (c : R) (f : nat -> R) (I : list nat)
    (u v w : nat -> R) : R :=
  gibbs_average c f I (fun i =>
    (u i - gibbs_average c f I u) *
    (v i - gibbs_average c f I v) *
    (w i - gibbs_average c f I w)).
