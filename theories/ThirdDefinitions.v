From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions.
Open Scope R_scope.

Definition gibbs_cumulant3 (c : R) (f : nat -> R) (I : list nat)
    (u v w : nat -> R) : R :=
  gibbs_average c f I (fun i =>
    (u i - gibbs_average c f I u) *
    (v i - gibbs_average c f I v) *
    (w i - gibbs_average c f I w)).
