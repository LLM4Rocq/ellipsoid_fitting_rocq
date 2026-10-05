(* Prints the axioms on which the main theorem depends. `make check`
   compares the output with check/assumptions.expected. *)
From EllipsoidFitting Require Import MainTheorem.

Print Assumptions ellipsoid_fitting_main.
