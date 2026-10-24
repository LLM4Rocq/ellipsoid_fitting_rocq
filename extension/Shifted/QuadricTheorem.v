(* Assembly of the explicit Gaussian quadric statement from the proved
   reserve-certificate good events. *)
From EllipsoidUniversality Require Import ShiftedQuadricStatement.
From EllipsoidUniversality.Shifted Require Import GaussianErrorLower.

Theorem shifted_quadric_theorem : shifted_quadric_statement.
Proof. exact gaussian_quadric_good_events. Qed.
