(* The universality theorem of Koehler and Sohn, "Universality and sharp
   thresholds for ellipsoid fitting" (arXiv 2608.27372, Theorem 1.2), at
   Stdlib's R: universality_theorem proves universality_statement
   (UniversalityStatement.v), the statement reviewed against the paper.
   `make check` prints its axioms and compares them with the expected list
   of the directory check/.

   universality_statement_of_interpolation (Sat/Universality) proves the
   statement from Theorem 1.9 of the paper, the small-residual
   interpolation, in the form small_residual_interpolation. Its first
   conjunct, Theorem 1.2 (i), corrects the approximate fit of Proposition
   2.1 (Sat/ApproximateFit) by Theorem 1.9; its second conjunct, Theorem
   1.2 (ii), is universality_unsat (Unsat/Universality).
   small_residual_interpolation_holds (Sat/SmallResidual) proves Theorem
   1.9 in that form. *)

From EllipsoidUniversality Require Import UniversalityStatement.
From EllipsoidUniversality.Sat Require Import Universality SmallResidual.

Theorem universality_theorem : universality_statement.
Proof.
exact (universality_statement_of_interpolation
  small_residual_interpolation_holds).
Qed.
