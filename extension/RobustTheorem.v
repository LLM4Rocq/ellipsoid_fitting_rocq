(* Robustness of the mixture theorems in total variation, at Stdlib's R:
   robust_theorem proves robust_theorem_statement (RobustStatement.v). Item
   R1 of phase 9.

   robust_statement_holds and robust_interpolation_holds (Countable/Robust)
   carry the conclusions of countable_theorem over to the samples of point
   laws P_d with d^2 tv(P_d, nu_d) -> 0: on every measurable set of samples
   the two probabilities differ by at most n_d (tv(P_d, nu_d) + 2 r_d),
   which tends to 0. contamination_holds shows that the scale d^-2 cannot
   be weakened: the contaminated family is within lambda / n_d of the
   family in total variation, and its probability of a positive definite
   fit of value one tends to expR (- lambda). *)

From EllipsoidUniversality Require Import RobustStatement.
From EllipsoidUniversality.Countable Require Import Robust.

Theorem robust_theorem : robust_theorem_statement.
Proof. exact robust_theorem_holds. Qed.
