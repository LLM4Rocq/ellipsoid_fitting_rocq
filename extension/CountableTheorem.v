(* The finite-mixture theorem for countable mixtures of product laws, at
   Stdlib's R: countable_theorem proves countable_theorem_statement
   (CountableMixtureStatement.v). Item K3 of phase 8.

   countable_theorem_holds (Countable/Theorem) truncates the family at each
   dimension to a finite mixture (Countable/Truncation), applies
   mixture_theorem to it, and transfers the three conclusions and the
   interpolation property by the coupling of samples, whose error n_d r_d
   tends to 0. *)

From EllipsoidUniversality Require Import CountableMixtureStatement.
Require Import EllipsoidUniversality.Countable.Theorem.

Theorem countable_theorem : countable_theorem_statement.
Proof. exact countable_theorem_holds. Qed.
