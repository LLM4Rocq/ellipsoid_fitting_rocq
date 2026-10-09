(* The condition-number theorem at fourth moment three: the statement
   condition_theorem_statement of ConditionStatement, proved. Item Q9 of
   phase 8.

   condition_statement_holds (Condition/Theorem) proves (20) for finite
   mixtures, and condition_number_of_threshold derives (21) from it. The
   countable versions follow from the finite ones by the truncation of the
   family and the coupling of samples (Condition/Countable). *)

From EllipsoidUniversality Require Import ConditionStatement.
Require Import EllipsoidUniversality.Condition.Theorem.
From EllipsoidUniversality.Condition Require Import Countable.

Theorem condition_theorem : condition_theorem_statement.
Proof.
pose proof condition_statement_holds as h20.
pose proof (condition_number_of_threshold h20) as h21.
split; [exact h20 | exact h21 | exact (countable_condition_holds h20) |
  exact (countable_condition_number_holds h21)].
Qed.
