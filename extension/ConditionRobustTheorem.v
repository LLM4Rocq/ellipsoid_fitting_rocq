(* Robustness of the optimal condition number at fourth moment three: the
   statement robust_condition_theorem_statement of ConditionRobustStatement,
   proved. Item R7 of phase 10.

   robust_condition_holds and robust_condition_number_holds
   (Condition/RobustCondition) carry the threshold (20) and the limit (21)
   of condition_theorem, for countable families of fourth moment 3, over to
   the samples of laws P d with d^2 tv(P d, nu_d) -> 0, through the
   transfer bound of Countable/Robust. *)

From EllipsoidUniversality Require Import ConditionRobustStatement.
From EllipsoidUniversality.Condition Require Import RobustCondition.

Theorem robust_condition_theorem : robust_condition_theorem_statement.
Proof. exact robust_condition_theorem_holds. Qed.
