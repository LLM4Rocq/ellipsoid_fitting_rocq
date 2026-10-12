(* Robustness of the condition-number theorem at every fourth moment
   kappa > 1: the statement condition_kappa_robust_theorem_statement of
   ConditionKappaRobustStatement, proved. Item A3 of phase 11.

   condition_kappa_robust_holds (ConditionKappa/Robust) carries the threshold
   (20) and the limit (21) of condition_kappa_theorem, for countable
   families of fourth moment kappa, to the samples of laws P d with
   d^2 tv(P d, nu_d) -> 0, through robust_transfer_tv of Countable/Robust
   and its exact bound n tv(P d, nu_d). A finite family is lifted to an
   admissible countable family as countable_of_finite of Countable/Theorem
   does: the weights are extended by zero and the inactive component laws,
   s >= N d, are filled with admissible laws. The zero weights keep the
   point law nu_d; the filled laws make the lifted family admissible. *)

From EllipsoidUniversality Require Import ConditionKappaRobustStatement.
From EllipsoidUniversality.ConditionKappa Require Import Robust.
From EllipsoidUniversality Require Import ConditionKappaTheorem.

Theorem condition_kappa_robust_theorem :
  condition_kappa_robust_theorem_statement.
Proof. exact (condition_kappa_robust_holds condition_kappa_theorem). Qed.
