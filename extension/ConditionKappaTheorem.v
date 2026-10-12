(* The condition-number theorem at every fourth moment kappa > 1: the
   statement condition_kappa_theorem_statement of ConditionKappaStatement,
   proved. Item A1 of phase 11.

   condition_kappa_statement_of_I3 (ConditionKappa/Theorem) proves (20) for
   finite mixtures from the two halves of items D1 and D2, with interface
   I1 discharged there by kcond_support_cvg (ConditionKappa/GaussianLimit,
   item M5); the three forms of interface I3 are supplied here by
   condition_kappa_alpha_left, condition_kappa_alpha_half and
   condition_kappa_alpha_right (ConditionKappa/Curve, item S3).
   condition_kappa_number_of_threshold derives (21) from it with the inverse
   of the curve, supplied here by condition_kappa_inverse_holds
   (ConditionKappa/Curve). The countable versions follow from the finite
   ones by countable_condition_kappa_holds and
   countable_condition_kappa_number_holds, through the truncation of the
   family and the coupling of samples (ConditionKappa/Countable, item A2). *)

From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From EllipsoidUniversality Require Import ConditionKappaStatement.
From EllipsoidUniversality.ConditionKappa Require Import Curve Countable.
Require Import EllipsoidUniversality.ConditionKappa.Theorem.

Theorem condition_kappa_theorem : condition_kappa_theorem_statement.
Proof.
have h20 : condition_kappa_statement.
  apply: condition_kappa_statement_of_I3.
  - exact: condition_kappa_alpha_left.
  - exact: condition_kappa_alpha_half.
  - exact: condition_kappa_alpha_right.
have h21 := condition_kappa_number_of_threshold h20
  condition_kappa_inverse_holds.
split => //.
  exact: countable_condition_kappa_holds.
exact: countable_condition_kappa_number_holds.
Qed.
