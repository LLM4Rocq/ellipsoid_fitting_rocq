(* The curve of the optimal condition number at fourth moment kappa: the
   statement condition_kappa_curve_statement of
   ConditionKappaCurveStatement, proved. Phase 11.

   For kappa > 1: the root u of F (condition_kappa_root_holds,
   ConditionKappa/Scalar, item S1); alpha(C, kappa) is the value of the
   variational problem over the profiles admissible for C
   (condition_kappa_variational_holds, ConditionKappa/Curve, item S2); its
   integral formula (condition_kappa_integral_holds, ConditionKappa/Integral,
   item S5); the range, the strict increase, the continuity and the limits
   of C |-> alpha(C, kappa) (condition_kappa_range_holds) and the inverse
   C_star(alpha, kappa) (condition_kappa_inverse_holds), both in
   ConditionKappa/Curve, item S3. At kappa = 3, the curve and its inverse
   are those of ConditionDefinitions (condition_kappa_three_holds,
   ConditionKappa/Compatibility, item S4). *)

From EllipsoidUniversality Require Import ConditionKappaCurveStatement.
From EllipsoidUniversality.ConditionKappa Require Import Scalar Curve.
From EllipsoidUniversality.ConditionKappa Require Import Integral Compatibility.

Theorem condition_kappa_curve_theorem : condition_kappa_curve_statement.
Proof.
split.
- intros kappa k1; split.
  + exact (condition_kappa_root_holds kappa k1).
  + exact (condition_kappa_variational_holds kappa k1).
  + exact (condition_kappa_integral_holds kappa k1).
  + exact (condition_kappa_range_holds kappa k1).
  + exact (condition_kappa_inverse_holds kappa k1).
- exact condition_kappa_three_holds.
Qed.
