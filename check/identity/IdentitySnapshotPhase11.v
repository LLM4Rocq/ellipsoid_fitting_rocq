(* The identity driver of the statement snapshot SnapshotPhase11 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase11.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase11.json. *)

Require EllipsoidUniversality.ConditionKappaDefinitions.
Require EllipsoidUniversality.ConditionKappaCurveStatement.
Require EllipsoidUniversality.ConditionKappaStatement.
Require EllipsoidUniversality.ConditionKappaRobustStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_L".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_F".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_u".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_ell".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_J".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_alpha".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_star".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_objective".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_profile".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_value".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_root".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_variational".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_integral".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_range".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_inverse".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_three".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_curve_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaStatement.condition_kappa_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaStatement.condition_kappa_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaStatement.countable_condition_kappa_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaStatement.countable_condition_kappa_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaStatement.condition_kappa_theorem_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaRobustStatement.robust_condition_kappa_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaRobustStatement.robust_condition_kappa_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaRobustStatement.finite_robust_condition_kappa_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaRobustStatement.finite_robust_condition_kappa_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionKappaRobustStatement.condition_kappa_robust_theorem_statement".
