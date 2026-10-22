(* The identity driver of the statement snapshot SnapshotPhase12Batch2 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase12Batch2.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase12Batch2.json. *)

Require GaussianApplications.TensorPackingStatement.
Require GaussianApplications.SKGapDefinitions.
Require GaussianApplications.SKGapStatement.
Require GaussianApplications.PerceptronSignDefinitions.
Require GaussianApplications.PerceptronSignStatement.
Require GaussianApplications.SatVarianceDefinitions.
Require GaussianApplications.SatVarianceStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "GaussianApplications.TensorPackingStatement.tensor_packing_statement".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.spin".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.spin_vec".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.spin_set".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_weight".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_mass".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_mean".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_var".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.half_diff".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_cond_mean".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_cond_var".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_dirichlet".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.ising_cov".
KernelIdentity "definition" "GaussianApplications.SKGapDefinitions.sk_coupling".
KernelIdentity "definition" "GaussianApplications.SKGapStatement.sk_gap_statement".
KernelIdentity "definition" "GaussianApplications.PerceptronSignDefinitions.spin_col".
KernelIdentity "definition" "GaussianApplications.PerceptronSignDefinitions.perceptron_pressure".
KernelIdentity "definition" "GaussianApplications.PerceptronSignDefinitions.gauss_pressure".
KernelIdentity "definition" "GaussianApplications.PerceptronSignDefinitions.sign_pressure".
KernelIdentity "definition" "GaussianApplications.PerceptronSignDefinitions.bounded_C3".
KernelIdentity "definition" "GaussianApplications.PerceptronSignStatement.perceptron_sign_statement".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.proper_clause".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.clause".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.clause_sat".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.prefix_sat".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.sat_cap".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.sat_prefix_len".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.sat_mean".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.sat_var".
KernelIdentity "definition" "GaussianApplications.SatVarianceDefinitions.sat_capped_var".
KernelIdentity "definition" "GaussianApplications.SatVarianceStatement.sat_variance_statement".
