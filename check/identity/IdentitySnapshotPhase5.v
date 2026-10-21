(* The identity driver of the statement snapshot SnapshotPhase5 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase5.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase5.json. *)

Require EllipsoidUniversality.UniversalityDefinitions.
Require EllipsoidUniversality.UniversalityStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_power".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_subgaussian_test".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_coordinate_law".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_product_law".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_sample_law".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_probability".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_positive_part".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_semicircle_density".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_semicircle_integral".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_semicircle_integrable".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_m".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_s".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_energy".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_cutoff".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_alpha_star".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_alpha_star_variational".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_level_cutoff".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_e_star".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_fitting_error".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_pd_fit_event".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_conditioned_fit_event".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_error_event".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityDefinitions.universality_density_tends_to".
KernelIdentity "definition" "EllipsoidUniversality.UniversalityStatement.universality_statement".
