(* The identity driver of the statement snapshot SnapshotPhase6 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase6.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase6.json. *)

Require EllipsoidUniversality.MixtureDefinitions.
Require EllipsoidUniversality.MixtureStatement.
Require EllipsoidUniversality.PairedDefinitions.
Require EllipsoidUniversality.PairedStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.MixtureDefinitions.mixture_component_law".
KernelIdentity "definition" "EllipsoidUniversality.MixtureDefinitions.mixture_family".
KernelIdentity "definition" "EllipsoidUniversality.MixtureDefinitions.mixture_fourth_moment".
KernelIdentity "definition" "EllipsoidUniversality.MixtureDefinitions.mixture_label".
KernelIdentity "definition" "EllipsoidUniversality.MixtureDefinitions.mixture_labelled_law".
KernelIdentity "definition" "EllipsoidUniversality.MixtureDefinitions.mixture_probability".
KernelIdentity "definition" "EllipsoidUniversality.MixtureDefinitions.mixture_interpolation".
KernelIdentity "definition" "EllipsoidUniversality.MixtureStatement.mixture_statement".
KernelIdentity "definition" "EllipsoidUniversality.MixtureStatement.mixture_interpolation_statement".
KernelIdentity "definition" "EllipsoidUniversality.MixtureStatement.mixture_theorem_statement".
KernelIdentity "definition" "EllipsoidUniversality.PairedDefinitions.paired_uniform_spec".
KernelIdentity "definition" "EllipsoidUniversality.PairedDefinitions.paired_kernel".
KernelIdentity "definition" "EllipsoidUniversality.PairedDefinitions.paired_pair_density".
KernelIdentity "definition" "EllipsoidUniversality.PairedDefinitions.paired_sample_density".
KernelIdentity "definition" "EllipsoidUniversality.PairedDefinitions.paired_probability".
KernelIdentity "definition" "EllipsoidUniversality.PairedStatement.paired_statement".
