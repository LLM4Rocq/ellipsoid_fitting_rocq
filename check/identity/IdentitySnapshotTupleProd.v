(* The identity driver of the statement snapshot SnapshotTupleProd (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotTupleProd.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotTupleProd.json. *)

Require GaussianAnalysis.probability.lindeberg.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "GaussianAnalysis.probability.lindeberg.tuple_cons".
KernelIdentity "type" "GaussianAnalysis.probability.lindeberg.measurable_tuple_cons".
KernelIdentity "definition" "GaussianAnalysis.probability.lindeberg.HB_unnamed_factory_2".
KernelIdentity "definition" "GaussianAnalysis.probability.lindeberg.lindeberg_tuple_cons__canonical__measurable_function_MeasurableFun".
KernelIdentity "definition" "GaussianAnalysis.probability.lindeberg.tuple_prod".
