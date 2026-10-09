(* A finite tensorization constant for the latent-sign law: the proof of
   latent_tensor_upper_statement of the frozen LatentTensorUpper, at
   Stdlib's R, from latent_tensorization_finite of Paired/TensorUpper.
   Item T of phase 10. *)

From mathcomp Require Import all_ssreflect_compat.
From EllipsoidUniversality Require Import LatentTensorUpper.
From EllipsoidUniversality.Paired Require Import TensorUpper.

Theorem latent_tensor_upper_theorem : latent_tensor_upper_statement.
Proof.
move=> s mu d hs hmu.
exact: (latent_tensorization_finite s mu d hs hmu).
Qed.
