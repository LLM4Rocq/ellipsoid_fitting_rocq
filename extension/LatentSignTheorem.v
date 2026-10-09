(* Exact fitting for the latent-sign law: the proof of latent_sign_statement
   of LatentSignStatement, at Stdlib's R, from the finite-mixture theorem
   (mixture_theorem of MixtureTheorem) and latent_sign_of_mixture of
   Paired/LatentSign. Item 3 of phase 7. *)

From mathcomp Require Import all_ssreflect_compat.
From EllipsoidUniversality Require Import LatentSignStatement MixtureTheorem.
From EllipsoidUniversality.Paired Require Import LatentSign.

Theorem latent_sign_theorem : latent_sign_statement.
Proof. exact: (latent_sign_of_mixture mixture_theorem). Qed.
