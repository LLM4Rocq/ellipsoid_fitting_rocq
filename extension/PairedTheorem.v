(* Exact fitting for the paired law: the proof of paired_statement of
   PairedStatement, at Stdlib's R, from the finite-mixture theorem
   (mixture_theorem of MixtureTheorem) and paired_of_mixture of
   Paired/Theorem. Item P3 of phase 6. The module Paired/Theorem is
   required by its full name, since Theorem is a keyword. *)

From mathcomp Require Import all_ssreflect_compat.
From EllipsoidUniversality Require Import PairedStatement MixtureTheorem.
Require Import EllipsoidUniversality.Paired.Theorem.

Theorem paired_theorem : paired_statement.
Proof. exact: (paired_of_mixture mixture_theorem). Qed.
