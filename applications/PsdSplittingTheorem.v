From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear reals.
From GaussianAnalysis.matrix Require Import euclidean psd_part psd_splitting.
From GaussianApplications Require Import PsdSplittingStatement.

(**md**************************************************************************)
(* # Orthogonal splitting of positive semidefinite matrices: the theorem      *)
(*                                                                            *)
(* Target T5 of phase 12 (AGENTS.md, section Phase 12). psd_splitting_theorem *)
(* proves psd_splitting_statement of PsdSplittingStatement.v, the lemma       *)
(* 'Orthogonal splitting' of 'Exponential PSD rank of positively shifted      *)
(* matching matrices' (family 126 of the OpenAI math collection, revision     *)
(* 1581d4cbd, source/sections/splitting.tex), from psd_splitting of           *)
(* library/matrix/psd_splitting.v, a Rocq formalization of the credited       *)
(* argument. The statement indexes L >= 1 matrices by 'I_L; the library lemma *)
(* takes L + 1 matrices, with constant 2^L.                                   *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Theorem psd_splitting_theorem : psd_splitting_statement.
Proof.
move=> R n [//|L] A _ Ap.
have [P [Po Porth Psum Pb]] := psd_splitting Ap.
by exists P; split => // s; exact: Po.
Qed.
