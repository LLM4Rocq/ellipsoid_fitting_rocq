From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix reals.
From GaussianAnalysis.matrix Require Import psd_part psd_factorization.
From GaussianApplications Require Import PsdNormalizationStatement.

(**md**************************************************************************)
(* # Exact normalization of PSD factors: the theorem                          *)
(*                                                                            *)
(* Target T10 of phase 13 (AGENTS.md, section Phase 13):                      *)
(* psd_normalization_theorem proves psd_normalization_statement of            *)
(* PsdNormalizationStatement.v, from psd_normalization of the library file    *)
(* matrix/psd_factorization.v, whose header gives the route. A Rocq           *)
(* formalization of the credited argument of the lemma 'Normalization of PSD  *)
(* factors' of 'Exponential PSD rank of positively shifted matching matrices' *)
(* (family 126 of the OpenAI math collection, revision 1581d4cbd,             *)
(* source/sections/matching.tex, lines 13-39), with the size kept by a        *)
(* compression to the range of the column factors, where the manuscript       *)
(* restricts to their span. The Lean development of the collection proves a   *)
(* regularized form:                                                          *)
(* Lean: exists_normalized_factors (DeterminantNormalization.lean, line 133)  *)
(******************************************************************************)

Theorem psd_normalization_theorem : psd_normalization_statement.
Proof. by move=> R I J r F G m; exact: psd_normalization. Qed.
