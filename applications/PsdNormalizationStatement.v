From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix reals.
From GaussianAnalysis.matrix Require Import psd_part.

(**md**************************************************************************)
(* # Exact normalization of PSD factors: the statement                        *)
(*                                                                            *)
(* Target T10 of phase 13 (AGENTS.md, section Phase 13; the plan              *)
(* notes/phase13-plan.md, section 2). The statement of a Rocq formalization   *)
(* of the credited argument of the lemma 'Normalization of PSD factors' of    *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/matching.tex, lines 13-39), in a general form. This file   *)
(* holds the statement only. The Lean development of the collection proves a  *)
(* regularized form:                                                          *)
(* Lean: exists_normalized_factors (DeterminantNormalization.lean, line 133)  *)
(*                                                                            *)
(* Setting. R is any realType, I and J are finite types with J nonempty, r is *)
(* a natural number, and F i, G j are positive semidefinite matrices of       *)
(* 'M[R]_r: psdmx (matrix/psd_part.v) says that a matrix is symmetric and     *)
(* that x^T A x >= 0 for every column x. \tr is the trace of MathComp. The    *)
(* pairings tr (F i G j) are the entries of the factorized matrix.            *)
(*                                                                            *)
(* psd_normalization_statement: if every pairing tr (F i G j) is at most m,   *)
(* there are positive semidefinite F' i and G' j of the same size r with the  *)
(* same pairings, tr (F' i G' j) = tr (F i G j), whose row traces are at most *)
(* m, tr (F' i) <= m, and whose column traces are at most r, tr (G' j) <= r.  *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - The exact form decided by the user on 14 October 2026 (D9): the bound m  *)
(*   of the pairings bounds the row traces, with no loss, and the size r is   *)
(*   kept. The manuscript states the lemma for a nonzero matrix with entries  *)
(*   at most B and gets a factorization of a size at most r; its proof        *)
(*   compresses the factors to the span of the column factors. A              *)
(*   factorization of a size s <= r pads by zero blocks to the size r, so the *)
(*   two forms are equivalent; the proof here keeps the size r directly, by   *)
(*   compressing the row factors with the projection onto the range of the    *)
(*   column factors. The Lean development maximizes the determinant over eps  *)
(*   I + conv(G_j) and gets row traces at most m + 1; a compactness step, or  *)
(*   the compression, removes the loss.                                       *)
(* - J is nonempty: with no column, the pairing bound says nothing, and no    *)
(*   positive semidefinite F' i has a trace at most m < 0. Rows need no       *)
(*   assumption: with no row the row condition is empty, and with rows and    *)
(*   columns the pairing bound forces m >= 0. The size r = 0 is allowed; then *)
(*   every factor is zero.                                                    *)
(* - The matrix that is factorized does not appear: its entries are the       *)
(*   pairings tr (F i G j). The predicate psd_factorization of                *)
(*   matrix/psd_factorization.v is not used, so that the statement unfolds    *)
(*   only to psdmx, already protected, and to MathComp.                       *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition psd_normalization_statement : Prop :=
  forall (R : realType) (I J : finType) (r : nat)
         (F : I -> 'M[R]_r) (G : J -> 'M[R]_r) (m : R),
  (0 < #|J|)%N ->
  (forall i, psdmx (F i)) -> (forall j, psdmx (G j)) ->
  (forall i j, \tr (F i *m G j) <= m) ->
  exists (F' : I -> 'M[R]_r) (G' : J -> 'M[R]_r),
    [/\ forall i, psdmx (F' i), forall j, psdmx (G' j),
        forall i j, \tr (F' i *m G' j) = \tr (F i *m G j),
        forall i, \tr (F' i) <= m &
        forall j, \tr (G' j) <= r%:R].
