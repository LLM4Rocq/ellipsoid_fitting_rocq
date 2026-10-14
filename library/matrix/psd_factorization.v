From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix reals.
From GaussianAnalysis.matrix Require Import psd_part.

(**md**************************************************************************)
(* # PSD factorizations                                                       *)
(*                                                                            *)
(* A real PSD factorization of size r of a matrix A : I -> J -> R, indexed by *)
(* two finite types, is a family of positive semidefinite r x r matrices F i  *)
(* for the rows and G j for the columns with A i j = tr (F i G j) for all i   *)
(* and j (psd_factorization A r). The PSD rank of A is the least such r; this *)
(* file does not define it, and the statements that use it are written for    *)
(* every factorization of a given size.                                       *)
(*                                                                            *)
(* The general statements of this file are compiled Prop definitions, for     *)
(* review with batch 2 of phase 13 (AGENTS.md, section Phase 13, step 0,      *)
(* items 3 and 4); their proofs follow their acceptance.                      *)
(*                                                                            *)
(* - psd_factorization_ge0_statement: the entries of a matrix with a PSD      *)
(*   factorization are nonnegative.                                           *)
(* - psd_factorization_size_gt0_statement: a factorization of a matrix with a *)
(*   nonzero entry has a positive size.                                       *)
(* - psd_factorization_restrict_statement: a factorization restricts to the   *)
(*   rows and columns of any maps I' -> I and J' -> J.                        *)
(* - psd_factorization_widen_statement: a factorization of size r gives one   *)
(*   of every size s >= r, by zero blocks.                                    *)
(* - psd_factorization_shift_statement: a factorization of A of size r gives  *)
(*   one of A + rho of size r + 1 for rho >= 0, by a block of size one.       *)
(* - psd_factorization_nonneg_statement: a nonnegative factorization A i j =  *)
(*   sum_(k < r) a i k b j k, with a, b >= 0, gives a PSD factorization of    *)
(*   size r, by diagonal matrices; it gives the factorization of A_n(1) of    *)
(*   size the number of edges of introduction.tex, lines 46-50.               *)
(*                                                                            *)
(* The exact normalization of the factors, target T10 of phase 13, is stated  *)
(* in applications/PsdNormalizationStatement.v, written out with psdmx and    *)
(* the trace.                                                                 *)
(*                                                                            *)
(* These are Rocq formalizations of the credited arguments of 'Exponential    *)
(* PSD rank of positively shifted matching matrices' (family 126 of the       *)
(* OpenAI math collection, revision 1581d4cbd): the definition of a PSD       *)
(* factorization (source/sections/introduction.tex, lines 25-35), the lemma   *)
(* 'Normalization of PSD factors' (source/sections/matching.tex, lines        *)
(* 13-39), and the padding of the proof of the corollary on semidefinite      *)
(* lifts (introduction.tex, lines 82-86). The Lean development of the         *)
(* collection for family 126 has the diagonal factorization of a nonnegative  *)
(* matrix and the normalization, in these declarations:                       *)
(* Lean: exists_diagonal_factorization (FiniteFactorization.lean, line 69)    *)
(* Lean: exists_normalized_factors (DeterminantNormalization.lean, line 133)  *)
(*                                                                            *)
(* ```                                                                        *)
(*   psd_factorization A r == there are PSD matrices F i and G j of size r    *)
(*                            with A i j = \tr (F i *m G j) for all i and j   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section factorization.
Variable R : realType.

(* A real PSD factorization of size r of A: PSD factors F i for the rows and
   G j for the columns, with the entries as their trace pairings. *)
Definition psd_factorization (I J : finType) (A : I -> J -> R) (r : nat) :
    Prop :=
  exists (F : I -> 'M[R]_r) (G : J -> 'M[R]_r),
    [/\ forall i, psdmx (F i), forall j, psdmx (G j) &
        forall i j, A i j = \tr (F i *m G j)].

End factorization.

(* The general statements, for review. *)

(* The trace of the product of two PSD matrices is nonnegative. *)
Definition psd_factorization_ge0_statement : Prop :=
  forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat),
  psd_factorization A r -> forall i j, 0 <= A i j.

(* A factorization of size 0 has only zero entries. *)
Definition psd_factorization_size_gt0_statement : Prop :=
  forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat),
  psd_factorization A r -> (exists i j, A i j != 0) -> (0 < r)%N.

(* Restriction to rows and columns, along any maps. *)
Definition psd_factorization_restrict_statement : Prop :=
  forall (R : realType) (I J I' J' : finType) (A : I -> J -> R) (r : nat)
         (f : I' -> I) (g : J' -> J),
  psd_factorization A r -> psd_factorization (fun i j => A (f i) (g j)) r.

(* Padding the factors with zero blocks. *)
Definition psd_factorization_widen_statement : Prop :=
  forall (R : realType) (I J : finType) (A : I -> J -> R) (r s : nat),
  (r <= s)%N -> psd_factorization A r -> psd_factorization A s.

(* Appending the scalar blocks rho to the row factors and 1 to the column
   factors. *)
Definition psd_factorization_shift_statement : Prop :=
  forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat) (rho : R),
  0 <= rho -> psd_factorization A r ->
  psd_factorization (fun i j => A i j + rho) r.+1.

(* A nonnegative factorization of size r gives a PSD factorization of size r,
   by diagonal factors. *)
Definition psd_factorization_nonneg_statement : Prop :=
  forall (R : realType) (I J : finType) (r : nat) (a : I -> 'I_r -> R)
         (b : J -> 'I_r -> R),
  (forall i k, 0 <= a i k) -> (forall j k, 0 <= b j k) ->
  psd_factorization (fun i j => \sum_(k < r) a i k * b j k) r.
