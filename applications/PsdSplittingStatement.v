From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear reals.
From GaussianAnalysis.matrix Require Import euclidean psd_part.

(**md**************************************************************************)
(* # Orthogonal splitting of positive semidefinite matrices: the statement    *)
(*                                                                            *)
(* Target T5 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The statement of a Rocq formalization   *)
(* of the credited argument of the lemma 'Orthogonal splitting' of            *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/splitting.tex). The collection has no Lean version of it.  *)
(* This file holds the statement only.                                        *)
(*                                                                            *)
(* Setting. R is any realType, n and L are natural numbers with L >= 1, and   *)
(* A_1, ..., A_L are positive semidefinite matrices of 'M[R]_n: psdmx         *)
(* (matrix/psd_part.v) says that A is symmetric and x^T A x >= 0 for every    *)
(* column x. frobenius M is the Frobenius norm of M, the square root of mxdot *)
(* M M = sum_(i, j) M_ij^2 (matrix/euclidean.v), and \tr is the trace of      *)
(* MathComp. The indices run over 'I_L.                                       *)
(*                                                                            *)
(* psd_splitting_statement: there are P_1, ..., P_L in 'M[R]_n such that      *)
(*                                                                            *)
(* (a) every P_s is an orthogonal projection: symmetric, with P_s P_s = P_s;  *)
(*                                                                            *)
(* (b) P_s P_t = 0 for s != t, and sum_s P_s = 1;                             *)
(*                                                                            *)
(* (c) sum_z sum_(s != z) frobenius (P_s A_z P_s)^2 <= 2^(L-1) sum_z sum_(z'  *)
(* != z) tr (A_z A_z').                                                       *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - As in the manuscript, zero projections are allowed, and the sum on the   *)
(*   right of (c) is over the ordered pairs of distinct indices, so each      *)
(*   unordered pair counts twice.                                             *)
(*                                                                            *)
(* - L >= 1 is needed: with no matrices, no family of projections sums to the *)
(*   identity in positive dimension.                                          *)
(*                                                                            *)
(* - The manuscript works on a finite-dimensional Euclidean space; here it is *)
(*   'cV[R]_n with the standard inner product, which is no loss of            *)
(*   generality.                                                              *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition psd_splitting_statement : Prop :=
  forall (R : realType) (n L : nat) (A : 'I_L -> 'M[R]_n),
  (0 < L)%N -> (forall z, psdmx (A z)) ->
  exists P : 'I_L -> 'M[R]_n,
  [/\ forall s, P s \is symmetricmx /\ P s *m P s = P s,
      (forall s t, s != t -> P s *m P t = 0) /\ \sum_(s < L) P s = 1%:M &
      \sum_(z < L) \sum_(s < L | s != z) frobenius (P s *m A z *m P s) ^+ 2 <=
        2 ^+ L.-1 * \sum_(z < L) \sum_(z' < L | z' != z) \tr (A z *m A z')].
