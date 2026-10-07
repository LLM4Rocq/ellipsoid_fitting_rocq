From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # Product laws by blocks                                                   *)
(*                                                                            *)
(* A tuple of n * d coordinates read as n rows of d coordinates, row i being  *)
(* made of the coordinates i * d + j for j < d, as the samples of the         *)
(* ellipsoid fitting papers are read.                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*   row_index i j == the index i * d + j of 'I_(n * d), for i : 'I_n and     *)
(*                    j : 'I_d                                                *)
(* tuple_rows n d x == the n rows of length d of the (n * d)-tuple x          *)
(* ```                                                                        *)
(*                                                                            *)
(* Planned results (phase 5, stage 1); names come with the proofs:            *)
(* - coordinatewise maps preserve independence: for measurable f_i : T -> T', *)
(*   the image of tuple_prod mu n under x |-> [tuple f_i (x_i) | i < n] is    *)
(*   tuple_prod of the images of the mu i under the f_i, so the integral of a *)
(*   bounded measurable, a nonnegative measurable or an integrable G against  *)
(*   the image is the integral of x |-> G [tuple f_i (x_i) | i < n] against   *)
(*   tuple_prod mu n;                                                         *)
(* - rows: the image of tuple_prod mu (n * d) under tuple_rows n d is the     *)
(*   product over i < n of the laws tuple_prod (fun j => mu (i * d + j)) d of *)
(*   the rows, and tuple_rows is a measurable bijection;                      *)
(* - blocks: the image of tuple_prod mu (n + m) under the split into the      *)
(*   first n and the last m coordinates is the product of tuple_prod mu n and *)
(*   tuple_prod (fun i => mu (n + i)) m, so a block of coordinates has the    *)
(*   product law of its coordinates and disjoint blocks are independent.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section tuple_rows.
Context (T : Type) (n d : nat).

Lemma row_index_subproof (i : 'I_n) (j : 'I_d) : (i * d + j < n * d)%N.
Proof.
rewrite (@leq_trans (i * d + d)) ?ltn_add2l // -mulSnr.
by rewrite leq_mul2r ltn_ord orbT.
Qed.

Definition row_index (i : 'I_n) (j : 'I_d) : 'I_(n * d) :=
  Ordinal (row_index_subproof i j).

Definition tuple_rows (x : (n * d).-tuple T) : n.-tuple (d.-tuple T) :=
  [tuple [tuple tnth x (row_index i j) | j < d] | i < n].

End tuple_rows.
