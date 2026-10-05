From Stdlib Require Import Reals List.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import normedtype.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions
  SymmetricDefinitions CoefficientDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GoeDefinitions.v from Coquelicot to MathComp-Analysis.

   The only Coquelicot notion written here is scal, the scaling of the
   normed module matrix_NormedModule n in goe_matrix. It becomes MathComp's
   scaling, written (_ *: _)%R, as in the ports of MatrixDefinitions and
   CoefficientDefinitions. On the nested tuples of MatrixDefinitions it is
   componentwise, as Coquelicot's scal was, so goe_matrix has the same value
   as in the original. Everything else keeps the text of the original:
   matrix_scale, module_coordinate_sum, symmetric_basis, vector and
   vector_entry keep their names and arguments in their ports, and the
   vectors and matrices still carry the Euclidean and Frobenius norms.

   The MathComp imports are limited to ssralg, ssrnum, Rstruct and
   normedtype, which are what (_ *: _)%R on matrix n needs. None of them
   imports MathComp's seq, ssrbool or ssrnat into this file, so map, seq,
   flat_map, ++, length, pred and nth below are Stdlib's list functions and
   Nat.pred, with Stdlib's argument order nth k l default, as in the
   original. An importer that loads all_ssreflect_compat sees MathComp's
   map, nth, ++ (cat), pred and seq under these names instead, and has to
   write List.map, List.nth, (_ ++ _)%list, Nat.pred and List.seq to mean
   the functions used here. R_scope is opened after the imports, so sqrt,
   /, 2 and INR in goe_scale are Stdlib's. *)

Definition goe_pairs (n : nat) : list (nat * nat) :=
  map (fun a => (a, a)) (seq 0 (S n)) ++
  flat_map (fun a => map (fun b => (a, b)) (seq (S a) (n - a))) (seq 0 (S n)).

Definition goe_vector_index (n : nat) : nat := pred (length (goe_pairs n)).

Definition goe_basis (n k : nat) : matrix n :=
  let ab := nth k (goe_pairs n) (0%nat, 0%nat) in
  symmetric_basis n (fst ab) (snd ab).

Definition goe_scale (n : nat) : R := sqrt (2 / INR (S n)).

Definition goe_matrix (n : nat) (z : vector (goe_vector_index n)) : matrix n :=
  matrix_scale n (goe_scale n)
    (module_coordinate_sum (matrix_NormedModule n) (goe_vector_index n)
      (fun k => (vector_entry (goe_vector_index n) z k *: goe_basis n k)%R)).
