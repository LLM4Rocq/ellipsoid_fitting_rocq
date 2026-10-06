From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Conversions between x : vector n and the list of its S n coordinates.
   vector_to_list lists the coordinates 0, ..., n, and vector_of_list
   builds a vector from the first S n entries of a list, a missing entry
   reading 0. The coordinates have the type R^o, the normed module view of
   R. With ssreflect loaded, the bare names map, seq and nth would mean
   MathComp's functions on seq, so the definitions write List.map, List.seq
   and List.nth, Stdlib's functions on lists. *)

Definition vector_to_list (n : nat) (x : vector n) : list R :=
  List.map (vector_entry n x) (List.seq 0 (S n)).

Definition vector_of_list (n : nat) (xs : list R) : vector n :=
  tuple_build R^o n (fun i => List.nth i xs 0).
