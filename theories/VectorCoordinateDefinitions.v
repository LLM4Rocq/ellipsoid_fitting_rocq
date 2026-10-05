From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/VectorCoordinateDefinitions.v from Coquelicot to
   MathComp-Analysis.

   Coquelicot's R_NormedModule becomes R^o, the normed module view of R, as
   in the ports of MatrixDefinitions and OperatorDefinitions. The lists are
   Stdlib's. With ssreflect loaded, the bare names map, seq and nth would mean
   MathComp's seq.map, the type seq and seq.nth, so the definitions write
   List.map, List.seq and List.nth, which are the functions the original
   used. The meaning is unchanged. *)

Definition vector_to_list (n : nat) (x : vector n) : list R :=
  List.map (vector_entry n x) (List.seq 0 (S n)).

Definition vector_of_list (n : nat) (xs : list R) : vector n :=
  tuple_build R^o n (fun i => List.nth i xs 0).
