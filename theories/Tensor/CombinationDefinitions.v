From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Matrix.Definitions Tensor.Definitions
  Tensor.GibbsDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Operations on lists of trace atoms. An atom with coefficient c and
   matrices B1, B2, B3 stands for the trilinear form
   (U, V, W) |-> c * trace_pair B1 U * trace_pair B2 V * trace_pair B3 W.
   tensor_weighted_join joins the lists rows i, each scaled by q i, for i
   in I. tensor_swap23_atoms swaps the second and third matrices of every
   atom, and tensor_rotate_atoms moves (B1, B2, B3) to (B3, B1, B2).
   mixed_trace_atoms is the list of the atoms (q i, B1 i, B2 i, B3 i) for i
   in I. MathComp is not imported, so map and flat_map are Stdlib's. *)

Definition tensor_weighted_join (n : nat) (q : nat -> R)
    (rows : nat -> list (trace_atom n)) (I : list nat) : list (trace_atom n) :=
  flat_map (fun i => tensor_scale_atoms (q i) (rows i)) I.

Definition tensor_swap23_atoms (n : nat) (atoms : list (trace_atom n)) :
    list (trace_atom n) :=
  map (fun a => {| atom_coefficient := atom_coefficient a;
    atom_first := atom_first a; atom_second := atom_third a;
    atom_third := atom_second a |}) atoms.

Definition tensor_rotate_atoms (n : nat) (atoms : list (trace_atom n)) :
    list (trace_atom n) :=
  map (fun a => {| atom_coefficient := atom_coefficient a;
    atom_first := atom_third a; atom_second := atom_first a;
    atom_third := atom_second a |}) atoms.

Definition mixed_trace_atoms (n : nat) (q : nat -> R)
    (B1 B2 B3 : nat -> matrix n) (I : list nat) : list (trace_atom n) :=
  map (fun i => {| atom_coefficient := q i;
    atom_first := B1 i; atom_second := B2 i; atom_third := B3 i |}) I.
