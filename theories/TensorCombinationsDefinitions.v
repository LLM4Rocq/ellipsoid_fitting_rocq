From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions TensorDefinitions TensorGibbsDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/TensorCombinationsDefinitions.v from Coquelicot to
   MathComp-Analysis. The original did not import Coquelicot; its only
   Coquelicot content came through matrix n of MatrixDefinitions, through the
   record trace_atom of TensorDefinitions and through tensor_scale_atoms of
   TensorGibbsDefinitions. Their ports keep the same names, arguments and
   fields, so the text below is the original's. MathComp is not imported
   here, so map and flat_map are Stdlib's List.map and List.flat_map, and
   the lists are Stdlib's, as before. *)

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
