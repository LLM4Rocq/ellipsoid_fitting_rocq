From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions ThirdDefinitions MomentDefinitions
  MatrixDefinitions OperatorDefinitions TensorDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/TensorGibbsDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly: its
   only Coquelicot content came through matrix_zero, matrix_add,
   matrix_scale and trace_pair of MatrixDefinitions, and through the record
   trace_atom of TensorDefinitions. Their ports keep the same names,
   arguments and fields; matrix_zero, matrix_add and matrix_scale are now
   MathComp's 0, + and *: on the nested tuples, which are componentwise as
   Coquelicot's zero, plus and scal were. So the import of Coquelicot is
   dropped and nothing else changes. MathComp is not imported here, so map
   is Stdlib's List.map, the lists are Stdlib's, and the arithmetic,
   including the scalar -1 and the product a * _, is Stdlib's, as before. *)

Fixpoint matrix_weighted_sum (n : nat) (q : nat -> R) (B : nat -> matrix n)
    (I : list nat) : matrix n :=
  match I with
  | [] => matrix_zero n
  | i :: rest => matrix_add n (matrix_scale n (q i) (B i)) (matrix_weighted_sum n q B rest)
  end.

Definition matrix_centered (n : nat) (q : nat -> R) (B : nat -> matrix n)
    (I : list nat) (i : nat) : matrix n :=
  matrix_add n (B i) (matrix_scale n (-1) (matrix_weighted_sum n q B I)).

Definition matrix_gibbs_mean (n : nat) (c : R) (f : nat -> R) (I : list nat)
    (B : nat -> matrix n) : matrix n :=
  matrix_weighted_sum n (gibbs_weight c f I) B I.

Definition weighted_matrix_cumulant (n : nat) (q : nat -> R) (B : nat -> matrix n)
    (I : list nat) (U V W : matrix n) : R :=
  weighted_average q I (fun i =>
    (trace_pair n (B i) U - weighted_average q I (fun j => trace_pair n (B j) U)) *
    (trace_pair n (B i) V - weighted_average q I (fun j => trace_pair n (B j) V)) *
    (trace_pair n (B i) W - weighted_average q I (fun j => trace_pair n (B j) W))).

Definition diagonal_trace_atoms (n : nat) (q : nat -> R) (B : nat -> matrix n)
    (I : list nat) : list (trace_atom n) :=
  map (fun i => {| atom_coefficient := q i;
    atom_first := B i; atom_second := B i; atom_third := B i |}) I.

Definition centered_trace_atoms (n : nat) (q : nat -> R) (B : nat -> matrix n)
    (I : list nat) : list (trace_atom n) :=
  diagonal_trace_atoms n q (matrix_centered n q B I) I.

Definition tensor_scale_atom {n} (a : R) (t : trace_atom n) : trace_atom n :=
  {| atom_coefficient := a * atom_coefficient t;
     atom_first := atom_first t; atom_second := atom_second t; atom_third := atom_third t |}.

Definition tensor_scale_atoms {n} (a : R) (atoms : list (trace_atom n)) : list (trace_atom n) :=
  map (tensor_scale_atom a) atoms.
