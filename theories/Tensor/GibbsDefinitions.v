From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.CumulantDefinitions Gibbs.WeightedAverageDefinitions Matrix.Definitions
  Matrix.OperatorDefinitions Tensor.Definitions.
Import ListNotations.
Open Scope R_scope.

(* Weighted means of matrices, the third cumulant of trace scores, and
   lists of trace atoms.
   - matrix_weighted_sum n q B I is sum_{i in I} q i B i, and
     matrix_gibbs_mean is this sum with the Gibbs weights.
   - matrix_centered n q B I i is B i minus the weighted sum.
   - weighted_matrix_cumulant n q B I U V W is the third cumulant, under the
     weights q, of the scores tr (B i U), tr (B i V), tr (B i W).
   - diagonal_trace_atoms n q B I has, for each index i, the atom with
     coefficient q i and the three matrices B i, whose value at U, V, W is
     q i tr (B i U) tr (B i V) tr (B i W). centered_trace_atoms does the
     same with the centered matrices, and tensor_scale_atoms multiplies the
     coefficients of a list of atoms by a. *)

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
