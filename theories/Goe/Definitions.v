From Stdlib Require Import Reals List.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import normedtype.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Matrix.SymmetricBasisDefinitions
  Tensor.ThirdArrayContraction.
Import ListNotations.
Open Scope R_scope.

(* The Gaussian orthogonal ensemble as a function of a vector. goe_pairs n
   lists the index pairs of an (S n) x (S n) symmetric matrix, diagonal
   pairs first, and goe_basis n k is the element of the orthonormal basis
   symmetric_basis of Matrix.SymmetricBasisDefinitions given by the k-th pair.
   goe_matrix n z is sqrt (2 / INR (S n)) times the sum of the
   z_k * goe_basis n k, for z : vector (goe_vector_index n). For a standard
   Gaussian z, its diagonal entries have variance 2 / INR (S n) and its
   off-diagonal entries 1 / INR (S n). The list functions are Stdlib's;
   modules that load MathComp's seq must qualify them, as in List.map. *)

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
