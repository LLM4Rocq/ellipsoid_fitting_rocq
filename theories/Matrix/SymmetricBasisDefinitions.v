From Stdlib Require Import Reals.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Chaos.SecondOrderDefinitions.
Open Scope R_scope.

(* A basis of the symmetric matrices, and the divergence of a map on them.
   symmetric_diagonal_basis n a is E_aa, and
   symmetric_offdiagonal_basis n a b is (E_ab + E_ba) / sqrt 2; together
   they form an orthonormal basis of the symmetric matrices for the
   Frobenius inner product. symmetric_divergence n L is the sum of
   trace_pair n E (L E) over that basis, where trace_pair n B H is the
   trace of B H. *)

Definition symmetric_diagonal_basis n a : matrix n :=
  vector_outer n (chaos_basis n a) (chaos_basis n a).

Definition symmetric_offdiagonal_basis n a b : matrix n :=
  matrix_scale n (/ sqrt 2) (chaos_second n a b).

(* The basis is indexed by a <= b; an off-diagonal element occurs once. *)
Definition symmetric_basis n a b : matrix n :=
  if Nat.eqb a b then symmetric_diagonal_basis n a
  else symmetric_offdiagonal_basis n a b.

Definition symmetric_divergence n (L : matrix n -> matrix n) : R :=
  coordinate_sum n (fun a => trace_pair n (symmetric_diagonal_basis n a)
    (L (symmetric_diagonal_basis n a))) +
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    if Nat.ltb a b then trace_pair n (symmetric_offdiagonal_basis n a b)
      (L (symmetric_offdiagonal_basis n a b)) else 0)).
