From Stdlib Require Import Reals.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions SecondChaosDefinitions.
Open Scope R_scope.

(* Port of theories/SymmetricDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly: its
   only Coquelicot content came through matrix n, matrix_scale,
   coordinate_sum and trace_pair of MatrixDefinitions, and through
   vector_outer, chaos_basis and chaos_second of SecondChaosDefinitions.
   Their ports keep the same names and arguments; matrix_scale is now
   MathComp's *: on the nested tuples, which is componentwise as Coquelicot's
   scal was. So the import of Coquelicot is dropped and nothing else changes.
   MathComp is not imported here, so the factor / sqrt 2 is Stdlib's inverse
   of Stdlib's square root, the sum + and the literal 0 are Stdlib's, and the
   tests Nat.eqb a b and Nat.ltb a b are Stdlib's boolean comparisons on nat,
   as before. *)

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
