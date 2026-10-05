From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions TensorDefinitions.
Open Scope R_scope.

(* Port of theories/SecondChaosDefinitions.v from Coquelicot to
   MathComp-Analysis.

   Coquelicot's R_NormedModule becomes R^o, the normed module view of R, as
   in the ports of MatrixDefinitions and OperatorDefinitions. It appears only
   as the coordinate type given to tuple_build in chaos_basis, so chaos_basis
   n a is still the vector whose coordinate a is 1 and whose other
   coordinates are 0. MathComp is imported for the notation R^o and its
   normed module structure. R_scope is opened last, so the arithmetic,
   including the factor / 2, the products and the literals 1 and 0, is
   Stdlib's, as before. The test Nat.eqb i a is Stdlib's boolean equality on
   nat, as before. The meaning of every definition is unchanged. *)

Definition vector_inner (n : nat) (x y : vector n) : R :=
  coordinate_sum n (fun i => vector_entry n x i * vector_entry n y i).

Definition vector_outer (n : nat) (x y : vector n) : matrix n :=
  matrix_build n (fun i j => vector_entry n x i * vector_entry n y j).

Definition chaos_basis (n a : nat) : vector n :=
  tuple_build R^o n (fun i => if Nat.eqb i a then 1 else 0).

Definition chaos_first (n : nat) (x : vector n) (a : nat) : matrix n :=
  matrix_add n (vector_outer n (chaos_basis n a) x)
    (vector_outer n x (chaos_basis n a)).

Definition chaos_second (n a b : nat) : matrix n :=
  matrix_add n (vector_outer n (chaos_basis n a) (chaos_basis n b))
    (vector_outer n (chaos_basis n b) (chaos_basis n a)).

Definition chaos_contraction (n : nat)
    (T : matrix n -> matrix n -> matrix n -> R) (x : vector n) : R :=
  / 2 * coordinate_sum n (fun a => coordinate_sum n (fun b =>
    T (chaos_first n x a) (chaos_first n x b) (chaos_second n a b))).
