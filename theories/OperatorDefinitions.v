From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions.
Open Scope R_scope.

(* Vectors, the action of a matrix on a vector, and the operator norm.

   vector n is tuple_NormedModule R^o n of MatrixDefinitions, the tuples of
   S n reals, whose norm `|x|%R is the Euclidean norm
   sqrt (x_0 ^ 2 + ... + x_n ^ 2).
   matrix_action n A x is the vector A x, with coordinates the sums over j
   of matrix_entry n A i j * vector_entry n x j. matrix_unit_image n A is
   the set of the norms of the A x with `|x| <= 1 (Stdlib's <= and 1), and
   matrix_operator_norm n A is its supremum, MathComp's sup
   (mathcomp.reals.reals.sup). For a set of reals that is nonempty and
   bounded above, sup is the least upper bound, in the sense of Stdlib's
   is_lub (operator_sup_is_lub in OperatorDefinitionsAux); for any other
   set it is 0 (sup_out). *)

Definition vector_NormedModule (n : nat) : normedModType R :=
  tuple_NormedModule R^o n.
Definition vector (n : nat) : Type := vector_NormedModule n.
Definition vector_entry (n : nat) (x : vector n) (i : nat) : R :=
  tuple_entry R^o n i x.

Definition matrix_action (n : nat) (A : matrix n) (x : vector n) : vector n :=
  tuple_build R^o n (fun i => coordinate_sum n
    (fun j => matrix_entry n A i j * vector_entry n x j)).

Definition matrix_unit_image (n : nat) (A : matrix n) (r : R) : Prop :=
  exists x : vector n, `|x|%R <= 1 /\ r = `|matrix_action n A x|%R.

(* OperatorBounds proves that matrix_unit_image n A is nonempty and bounded
   above, so that this is its least upper bound (matrix_operator_norm_lub). *)
Definition matrix_operator_norm (n : nat) (A : matrix n) : R :=
  sup (matrix_unit_image n A).
