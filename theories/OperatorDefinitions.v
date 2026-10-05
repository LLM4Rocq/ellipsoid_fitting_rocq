From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions.
Open Scope R_scope.

(* Port of theories/OperatorDefinitions.v from Coquelicot to MathComp-Analysis.

   Coquelicot's NormedModule R_AbsRing becomes normedModType R, its
   R_NormedModule becomes R^o, and its norm becomes MathComp's norm
   `|x|%R. As in the port of MatrixDefinitions, the tuples nest
   euclidean_product, so the norm of a vector is still the Euclidean norm
   sqrt (x_0 ^ 2 + ... + x_n ^ 2). The comparison with 1 in
   matrix_unit_image is Stdlib's <= and 1, as before.

   Coquelicot's real (Lub_Rbar E) becomes MathComp's sup E, the supremum of
   a set of reals (mathcomp.reals.reals.sup). The two agree on every set E.
   If E is nonempty and bounded above, both are its least upper bound. If E
   is empty, Lub_Rbar E is m_infty; if E is unbounded above, it is p_infty;
   real sends both to 0, and sup E is 0 in both cases (sup_out). So
   matrix_operator_norm has the same value as the original on every
   matrix. OperatorDefinitionsAux states the bridge to Stdlib's is_lub. *)

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

(* The supremum is finite; OperatorBounds proves this before using it. *)
Definition matrix_operator_norm (n : nat) (A : matrix n) : R :=
  sup (matrix_unit_image n A).
