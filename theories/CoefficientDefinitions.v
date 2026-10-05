From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions HessianDefinitions ContinuityDefinitions.
Open Scope R_scope.

(* Port of theories/CoefficientDefinitions.v from Coquelicot to
   MathComp-Analysis.

   Coquelicot's NormedModule R_AbsRing becomes normedModType R, as in the
   ports of MatrixDefinitions, HessianDefinitions and ContinuityDefinitions.
   Coquelicot's plus and scal on such a module become MathComp's + and *:,
   written in ring_scope as (_ + _)%R and (_ *: _)%R. Both are the vector
   space operations of the same module, so the sums below have the same
   values as in the original. On R^o, (x + y)%R is Stdlib's Rplus x y, so
   module_coordinate_sum R^o n f is coordinate_sum n f of MatrixDefinitions,
   as in the original with R_NormedModule.

   hessian_NormedModule n is the port of HessianDefinitions. Its products
   are euclidean_product of MatrixEuclideanProduct and keep Coquelicot's
   product norm, so the norms of third_action n T W and of the other values
   are the Euclidean norms of all their entries, as in the original.

   The definitions keep the names, arguments and text of the original.
   MathComp is imported only for normedModType and its operations; R_scope
   is opened after it, so the arithmetic on R written here is Stdlib's. *)

Fixpoint module_coordinate_sum (V : normedModType R) (n : nat) (f : nat -> V) : V :=
  match n with
  | O => f O
  | S k => (f O + module_coordinate_sum V k (fun i => f (S i)))%R
  end.

Definition coefficient_contract (V : normedModType R) n
    (F : nat -> nat -> V) (W : matrix n) : V :=
  module_coordinate_sum V n (fun i => module_coordinate_sum V n
    (fun j => (matrix_entry n W j i *: F i j)%R)).

Definition third_action n (T : third_array n) (W : matrix n) : hessian_array n :=
  coefficient_contract (hessian_NormedModule n) n (third_entry n T) W.

Definition third_evaluation n (T : third_array n) (U V W : matrix n) : R :=
  hessian_evaluation n (third_action n T W) U V.
