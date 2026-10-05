From Stdlib Require Import Reals.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import normedtype.
From EllipsoidFitting Require Import MatrixDefinitions GradientDefinitions CoefficientDefinitions.
Open Scope R_scope.

(* Port of theories/OperatorSpaceDefinitions.v from Coquelicot to
   MathComp-Analysis.

   Coquelicot's NormedModule R_AbsRing becomes normedModType R, as in the
   ports of MatrixDefinitions and CoefficientDefinitions. The nested tuples
   of operator_coefficients n V are those of MatrixDefinitions, so their
   norm is still the Euclidean norm of the n + 1 by n + 1 entries, each
   measured with the norm of V, as in the original.

   One statement changes form: the predicate of bounded_matrix_map.
   Coquelicot's is_linear f is a record with three fields,
     f (plus x y) = plus (f x) (f y),
     f (scal k x) = scal k (f x),
     exists M, 0 < M /\ forall x, norm (f x) <= M * norm x.
   MathComp's linear f is the algebraic part only, stated as
   forall a u v, f (a *: u + v) = a *: f u + f v, which is equivalent to the
   first two fields (take a = 1 for additivity; then f 0 = 0, and v = 0
   gives homogeneity). MathComp has no predicate for the third field, the
   bound that makes f continuous (README, difference 2). The port therefore
   states Coquelicot's is_linear f as the conjunction
     linear f /\
     exists M : R, 0 < M /\ forall x, (`|f x|)%R <= M * (`|x|)%R,
   the form that NormedTransport, MatrixCoordinates and OperatorBounds use.
   The bound uses Stdlib's 0, <, <= and * around MathComp's norms. The norm
   of x : matrix n is the Frobenius norm of MatrixDefinitions and the norm
   of f x is that of V, so the bound means the same as in the original,
   constants included. bounded_matrix_map n V therefore has the same
   elements as in the original: the linear maps from matrix n to V with a
   norm bound, which are the continuous linear maps.

   The other definitions keep the text of the original. The MathComp
   imports are limited to what linear and the norm need, and R_scope is
   opened after them. *)

Definition operator_coefficients (n : nat) (V : normedModType R) : normedModType R :=
  tuple_NormedModule (tuple_NormedModule V n) n.

Definition bounded_matrix_map (n : nat) (V : normedModType R) : Type :=
  { f : matrix n -> V | linear f /\
      exists M : R, 0 < M /\ forall x : matrix n, (`|f x|)%R <= M * (`|x|)%R }.

Definition operator_apply n V (L : bounded_matrix_map n V) (W : matrix n) : V :=
  proj1_sig L W.

Definition operator_encode n V (L : bounded_matrix_map n V) : operator_coefficients n V :=
  tuple_build (tuple_NormedModule V n) n (fun i => tuple_build V n
    (fun j => operator_apply n V L (matrix_basis n j i))).

Definition operator_coefficient n V (C : operator_coefficients n V) (i j : nat) : V :=
  tuple_entry V n j (tuple_entry (tuple_NormedModule V n) n i C).

Definition operator_coefficient_apply n V (C : operator_coefficients n V) : matrix n -> V :=
  coefficient_contract V n (operator_coefficient n V C).
