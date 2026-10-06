From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Functions of three matrices written as sums of products of traces, and
   their projective operator norm. A trace_atom n is a coefficient c with
   three matrices A, B and C. Its value at U, V, W is
   c * tr (A U) * tr (B V) * tr (C W), with tr (A U) = trace_pair n A U
   (atom_value), and its cost is |c| times the product of the operator norms
   of A, B and C (atom_cost). A list of atoms represents a function T of
   three matrices (tensor_represents) when the matrices of its atoms are
   symmetric and T U V W is the sum of the values of the atoms whenever U,
   V and W are symmetric. projective_operator_norm T is the infimum of the
   costs of the representations of T.

   Index bounds are written (i <= n)%coq_nat, Stdlib's le, since with
   ssreflect loaded (i <= n)%nat is ssrnat's boolean leq. The arithmetic,
   Rabs, the lists and In are Stdlib's. *)

Definition symmetric_matrix (n : nat) (A : matrix n) : Prop :=
  forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat ->
    matrix_entry n A i j = matrix_entry n A j i.

Record trace_atom (n : nat) : Type := {
  atom_coefficient : R;
  atom_first : matrix n;
  atom_second : matrix n;
  atom_third : matrix n
}.
Arguments atom_coefficient {n} _.
Arguments atom_first {n} _.
Arguments atom_second {n} _.
Arguments atom_third {n} _.

Definition symmetric_atom {n} (a : trace_atom n) : Prop :=
  symmetric_matrix n (atom_first a) /\
  symmetric_matrix n (atom_second a) /\
  symmetric_matrix n (atom_third a).

Definition atom_value {n} (a : trace_atom n) (U V W : matrix n) : R :=
  atom_coefficient a * trace_pair n (atom_first a) U *
    trace_pair n (atom_second a) V * trace_pair n (atom_third a) W.

Definition atom_cost {n} (a : trace_atom n) : R :=
  Rabs (atom_coefficient a) * matrix_operator_norm n (atom_first a) *
    matrix_operator_norm n (atom_second a) * matrix_operator_norm n (atom_third a).

Fixpoint tensor_value {n} (atoms : list (trace_atom n)) (U V W : matrix n) : R :=
  match atoms with
  | [] => 0
  | a :: rest => atom_value a U V W + tensor_value rest U V W
  end.

Fixpoint tensor_cost {n} (atoms : list (trace_atom n)) : R :=
  match atoms with
  | [] => 0
  | a :: rest => atom_cost a + tensor_cost rest
  end.

Definition tensor_represents {n} (T : matrix n -> matrix n -> matrix n -> R)
    (atoms : list (trace_atom n)) : Prop :=
  (forall a, In a atoms -> symmetric_atom a) /\
  (forall U V W, symmetric_matrix n U -> symmetric_matrix n V ->
    symmetric_matrix n W -> T U V W = tensor_value atoms U V W).

Definition tensor_cost_set {n} (T : matrix n -> matrix n -> matrix n -> R)
    (c : R) : Prop :=
  exists atoms, tensor_represents T atoms /\ c = tensor_cost atoms.

(* The infimum is taken in the extended reals \bar R, as ereal_inf of the
   image of the set of costs under EFin, so that it is defined before a
   representation of T is known; it is +oo when T has none.
   TensorDefinitionsAux proves that it is the greatest lower bound of the
   costs (projective_operator_norm_lower_bound,
   projective_operator_norm_greatest), and TensorBounds that it is finite
   when T has a representation (projective_operator_norm_finite). *)
Definition projective_operator_norm {n}
    (T : matrix n -> matrix n -> matrix n -> R) : \bar R :=
  ereal_inf [set c%:E | c in tensor_cost_set T]%classic.
