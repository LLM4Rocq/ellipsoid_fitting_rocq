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

(* Port of theories/TensorDefinitions.v from Coquelicot to MathComp-Analysis.

   Everything except the last definition keeps the text of the original, with
   two changes of notation.

   1. Order on indices. With ssreflect loaded, (i <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so
      symmetric_matrix writes (i <= n)%coq_nat, which is ssrnat's notation
      for Stdlib's le. This is the convention of the port of
      MatrixCoordinates. The meaning is unchanged.

   2. The arithmetic, Rabs, the lists and In are Stdlib's, as before.
      matrix_operator_norm, matrix_entry and trace_pair come from the ports of
      OperatorDefinitions and MatrixDefinitions, which keep their values.

   The last definition changes vocabulary. Coquelicot's extended reals Rbar
   become MathComp's \bar R, and Coquelicot's Glb_Rbar E, the greatest lower
   bound in Rbar of a set E of reals, becomes MathComp's
   ereal_inf [set c%:E | c in E], the infimum in \bar R of the image of E
   under the embedding EFin. Both are the greatest lower bound of E in the
   complete lattice of extended reals: +oo when E is empty, -oo when E is not
   bounded below, and the infimum of E otherwise. So projective_operator_norm
   has the same value as the original on every T. TensorDefinitionsAux proves
   the two properties of Coquelicot's Glb_Rbar_correct for it.

   Downstream, Coquelicot's names translate as follows:
   Finite r becomes r%:E, p_infty and m_infty become +oo and -oo,
   Rbar_le x y becomes (x <= y)%E, and real x becomes fine x. Both real and
   fine send the two infinite values to 0. *)

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

(* The extended value is useful even before representability has been proved.
   TensorBounds proves finiteness for every explicitly represented tensor. *)
Definition projective_operator_norm {n}
    (T : matrix n -> matrix n -> matrix n -> R) : \bar R :=
  ereal_inf [set c%:E | c in tensor_cost_set T]%classic.
