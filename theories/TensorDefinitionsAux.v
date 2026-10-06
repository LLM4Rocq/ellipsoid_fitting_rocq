From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions TensorDefinitions.
Open Scope R_scope.

(* The projective operator norm of TensorDefinitions as a greatest lower
   bound. projective_operator_norm T is the infimum, in the extended reals,
   of the costs of the representations of T (tensor_cost_set T).
   projective_operator_norm_lower_bound: it is at most each such cost.
   projective_operator_norm_greatest: it is at least every lower bound of
   these costs. *)

Lemma projective_operator_norm_lower_bound n
    (T : matrix n -> matrix n -> matrix n -> R) (c : R) :
  tensor_cost_set T c -> (projective_operator_norm T <= c%:E)%E.
Proof. by move=> Hc; apply: ereal_inf_lbound; exists c. Qed.

Lemma projective_operator_norm_greatest n
    (T : matrix n -> matrix n -> matrix n -> R) (l : \bar R) :
  (forall c : R, tensor_cost_set T c -> (l <= c%:E)%E) ->
  (l <= projective_operator_norm T)%E.
Proof. by move=> Hl; apply/ereal_infP => _ [c Hc <-]; exact: Hl. Qed.
