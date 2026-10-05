From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions TensorDefinitions.
Open Scope R_scope.

(* Facts about the port of TensorDefinitions that need proofs, kept out of
   the definitions module.

   The original defined projective_operator_norm T as
   Glb_Rbar (tensor_cost_set T), and its importers used Coquelicot's
   Glb_Rbar_correct, which says that Glb_Rbar E is a lower bound of E in Rbar
   and lies above every other lower bound. The port uses MathComp's
   ereal_inf of the image of the cost set in \bar R. The lemmas below state
   the same two properties for it, in MathComp's order on \bar R. A greatest
   lower bound is unique, so these two properties fix the value, and the
   value is the one of the original.

   A downstream proof that wrote
     apply (proj1 (Glb_Rbar_correct (tensor_cost_set T)))
   or proj2 of it can use proj1 or proj2 of projective_operator_norm_glb. *)

Lemma projective_operator_norm_lower_bound n
    (T : matrix n -> matrix n -> matrix n -> R) (c : R) :
  tensor_cost_set T c -> (projective_operator_norm T <= c%:E)%E.
Proof. by move=> Hc; apply: ereal_inf_lbound; exists c. Qed.

Lemma projective_operator_norm_greatest n
    (T : matrix n -> matrix n -> matrix n -> R) (l : \bar R) :
  (forall c : R, tensor_cost_set T c -> (l <= c%:E)%E) ->
  (l <= projective_operator_norm T)%E.
Proof. by move=> Hl; apply/ereal_infP => _ [c Hc <-]; exact: Hl. Qed.

(* The shape of Coquelicot's is_glb_Rbar (tensor_cost_set T) N. *)
Lemma projective_operator_norm_glb n
    (T : matrix n -> matrix n -> matrix n -> R) :
  (forall c : R, tensor_cost_set T c ->
    (projective_operator_norm T <= c%:E)%E) /\
  (forall l : \bar R, (forall c : R, tensor_cost_set T c -> (l <= c%:E)%E) ->
    (l <= projective_operator_norm T)%E).
Proof.
  split.
  - exact: projective_operator_norm_lower_bound.
  - exact: projective_operator_norm_greatest.
Qed.
