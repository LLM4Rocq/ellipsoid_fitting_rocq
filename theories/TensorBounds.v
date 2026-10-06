From Stdlib Require Import Reals List Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions OperatorBounds TensorDefinitions.
From EllipsoidFitting Require Import TensorDefinitionsAux.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Basic bounds on the projective operator norm of TensorDefinitions. For
   a form T of three matrices, it is the infimum in \bar R of the costs of
   the representations of T, on symmetric matrices, as sums of trace atoms.
   - atom_cost_nonnegative and tensor_cost_nonnegative: costs are
     nonnegative.
   - projective_operator_norm_nonnegative and
     projective_operator_norm_representation_bound: the norm is at least 0
     and at most the cost of every representation. So the norm of a
     represented form is a real r with 0 <= r <= tensor_cost atoms
     (projective_operator_norm_finite).
   - tensor_value_append, tensor_cost_append and tensor_represents_add: the
     values and the costs of concatenated lists of atoms add up, and the
     concatenation of two representations represents the sum of the forms.
   The proofs use projective_operator_norm_lower_bound and
   projective_operator_norm_greatest of TensorDefinitionsAux. With
   ssreflect loaded, a ++ b would mean MathComp's cat, so the statements
   write (a ++ b)%list for Stdlib's app. *)

Lemma atom_cost_nonnegative n (a : trace_atom n) : 0 <= atom_cost a.
Proof.
  unfold atom_cost; repeat apply Rmult_le_pos;
    try apply Rabs_pos; apply matrix_operator_norm_nonnegative.
Qed.

Lemma tensor_cost_nonnegative n (atoms : list (trace_atom n)) :
  0 <= tensor_cost atoms.
Proof.
  induction atoms as [|a rest IH]; simpl; [lra|].
  pose proof (atom_cost_nonnegative n a); lra.
Qed.

Theorem projective_operator_norm_nonnegative n
    (T : matrix n -> matrix n -> matrix n -> R) :
  (0%:E <= projective_operator_norm T)%E.
Proof.
  apply projective_operator_norm_greatest.
  intros c [atoms [HR ->]]; rewrite lee_fin.
  apply/RleP; apply tensor_cost_nonnegative.
Qed.

Theorem projective_operator_norm_representation_bound n
    (T : matrix n -> matrix n -> matrix n -> R) atoms :
  tensor_represents T atoms ->
  (projective_operator_norm T <= (tensor_cost atoms)%:E)%E.
Proof.
  intros HR; apply projective_operator_norm_lower_bound.
  exists atoms; split; [exact HR | reflexivity].
Qed.

Theorem projective_operator_norm_finite n
    (T : matrix n -> matrix n -> matrix n -> R) atoms :
  tensor_represents T atoms ->
  exists r : R, projective_operator_norm T = r%:E /\
    0 <= r /\ r <= tensor_cost atoms.
Proof.
  intros HR.
  have Hlow := projective_operator_norm_nonnegative n T.
  have Hhigh := projective_operator_norm_representation_bound n T atoms HR.
  move: Hlow Hhigh; case: (projective_operator_norm T) => [r| |] Hlow Hhigh.
  - exists r; split; [reflexivity|].
    rewrite lee_fin in Hlow; rewrite lee_fin in Hhigh.
    split; apply/RleP; assumption.
  - by rewrite leye_eq in Hhigh.
  - by rewrite leeNy_eq in Hlow.
Qed.

Lemma tensor_value_append n (left right : list (trace_atom n)) U V W :
  tensor_value (left ++ right)%list U V W =
    tensor_value left U V W + tensor_value right U V W.
Proof. induction left; simpl; [ring | rewrite IHleft; ring]. Qed.

Lemma tensor_cost_append n (left right : list (trace_atom n)) :
  tensor_cost (left ++ right)%list = tensor_cost left + tensor_cost right.
Proof. induction left; simpl; [ring | rewrite IHleft; ring]. Qed.

Lemma tensor_represents_add n (T S : matrix n -> matrix n -> matrix n -> R) left right :
  tensor_represents T left -> tensor_represents S right ->
  tensor_represents (fun U V W => T U V W + S U V W) (left ++ right)%list.
Proof.
  intros [HL HT] [HR HS]; split.
  - intros a Ha; apply in_app_or in Ha; destruct Ha; [apply HL | apply HR]; assumption.
  - intros U V W HU HV HW; simpl.
    rewrite tensor_value_append (HT U V W HU HV HW) (HS U V W HU HV HW).
    reflexivity.
Qed.
