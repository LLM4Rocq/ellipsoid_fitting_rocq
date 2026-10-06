From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import GibbsDefinitions MatrixDefinitions MatrixGibbsDefinitions
  MatrixThirdDefinitions OperatorDefinitions TensorDefinitions TensorBounds
  TensorNestedDefinitions TensorNestedRepresentation TensorNestedBounds.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* The third derivative of the nested soft minimax as a trilinear form of
   bounded projective norm. The coefficient matrices coeff y s are
   symmetric, with operator norm at most k * r y.
   - matrix_nested_third_trace_representation: the atoms
     nested_third_atoms represent the third derivative
     matrix_nested_third_derivative ... A on symmetric matrices, with cost
     at most 10 k^3 (beta + gamma)^2 times the Gibbs average of r y ^ 3.
   - matrix_nested_third_projective_finite_bound: so the projective
     operator norm of the third derivative, an extended real, is EFin z
     for a real z >= 0 with the same bound. *)

(* The concrete list contains inner centered triples, all three distinct
   covariance placements, and outer centered triples.  Dimension n denotes
   square matrices of positive dimension S n.  The target is the full mixed
   third expression already obtained by differentiating evaluated derivatives;
   this statement does not assert operator-valued C3 regularity. *)
Theorem matrix_nested_third_trace_representation n beta gamma offset coeff Y S
    (A : matrix n) k r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall y, In y Y -> 0 <= r y) ->
  (forall y, In y Y -> forall s, In s S -> symmetric_matrix n (coeff y s)) ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  tensor_represents (matrix_nested_third_derivative n beta gamma offset coeff Y S A)
    (nested_third_atoms n beta gamma offset coeff Y S A) /\
  tensor_cost (nested_third_atoms n beta gamma offset coeff Y S A) <=
    10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y (fun y => r y ^ 3).
Proof.
  intros Hbeta Hgamma HY HS Hk Hr Hsym Hcap; split.
  - apply nested_third_atoms_represents; [exact HS|].
    intros y s Hy Hs; apply Hsym; assumption.
  - apply nested_third_atoms_cost_bound; assumption.
Qed.

Theorem matrix_nested_third_projective_finite_bound n beta gamma offset coeff Y S
    (A : matrix n) k r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall y, In y Y -> 0 <= r y) ->
  (forall y, In y Y -> forall s, In s S -> symmetric_matrix n (coeff y s)) ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  exists z : R,
    projective_operator_norm (matrix_nested_third_derivative n beta gamma offset coeff Y S A) = EFin z /\
    0 <= z /\ z <= 10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y (fun y => r y ^ 3).
Proof.
  intros Hbeta Hgamma HY HS Hk Hr Hsym Hcap.
  destruct (matrix_nested_third_trace_representation n beta gamma offset coeff Y S A k r
    Hbeta Hgamma HY HS Hk Hr Hsym Hcap) as [Hrep Hcost].
  destruct (projective_operator_norm_finite n _ _ Hrep) as [z [HE [Hz Hbound]]].
  exists z; split; [exact HE|]; split; [exact Hz|].
  eapply Rle_trans; [exact Hbound|exact Hcost].
Qed.
