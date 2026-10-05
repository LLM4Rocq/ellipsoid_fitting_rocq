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

(* Port of theories/TensorNested.v from Coquelicot to MathComp-Analysis.

   The three theorems keep their names, their arguments in the same order and
   their hypotheses. The first theorem keeps the text of the original: it
   mentions only definitions of the ported modules, Stdlib's arithmetic, pow,
   order, lists and In, whose meaning the ports keep.

   The second and third theorems use Coquelicot's extended reals. As in the
   ports of TensorDefinitions, TensorBounds and TensorGibbs, and in the
   restatement of the challenge ellipsoid_tensor_nested in analysis/challenges,
   Rbar becomes MathComp's \bar R, Finite becomes EFin, and Rbar_le x y
   becomes lee x y, the order of \bar R that the notation (x <= y)%E unfolds
   to. The prefix forms EFin and lee are used, not the notations x%:E and
   (x <= y)%E, so that the bound 10 * k ^ 3 * (beta + gamma) ^ 2 * ... keeps
   Stdlib's arithmetic: inside x%:E the numeral 10 would be read as MathComp's
   natmul 1 10, a different term from Stdlib's IZR 10. The order of \bar R has
   the cases of Rbar_le, and EFin embeds R as Finite did, so the statements
   mean the same as the originals.

   The proofs follow the original. Rbar_le_trans becomes Order's le_trans,
   and the comparison of two finite values, which Rbar_le gave by computation,
   goes through lee_fin and RleP. *)

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

(* Finite z of the original becomes EFin z; see the comment at the top of the
   file. *)
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

(* Rbar_le and Finite of the original become lee and EFin; see the comment at
   the top of the file. *)
Theorem matrix_nested_third_projective_bound n beta gamma offset coeff Y S
    (A : matrix n) k r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= k ->
  (forall y, In y Y -> 0 <= r y) ->
  (forall y, In y Y -> forall s, In s S -> symmetric_matrix n (coeff y s)) ->
  (forall y, In y Y -> forall s, In s S -> matrix_operator_norm n (coeff y s) <= k * r y) ->
  lee (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma offset coeff Y S A))
    (EFin (10 * k ^ 3 * (beta + gamma) ^ 2 *
      gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y (fun y => r y ^ 3))).
Proof.
  intros Hbeta Hgamma HY HS Hk Hr Hsym Hcap.
  destruct (matrix_nested_third_trace_representation n beta gamma offset coeff Y S A k r
    Hbeta Hgamma HY HS Hk Hr Hsym Hcap) as [Hrep Hcost].
  apply: Order.POrderTheory.le_trans.
  - apply: projective_operator_norm_representation_bound; exact Hrep.
  - rewrite lee_fin; apply/RleP; exact Hcost.
Qed.
