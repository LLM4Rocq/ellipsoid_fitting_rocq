From Stdlib Require Import Reals Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Gibbs.NestedGradientDefinitions
  Gibbs.MatrixNestedGradient Tensor.ThirdArrayContraction
  Matrix.CoefficientMaps.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Two facts about the finite sums module_coordinate_sum of
   Tensor.ThirdArrayContraction in a real normed space V. A sum of zeros is zero
   (module_coordinate_sum_zero), and the sum of the f i weighted by the
   indicator of i = j is f j when j <= n (module_coordinate_sum_select).
   The operations and the scalars 1 and 0 are MathComp's, written inside
   %R; at Stdlib's R the scalars are Stdlib's R1 and R0. Index bounds are
   written (j <= n)%coq_nat, Stdlib's order le. *)

Lemma module_coordinate_sum_zero (V : normedModType R) n :
  module_coordinate_sum V n (fun _ => 0%R) = 0%R.
Proof. induction n; simpl; [reflexivity|by rewrite IHn addr0]. Qed.

Lemma module_coordinate_sum_select (V : normedModType R) n j (f : nat -> V) :
  (j <= n)%coq_nat ->
  module_coordinate_sum V n (fun i => ((if Nat.eqb i j then 1 else 0) *: f i)%R) = f j.
Proof.
  revert j f; induction n as [|n IH]; intros [|j] f Hj; simpl in *.
  - by rewrite scale1r.
  - lia.
  - rewrite scale1r.
    transitivity (f O + module_coordinate_sum V n (fun _ => 0%R))%R.
    + f_equal; apply module_coordinate_sum_ext; intros i Hi; by rewrite scale0r.
    + by rewrite module_coordinate_sum_zero addr0.
  - rewrite scale0r add0r; apply (IH j (fun i => f (S i))); lia.
Qed.
