From Stdlib Require Import Reals Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates GradientDefinitions MatrixGradient
  CoefficientDefinitions CoefficientMaps.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/OperatorRepresentation.v from Coquelicot to
   MathComp-Analysis.

   Every definition, lemma and theorem of the original keeps its name and its
   arguments, in the same order. No item is added. The statements change form
   in the ways of the ports of MatrixCoordinates, CoefficientMaps and
   OperatorSpaceDefinitions.

   1. Linear maps. Coquelicot's is_linear f is stated, as in
      OperatorSpaceDefinitions and CoefficientMaps, as the conjunction
        linear f /\
        exists M : R, 0 < M /\ forall x, (`|f x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound. This is
      the predicate of bounded_matrix_map in OperatorSpaceDefinitions, so
      operator_decode still packs operator_coefficient_apply n V C with the
      proof operator_coefficient_apply_linear n V C, and the elements of
      bounded_matrix_map n V are the same as in the original.

   2. Coquelicot's NormedModule R_AbsRing becomes normedModType R. Its zero,
      plus and scal become MathComp's 0, + and *:, written 0%R, (_ + _)%R and
      (_ *: _)%R. In module_coordinate_sum_select the scalars 1 and 0 are
      written inside %R, so they are MathComp's ring constants of R. Through
      Rstruct these are Stdlib's R1 and R0, the values of the literals 1 and
      0 of the original, so the statement means the same. A goal written with
      Stdlib's literals, as matrix_basis_entry produces, is closed by the
      lemma by conversion.

   3. Order on indices. With ssreflect loaded, (i <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statements write (i <= n)%coq_nat, which is Stdlib's le.

   4. Axioms. The original proved bounded_matrix_map_ext with Stdlib's
      functional_extensionality and Classical_Prop.proof_irrelevance. The port
      uses funext and Prop_irrelevance of MathComp's boolp instead. They rest
      on boolp.functional_extensionality_dep and
      boolp.propositional_extensionality, two of the seven axioms of the
      README, so the module does not need Classical_Prop.classic. *)

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
