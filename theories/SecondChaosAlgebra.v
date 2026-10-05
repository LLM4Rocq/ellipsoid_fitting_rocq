From Stdlib Require Import Reals Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorBounds OperatorProperties NormEquivalence
  TensorDefinitions SecondChaosDefinitions.
Open Scope R_scope.

(* Port of theories/SecondChaosAlgebra.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order, and the statements keep their meaning. They change form in one
   way, and the proofs in two.

   1. Order on indices. With ssreflect loaded, (i <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statements write (i <= n)%coq_nat, which is ssrnat's notation for
      Stdlib's le. This is the convention of the ports of MatrixCoordinates,
      OperatorProperties and TensorDefinitions. The statements are the same
      terms as in the original.

   2. The arithmetic is Stdlib's, as before, because R_scope is opened last.
      vector_inner, vector_outer, chaos_basis, chaos_first, chaos_second,
      chaos_contraction, matrix_action, matrix_mul and trace_pair come from
      the ports of SecondChaosDefinitions, OperatorDefinitions and
      MatrixDefinitions, which keep their values.

   3. Proofs. Coquelicot's R_NormedModule becomes R^o in the call to
      tuple_ext. Stdlib's "rewrite A, B" and "rewrite ... by tac" are not
      available once ssreflect is loaded, so the proofs rewrite with lemmas
      applied to their side conditions, or discharge them with //. *)

Lemma vector_inner_sym n (x y : vector n) : vector_inner n x y = vector_inner n y x.
Proof. unfold vector_inner; apply coordinate_sum_ext; intros; ring. Qed.

Lemma chaos_basis_entry n a i : (i <= n)%coq_nat ->
  vector_entry n (chaos_basis n a) i = if Nat.eqb i a then 1 else 0.
Proof.
  intros Hi; unfold vector_entry, chaos_basis.
  exact (tuple_entry_build R^o n i (fun i => if Nat.eqb i a then 1 else 0) Hi).
Qed.

Lemma vector_outer_entry n (x y : vector n) i j :
  (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  matrix_entry n (vector_outer n x y) i j = vector_entry n x i * vector_entry n y j.
Proof. intros; unfold vector_outer; apply matrix_entry_build; assumption. Qed.

Theorem chaos_first_symmetric n (x : vector n) a : symmetric_matrix n (chaos_first n x a).
Proof.
  intros i j Hi Hj; unfold chaos_first; rewrite !matrix_entry_add.
  rewrite (vector_outer_entry n _ _ i j Hi Hj) (vector_outer_entry n _ _ i j Hi Hj).
  rewrite (vector_outer_entry n _ _ j i Hj Hi) (vector_outer_entry n _ _ j i Hj Hi).
  ring.
Qed.

Theorem chaos_second_symmetric n a b : symmetric_matrix n (chaos_second n a b).
Proof.
  intros i j Hi Hj; unfold chaos_second; rewrite !matrix_entry_add.
  rewrite (vector_outer_entry n _ _ i j Hi Hj) (vector_outer_entry n _ _ i j Hi Hj).
  rewrite (vector_outer_entry n _ _ j i Hj Hi) (vector_outer_entry n _ _ j i Hj Hi).
  ring.
Qed.

Lemma vector_inner_basis n (x : vector n) a : (a <= n)%coq_nat ->
  vector_inner n (chaos_basis n a) x = vector_entry n x a.
Proof.
  intros Ha; unfold vector_inner.
  transitivity (coordinate_sum n (fun i => vector_entry n x i * (if Nat.eqb i a then 1 else 0))).
  - apply coordinate_sum_ext; intros i Hi; rewrite (chaos_basis_entry n a i Hi).
    destruct (Nat.eqb i a); ring.
  - exact (operator_coordinate_sum_select n a (vector_entry n x) Ha).
Qed.

Lemma vector_inner_action n (A : matrix n) (x y : vector n) :
  vector_inner n x (matrix_action n A y) =
  coordinate_sum n (fun i => coordinate_sum n
    (fun j => vector_entry n x i * matrix_entry n A i j * vector_entry n y j)).
Proof.
  unfold vector_inner; apply coordinate_sum_ext; intros i Hi.
  rewrite (matrix_action_entry n A y i Hi).
  rewrite -normeq_coordinate_sum_scale.
  apply coordinate_sum_ext; intros; ring.
Qed.

Theorem vector_inner_action_symmetric n (A : matrix n) (x y : vector n) :
  symmetric_matrix n A ->
  vector_inner n x (matrix_action n A y) = vector_inner n (matrix_action n A x) y.
Proof.
  intros HA; rewrite (vector_inner_sym n (matrix_action n A x) y).
  rewrite !vector_inner_action normeq_coordinate_sum_swap.
  apply coordinate_sum_ext; intros i Hi; apply coordinate_sum_ext; intros j Hj.
  rewrite (HA j i Hj Hi); ring.
Qed.

Theorem trace_pair_outer n (A : matrix n) (x y : vector n) :
  trace_pair n A (vector_outer n x y) = vector_inner n y (matrix_action n A x).
Proof.
  unfold trace_pair; rewrite vector_inner_action.
  apply coordinate_sum_ext; intros i Hi; apply coordinate_sum_ext; intros j Hj.
  rewrite (vector_outer_entry n x y j i Hj Hi); ring.
Qed.

Theorem trace_pair_chaos_first n (A : matrix n) (x : vector n) a :
  symmetric_matrix n A -> (a <= n)%coq_nat ->
  trace_pair n A (chaos_first n x a) = 2 * vector_entry n (matrix_action n A x) a.
Proof.
  intros HA Ha; unfold chaos_first; rewrite trace_pair_add !trace_pair_outer.
  rewrite (vector_inner_action_symmetric n A x (chaos_basis n a) HA).
  rewrite (vector_inner_sym n (matrix_action n A x) (chaos_basis n a)).
  rewrite (vector_inner_basis n (matrix_action n A x) a Ha); ring.
Qed.

Theorem trace_pair_chaos_second n (A : matrix n) a b :
  symmetric_matrix n A -> (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  trace_pair n A (chaos_second n a b) = 2 * matrix_entry n A a b.
Proof.
  intros HA Ha Hb.
  change (trace_pair n A (chaos_first n (chaos_basis n b) a) = 2 * matrix_entry n A a b).
  rewrite (trace_pair_chaos_first n A (chaos_basis n b) a HA Ha).
  change (2 * vector_entry n (matrix_action n A (operator_basis_vector n b)) a =
    2 * matrix_entry n A a b).
  rewrite (matrix_action_basis_entry n A a b Ha Hb); reflexivity.
Qed.

Theorem chaos_pure_contraction_inner n (A1 A2 A3 : matrix n) (x : vector n) :
  symmetric_matrix n A1 -> symmetric_matrix n A2 -> symmetric_matrix n A3 ->
  chaos_contraction n (fun H1 H2 H3 =>
    trace_pair n A1 H1 * trace_pair n A2 H2 * trace_pair n A3 H3) x =
  4 * vector_inner n (matrix_action n A1 x) (matrix_action n A3 (matrix_action n A2 x)).
Proof.
  intros H1 H2 H3; unfold chaos_contraction; rewrite vector_inner_action.
  replace (4 * coordinate_sum n (fun i => coordinate_sum n
    (fun j => vector_entry n (matrix_action n A1 x) i * matrix_entry n A3 i j *
      vector_entry n (matrix_action n A2 x) j))) with
    (/ 2 * (8 * coordinate_sum n (fun i => coordinate_sum n
    (fun j => vector_entry n (matrix_action n A1 x) i * matrix_entry n A3 i j *
      vector_entry n (matrix_action n A2 x) j)))) by field.
  f_equal; rewrite -normeq_coordinate_sum_scale.
  apply coordinate_sum_ext; intros a Ha; rewrite -normeq_coordinate_sum_scale.
  apply coordinate_sum_ext; intros b Hb.
  rewrite (trace_pair_chaos_first n A1 x a H1 Ha).
  rewrite (trace_pair_chaos_first n A2 x b H2 Hb).
  rewrite (trace_pair_chaos_second n A3 a b H3 Ha Hb); ring.
Qed.
