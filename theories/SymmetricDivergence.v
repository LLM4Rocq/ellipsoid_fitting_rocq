From Stdlib Require Import Reals Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorProperties NormEquivalence TensorDefinitions
  SecondChaosDefinitions SecondChaosAlgebra SymmetricDefinitions SymmetricBasis.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* The symmetric divergence through the second-chaos matrices. For a linear
   map L on matrices, the sum over all a, b of the (a, b) entry of
   L (chaos_second n a b) is twice symmetric_divergence n L
   (symmetric_divergence_identity). The proof splits the double sum into
   its diagonal and its pairs a < b (symmetric_ordered_sum_partition), and
   compares each part with the orthonormal basis of symmetric matrices
   (symmetric_linear_diagonal, symmetric_linear_offdiagonal).

   Linearity is stated as MathComp's linear together with a norm bound for
   the Frobenius norm; the proofs use only the linear part. The index
   bounds are written (a <= n)%coq_nat, Stdlib's le, because %nat would
   give ssrnat's boolean leq; R_scope is opened last, so the arithmetic is
   Stdlib's. *)

Lemma symmetric_double_sum_add n f g :
  coordinate_sum n (fun a => coordinate_sum n (fun b => f a b + g a b)) =
  coordinate_sum n (fun a => coordinate_sum n (f a)) +
  coordinate_sum n (fun a => coordinate_sum n (g a)).
Proof.
  transitivity (coordinate_sum n (fun a => coordinate_sum n (f a) + coordinate_sum n (g a))).
  - apply coordinate_sum_ext; intros; apply normeq_coordinate_sum_add.
  - apply normeq_coordinate_sum_add.
Qed.

Lemma symmetric_sum_diagonal n f :
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    if Nat.eqb a b then f a b else 0)) = coordinate_sum n (fun a => f a a).
Proof.
  apply coordinate_sum_ext; intros a Ha.
  transitivity (coordinate_sum n (fun b => f a b * (if Nat.eqb b a then 1 else 0))).
  - apply coordinate_sum_ext; intros b Hb; rewrite Nat.eqb_sym; destruct (Nat.eqb b a); ring.
  - apply operator_coordinate_sum_select; exact Ha.
Qed.

Theorem symmetric_ordered_sum_partition n f :
  coordinate_sum n (fun a => coordinate_sum n (f a)) =
  coordinate_sum n (fun a => f a a) +
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    if Nat.ltb a b then f a b + f b a else 0)).
Proof.
  transitivity (coordinate_sum n (fun a => coordinate_sum n (fun b =>
    (if Nat.eqb a b then f a b else 0) +
    ((if Nat.ltb a b then f a b else 0) + (if Nat.ltb b a then f a b else 0))))).
  - apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hb.
    destruct (Nat.eqb a b) eqn:Heq;
      destruct (Nat.ltb a b) eqn:Hab; destruct (Nat.ltb b a) eqn:Hba;
      repeat match goal with
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
      | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
      | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
      end; try lia; ring.
  - rewrite symmetric_double_sum_add symmetric_sum_diagonal; f_equal.
    rewrite symmetric_double_sum_add.
    rewrite (normeq_coordinate_sum_swap n n (fun a b => if Nat.ltb b a then f a b else 0)).
    rewrite <- symmetric_double_sum_add.
    apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hb.
    destruct (Nat.ltb a b); ring.
Qed.

Lemma symmetric_linear_diagonal n (L : matrix n -> matrix n) a :
  (linear L /\
    exists M : R, 0 < M /\ forall x : matrix n, (`|L x|)%R <= M * (`|x|)%R) ->
  (a <= n)%coq_nat ->
  matrix_entry n (L (chaos_second n a a)) a a =
    2 * trace_pair n (symmetric_diagonal_basis n a) (L (symmetric_diagonal_basis n a)).
Proof.
  intros [HL _] Ha.
  rewrite (chaos_second_diagonal n a) (symmetric_diagonal_trace n a _ Ha).
  (* L commutes with scaling: pack it as a {linear _ -> _} and use
     linearZ_LR. *)
  pose L' : {linear matrix_NormedModule n -> matrix_NormedModule n} :=
    HB.pack L (GRing.isLinear.Build R _ _ *:%R L HL).
  have HZ : forall c (X : matrix n), L (matrix_scale n c X) = matrix_scale n c (L X).
  { intros c X; exact (linearZ_LR L' c X). }
  rewrite HZ; apply matrix_entry_scale.
Qed.

Lemma symmetric_linear_offdiagonal n (L : matrix n -> matrix n) a b :
  (linear L /\
    exists M : R, 0 < M /\ forall x : matrix n, (`|L x|)%R <= M * (`|x|)%R) ->
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  matrix_entry n (L (chaos_second n a b)) a b +
  matrix_entry n (L (chaos_second n b a)) b a =
    2 * trace_pair n (symmetric_offdiagonal_basis n a b)
      (L (symmetric_offdiagonal_basis n a b)).
Proof.
  intros [HL _] Ha Hb.
  rewrite (chaos_second_swap n b a) (symmetric_offdiagonal_trace n a b _ Ha Hb).
  unfold symmetric_offdiagonal_basis.
  (* L commutes with scaling, as above. *)
  pose L' : {linear matrix_NormedModule n -> matrix_NormedModule n} :=
    HB.pack L (GRing.isLinear.Build R _ _ *:%R L HL).
  have HZ : forall c (X : matrix n), L (matrix_scale n c X) = matrix_scale n c (L X).
  { intros c X; exact (linearZ_LR L' c X). }
  rewrite HZ.
  transitivity (2 * (/ sqrt 2 *
    (/ sqrt 2 * matrix_entry n (L (chaos_second n a b)) a b +
     / sqrt 2 * matrix_entry n (L (chaos_second n a b)) b a))).
  - replace (2 * (/ sqrt 2 *
      (/ sqrt 2 * matrix_entry n (L (chaos_second n a b)) a b +
       / sqrt 2 * matrix_entry n (L (chaos_second n a b)) b a))) with
      (2 * (/ sqrt 2 * / sqrt 2) *
        (matrix_entry n (L (chaos_second n a b)) a b +
         matrix_entry n (L (chaos_second n a b)) b a)) by ring.
    rewrite symmetric_inv_sqrt2_square; field.
  - f_equal; f_equal; apply f_equal2; symmetry; apply matrix_entry_scale.
Qed.

(* L may have nonsymmetric outputs: both ordered off-diagonal entries occur. *)
Theorem symmetric_divergence_identity n (L : matrix n -> matrix n) :
  (linear L /\
    exists M : R, 0 < M /\ forall x : matrix n, (`|L x|)%R <= M * (`|x|)%R) ->
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    matrix_entry n (L (chaos_second n a b)) a b)) =
    2 * symmetric_divergence n L.
Proof.
  intros HL; rewrite symmetric_ordered_sum_partition.
  unfold symmetric_divergence; rewrite Rmult_plus_distr_l.
  f_equal.
  - rewrite <- normeq_coordinate_sum_scale; apply coordinate_sum_ext; intros a Ha.
    apply symmetric_linear_diagonal; assumption.
  - rewrite <- normeq_coordinate_sum_scale; apply coordinate_sum_ext; intros a Ha.
    rewrite <- normeq_coordinate_sum_scale; apply coordinate_sum_ext; intros b Hb.
    destruct (Nat.ltb a b); [apply symmetric_linear_offdiagonal; assumption|ring].
Qed.
