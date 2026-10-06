From Stdlib Require Import Reals Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Matrix.OperatorDefinitions
  Matrix.OperatorNormProperties Matrix.FrobeniusNorm Tensor.Definitions
  Chaos.SecondOrderDefinitions Chaos.SecondAlgebra
  Matrix.SymmetricBasisDefinitions.
Import Num.Theory.
Open Scope R_scope.

(* The orthonormal basis of the symmetric matrices of Matrix.SymmetricBasisDefinitions.
   For a <= b <= n, symmetric_basis n a b is e_a e_a^T when a = b and
   (e_a e_b^T + e_b e_a^T) / sqrt 2 otherwise, where e_a is
   chaos_basis n a.
   - symmetric_diagonal_trace and symmetric_offdiagonal_trace: the trace
     pairing of a basis matrix with A is the entry (a, a) of A, or
     (A a b + A b a) / sqrt 2.
   - symmetric_basis_symmetric: every basis matrix is symmetric.
   - symmetric_basis_orthonormal and symmetric_basis_normalized: the basis
     is orthonormal for trace_pair; symmetric_basis_unit_norm: each basis
     matrix has Frobenius norm 1.
   - chaos_second_diagonal and chaos_second_swap: chaos_second n a a is
     twice the diagonal basis matrix, and chaos_second is symmetric in a
     and b.
   With ssreflect loaded, the statements write (i <= n)%coq_nat for
   Stdlib's order on nat. The arithmetic, the square root, the literals and
   the tests Nat.eqb and Nat.ltb are Stdlib's, since R_scope is opened
   last. *)

Lemma symmetric_trace_pair_comm n (A B : matrix n) : trace_pair n A B = trace_pair n B A.
Proof.
  unfold trace_pair; rewrite normeq_coordinate_sum_swap.
  apply coordinate_sum_ext; intros i Hi; apply coordinate_sum_ext; intros j Hj; ring.
Qed.

Lemma symmetric_trace_unit n a b (A : matrix n) :
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  trace_pair n (vector_outer n (chaos_basis n a) (chaos_basis n b)) A =
    matrix_entry n A b a.
Proof.
  intros Ha Hb.
  rewrite symmetric_trace_pair_comm trace_pair_outer (vector_inner_basis _ _ b Hb).
  change (vector_entry n (matrix_action n A (operator_basis_vector n a)) b = matrix_entry n A b a).
  apply matrix_action_basis_entry; assumption.
Qed.

Theorem symmetric_diagonal_trace n a (A : matrix n) :
  (a <= n)%coq_nat -> trace_pair n (symmetric_diagonal_basis n a) A = matrix_entry n A a a.
Proof. intros; apply symmetric_trace_unit; assumption. Qed.

Theorem symmetric_offdiagonal_trace n a b (A : matrix n) :
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  trace_pair n (symmetric_offdiagonal_basis n a b) A =
    / sqrt 2 * (matrix_entry n A a b + matrix_entry n A b a).
Proof.
  intros Ha Hb; unfold symmetric_offdiagonal_basis.
  rewrite symmetric_trace_pair_comm trace_pair_scale.
  unfold chaos_second; rewrite trace_pair_add.
  rewrite (symmetric_trace_pair_comm n A) (symmetric_trace_pair_comm n A).
  rewrite (symmetric_trace_unit n a b A Ha Hb) (symmetric_trace_unit n b a A Hb Ha).
  ring.
Qed.

Lemma symmetric_diagonal_entry n a i j : (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  matrix_entry n (symmetric_diagonal_basis n a) i j =
    (if Nat.eqb i a then 1 else 0) * (if Nat.eqb j a then 1 else 0).
Proof.
  intros Hi Hj; unfold symmetric_diagonal_basis.
  rewrite (vector_outer_entry n _ _ i j Hi Hj).
  rewrite (chaos_basis_entry n a i Hi) (chaos_basis_entry n a j Hj); reflexivity.
Qed.

Lemma symmetric_offdiagonal_entry n a b i j : (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  matrix_entry n (symmetric_offdiagonal_basis n a b) i j = / sqrt 2 *
    ((if Nat.eqb i a then 1 else 0) * (if Nat.eqb j b then 1 else 0) +
     (if Nat.eqb i b then 1 else 0) * (if Nat.eqb j a then 1 else 0)).
Proof.
  intros Hi Hj; unfold symmetric_offdiagonal_basis, chaos_second.
  rewrite matrix_entry_scale matrix_entry_add.
  rewrite (vector_outer_entry n _ _ i j Hi Hj) (vector_outer_entry n _ _ i j Hi Hj).
  rewrite (chaos_basis_entry n a i Hi) (chaos_basis_entry n b j Hj).
  rewrite (chaos_basis_entry n b i Hi) (chaos_basis_entry n a j Hj); reflexivity.
Qed.

Theorem symmetric_basis_symmetric n a b : symmetric_matrix n (symmetric_basis n a b).
Proof.
  unfold symmetric_basis; destruct (Nat.eqb a b).
  - intros i j Hi Hj.
    rewrite (symmetric_diagonal_entry n a i j Hi Hj) (symmetric_diagonal_entry n a j i Hj Hi).
    ring.
  - intros i j Hi Hj.
    rewrite (symmetric_offdiagonal_entry n a b i j Hi Hj).
    rewrite (symmetric_offdiagonal_entry n a b j i Hj Hi).
    ring.
Qed.

Lemma symmetric_inv_sqrt2_square : / sqrt 2 * / sqrt 2 = / 2.
Proof.
  pose proof (sqrt_def 2 ltac:(lra)) as H.
  assert (H0 : sqrt 2 <> 0) by nra.
  apply (Rmult_eq_reg_r (sqrt 2 * sqrt 2)); [field_simplify; nra|nra].
Qed.

Theorem symmetric_basis_orthonormal n a b c d :
  (a <= b)%coq_nat -> (b <= n)%coq_nat -> (c <= d)%coq_nat -> (d <= n)%coq_nat ->
  trace_pair n (symmetric_basis n a b) (symmetric_basis n c d) =
    if andb (Nat.eqb a c) (Nat.eqb b d) then 1 else 0.
Proof.
  intros Hab Hb Hcd Hd.
  pose proof symmetric_inv_sqrt2_square as Hsqrt.
  assert (Ha : (a <= n)%coq_nat) by lia.
  assert (Hc : (c <= n)%coq_nat) by lia.
  unfold symmetric_basis.
  destruct (Nat.eqb a b) eqn:Habeq; destruct (Nat.eqb c d) eqn:Hcdeq.
  - apply Nat.eqb_eq in Habeq; apply Nat.eqb_eq in Hcdeq; subst b d.
    rewrite (symmetric_diagonal_trace n a _ Ha) (symmetric_diagonal_entry n c a a Ha Ha).
    destruct (Nat.eqb a c); simpl; ring.
  - apply Nat.eqb_eq in Habeq; apply Nat.eqb_neq in Hcdeq; subst b.
    rewrite (symmetric_diagonal_trace n a _ Ha) (symmetric_offdiagonal_entry n c d a a Ha Ha).
    destruct (Nat.eqb a c) eqn:Hac; destruct (Nat.eqb a d) eqn:Had; simpl;
      try (apply Nat.eqb_eq in Hac; apply Nat.eqb_eq in Had; lia); ring.
  - apply Nat.eqb_neq in Habeq; apply Nat.eqb_eq in Hcdeq; subst d.
    rewrite (symmetric_offdiagonal_trace n a b _ Ha Hb).
    rewrite (symmetric_diagonal_entry n c a b Ha Hb) (symmetric_diagonal_entry n c b a Hb Ha).
    destruct (Nat.eqb a c) eqn:Hac; destruct (Nat.eqb b c) eqn:Hbc; simpl;
      try (apply Nat.eqb_eq in Hac; apply Nat.eqb_eq in Hbc; lia); ring.
  - apply Nat.eqb_neq in Habeq; apply Nat.eqb_neq in Hcdeq.
    rewrite (symmetric_offdiagonal_trace n a b _ Ha Hb).
    rewrite (symmetric_offdiagonal_entry n c d a b Ha Hb).
    rewrite (symmetric_offdiagonal_entry n c d b a Hb Ha).
    destruct (Nat.eqb a c) eqn:Hac; destruct (Nat.eqb a d) eqn:Had;
      destruct (Nat.eqb b c) eqn:Hbc; destruct (Nat.eqb b d) eqn:Hbd; simpl;
      try (apply Nat.eqb_eq in Hac); try (apply Nat.eqb_eq in Had);
      try (apply Nat.eqb_eq in Hbc); try (apply Nat.eqb_eq in Hbd);
      try lia; nra.
Qed.

Theorem symmetric_basis_normalized n a b : (a <= b)%coq_nat -> (b <= n)%coq_nat ->
  trace_pair n (symmetric_basis n a b) (symmetric_basis n a b) = 1.
Proof.
  intros Hab Hb; rewrite (symmetric_basis_orthonormal n a b a b Hab Hb Hab Hb).
  rewrite !Nat.eqb_refl; reflexivity.
Qed.

Theorem chaos_second_diagonal n a :
  chaos_second n a a = matrix_scale n 2 (symmetric_diagonal_basis n a).
Proof.
  apply matrix_ext; intros i j Hi Hj; unfold chaos_second, symmetric_diagonal_basis.
  rewrite matrix_entry_add matrix_entry_scale; ring.
Qed.

Theorem chaos_second_swap n a b : chaos_second n a b = chaos_second n b a.
Proof.
  apply matrix_ext; intros i j Hi Hj; unfold chaos_second; rewrite !matrix_entry_add; ring.
Qed.

Theorem symmetric_basis_unit_norm n a b : (a <= b)%coq_nat -> (b <= n)%coq_nat ->
  (`|symmetric_basis n a b|)%R = 1.
Proof.
  intros Hab Hb.
  assert (HE : trace_pair n (symmetric_basis n a b) (symmetric_basis n a b) =
    (`|symmetric_basis n a b|)%R ^ 2).
  { rewrite matrix_frobenius_norm_squared; unfold trace_pair.
    apply coordinate_sum_ext; intros i Hi; apply coordinate_sum_ext; intros j Hj.
    rewrite (symmetric_basis_symmetric n a b j i Hj Hi); ring. }
  rewrite (symmetric_basis_normalized n a b Hab Hb) in HE.
  assert (H0 : 0 <= (`|symmetric_basis n a b|)%R) by (apply/RleP; apply normr_ge0).
  nra.
Qed.
