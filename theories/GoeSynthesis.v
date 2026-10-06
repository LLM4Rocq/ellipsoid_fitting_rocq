From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorProperties TensorDefinitions
  SecondChaosDefinitions SecondChaosAlgebra SymmetricDefinitions
  SymmetricBasis GradientDefinitions MatrixGradient CoefficientDefinitions
  CoefficientMaps CoefficientBounds GoeDefinitions GoePairs.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* The GOE matrix of a vector z, goe_matrix n z, is goe_scale n times the
   sum of z_k * goe_basis n k, where goe_scale n = sqrt (2 / (n + 1)) and
   goe_basis n k runs over the basis of symmetric matrices indexed by the
   pairs a <= b.
   - goe_basis_symmetric, goe_basis_unit_norm, goe_basis_orthonormal: the
     basis matrices are symmetric and orthonormal for trace_pair.
   - goe_matrix_symmetric, goe_matrix_linear, goe_matrix_norm_bound:
     goe_matrix n z is symmetric, linear in z, and of Frobenius norm at
     most goe_scale n * (goe_vector_index n + 1) * |z|.
   - goe_matrix_coordinate_direction: the k-th coordinate vector goes to
     goe_scale n * goe_basis n k.
   - goe_matrix_trace: trace_pair (goe_matrix n z) U is goe_scale n times
     the sum of z_k * trace_pair (goe_basis n k) U.
   - goe_basis_divergence: the sum over the basis of trace_pair E (L E) is
     symmetric_divergence n L.
   Linearity in goe_matrix_linear is MathComp's linear together with a norm
   bound. The index bounds are written (k <= _)%coq_nat, Stdlib's le,
   because %nat would give ssrnat's boolean leq. *)

Lemma goe_scale_positive n : 0 < goe_scale n.
Proof.
  unfold goe_scale; apply sqrt_lt_R0; apply Rdiv_lt_0_compat; [lra|].
  apply lt_0_INR; lia.
Qed.

Lemma goe_scale_square n : goe_scale n * goe_scale n = 2 / INR (S n).
Proof.
  unfold goe_scale; apply sqrt_def; apply Rlt_le, Rdiv_lt_0_compat; [lra|].
  apply lt_0_INR; lia.
Qed.

Lemma goe_basis_symmetric n k : symmetric_matrix n (goe_basis n k).
Proof. unfold goe_basis; apply symmetric_basis_symmetric. Qed.

Lemma goe_basis_unit_norm n k : (k <= goe_vector_index n)%coq_nat ->
  (`|goe_basis n k|)%R = 1.
Proof.
  intro Hk; unfold goe_basis.
  pose proof (goe_pairs_nth_valid n k Hk) as [H1 H2].
  apply symmetric_basis_unit_norm; assumption.
Qed.

Theorem goe_basis_orthonormal n i j :
  (i <= goe_vector_index n)%coq_nat -> (j <= goe_vector_index n)%coq_nat ->
  trace_pair n (goe_basis n i) (goe_basis n j) = if Nat.eqb i j then 1 else 0.
Proof.
  intros Hi Hj; unfold goe_basis.
  pose proof (goe_pairs_nth_valid n i Hi) as [Ha Hb].
  pose proof (goe_pairs_nth_valid n j Hj) as [Hc Hd].
  rewrite (symmetric_basis_orthonormal n _ _ _ _ Ha Hb Hc Hd).
  destruct (Nat.eq_dec i j) as [He|He].
  - subst j; rewrite !Nat.eqb_refl; reflexivity.
  - rewrite (proj2 (Nat.eqb_neq i j) He).
    destruct (andb
      (Nat.eqb (fst (List.nth i (goe_pairs n) (O,O)))
        (fst (List.nth j (goe_pairs n) (O,O))))
      (Nat.eqb (snd (List.nth i (goe_pairs n) (O,O)))
        (snd (List.nth j (goe_pairs n) (O,O))))) eqn:H;
      [|reflexivity].
    apply Bool.andb_true_iff in H as [H1 H2]; apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    exfalso; apply He; apply (goe_pairs_nth_injective n i j Hi Hj).
    destruct (List.nth i (goe_pairs n) (O,O)), (List.nth j (goe_pairs n) (O,O));
      simpl in *; congruence.
Qed.

Lemma goe_module_sum_entry n m (F : nat -> matrix n) i j :
  matrix_entry n (module_coordinate_sum (matrix_NormedModule n) m F) i j =
    coordinate_sum m (fun k => matrix_entry n (F k) i j).
Proof.
  exact (eq_trans
    (@linear_module_coordinate_sum (matrix_NormedModule n) R^o m F
      (fun M : matrix n => matrix_entry n M i j : R^o)
      (matrix_entry_linear n i j))
    (module_coordinate_sum_real m (fun k => matrix_entry n (F k) i j))).
Qed.

Theorem goe_matrix_symmetric n z : symmetric_matrix n (goe_matrix n z).
Proof.
  unfold goe_matrix; intros i j Hi Hj.
  rewrite !matrix_entry_scale !goe_module_sum_entry; f_equal.
  apply coordinate_sum_ext; intros k Hk.
  change (matrix_entry n (matrix_scale n (vector_entry (goe_vector_index n) z k)
    (goe_basis n k)) i j = matrix_entry n
    (matrix_scale n (vector_entry (goe_vector_index n) z k) (goe_basis n k)) j i).
  rewrite !matrix_entry_scale (goe_basis_symmetric n k i j Hi Hj); reflexivity.
Qed.

Theorem goe_matrix_linear n :
  linear (goe_matrix n) /\
  exists M : R, 0 < M /\ forall x : vector (goe_vector_index n),
    (`|goe_matrix n x|)%R <= M * (`|x|)%R.
Proof.
  unfold goe_matrix, matrix_scale.
  apply (@matrix_linear_comp (vector_NormedModule (goe_vector_index n))
    (matrix_NormedModule n) (matrix_NormedModule n)
    (fun z : vector (goe_vector_index n) =>
      module_coordinate_sum (matrix_NormedModule n) (goe_vector_index n)
        (fun k => (vector_entry (goe_vector_index n) z k *: goe_basis n k)%R))
    (fun M : matrix n => (goe_scale n *: M)%R)).
  - apply module_coordinate_sum_linear; intros k Hk.
    apply (@matrix_linear_comp (vector_NormedModule (goe_vector_index n)) R^o
      (matrix_NormedModule n)
      (fun z : vector (goe_vector_index n) =>
        vector_entry (goe_vector_index n) z k : R^o)
      (fun r : R^o => (r *: goe_basis n k)%R)).
    + apply tuple_entry_linear.
    + split.
      * intros a u v; rewrite /= scalerDl scalerA; reflexivity.
      * exists ((`|goe_basis n k|)%R + 1); split.
        -- assert (0 <= (`|goe_basis n k|)%R) by (apply/RleP; apply normr_ge0).
           lra.
        -- intros r; rewrite real_norm_scal_exact.
           change (Rabs r * (`|goe_basis n k|)%R <=
             ((`|goe_basis n k|)%R + 1) * Rabs r).
           assert (0 <= (`|goe_basis n k|)%R) by (apply/RleP; apply normr_ge0).
           pose proof (Rabs_pos r).
           nra.
  - split.
    + intros a u v; rewrite /= scalerDr !scalerA mulrC; reflexivity.
    + exists (Rabs (goe_scale n) + 1); split.
      * pose proof (Rabs_pos (goe_scale n)); lra.
      * intros M; rewrite real_norm_scal_exact.
        pose proof (Rabs_pos (goe_scale n)).
        assert (0 <= (`|M|)%R) by (apply/RleP; apply normr_ge0).
        nra.
Qed.

Theorem goe_matrix_coordinate_direction n k : (k <= goe_vector_index n)%coq_nat ->
  goe_matrix n (chaos_basis (goe_vector_index n) k) =
    matrix_scale n (goe_scale n) (goe_basis n k).
Proof.
  intro Hk; unfold goe_matrix; f_equal; apply matrix_ext; intros i j Hi Hj.
  rewrite goe_module_sum_entry.
  transitivity (coordinate_sum (goe_vector_index n) (fun r =>
    matrix_entry n (goe_basis n r) i j * (if Nat.eqb r k then 1 else 0))).
  - apply coordinate_sum_ext; intros r Hr.
    change (matrix_entry n (matrix_scale n
      (vector_entry (goe_vector_index n) (chaos_basis (goe_vector_index n) k) r)
      (goe_basis n r)) i j = matrix_entry n (goe_basis n r) i j * (if Nat.eqb r k then 1 else 0)).
    rewrite matrix_entry_scale (chaos_basis_entry (goe_vector_index n) k r Hr); ring.
  - exact (gradient_coordinate_sum_select (goe_vector_index n) k
      (fun r => matrix_entry n (goe_basis n r) i j) Hk).
Qed.

Theorem goe_matrix_norm_bound n z :
  (`|goe_matrix n z|)%R <= goe_scale n * INR (S (goe_vector_index n)) * (`|z|)%R.
Proof.
  unfold goe_matrix, matrix_scale; rewrite real_norm_scal_exact.
  rewrite (Rabs_pos_eq (goe_scale n) (Rlt_le _ _ (goe_scale_positive n))).
  rewrite Rmult_assoc; apply Rmult_le_compat_l; [pose proof (goe_scale_positive n); lra|].
  apply module_coordinate_sum_norm_bound; [apply/RleP; apply normr_ge0|].
  intros k Hk; rewrite real_norm_scal_exact (goe_basis_unit_norm n k Hk).
  rewrite Rmult_1_r RabsE; unfold vector_entry.
  exact (tuple_entry_norm_bound R^o (goe_vector_index n) k z).
Qed.

Theorem goe_matrix_trace n z (U : matrix n) :
  trace_pair n (goe_matrix n z) U = goe_scale n *
    coordinate_sum (goe_vector_index n) (fun k =>
      vector_entry (goe_vector_index n) z k * trace_pair n (goe_basis n k) U).
Proof.
  assert (Hscal : forall (c : R) (M : matrix n),
    trace_pair n (c *: M)%R U = c * trace_pair n M U).
  { intros c M; rewrite !(symmetric_trace_pair_comm n _ U).
    exact (trace_pair_scale n U M c). }
  unfold goe_matrix, matrix_scale.
  rewrite Hscal.
  rewrite (@linear_module_coordinate_sum (matrix_NormedModule n) R^o
    (goe_vector_index n)
    (fun k => (vector_entry (goe_vector_index n) z k *: goe_basis n k)%R)
    (fun M : matrix n => trace_pair n M U : R^o) (trace_pair_left_linear n U)).
  rewrite module_coordinate_sum_real.
  f_equal; apply coordinate_sum_ext; intros k Hk.
  apply Hscal.
Qed.

Theorem goe_basis_divergence n (L : matrix n -> matrix n) :
  coordinate_sum (goe_vector_index n) (fun k =>
    trace_pair n (goe_basis n k) (L (goe_basis n k))) = symmetric_divergence n L.
Proof. exact (goe_basis_sum n (fun E => trace_pair n E (L E))). Qed.
