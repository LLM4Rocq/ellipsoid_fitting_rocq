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

(* Port of the inner module GoeSynthesis of theories/InterpolationProofs.v
   (also copied in GoeProofs.v and JointProofs.v) from Coquelicot to
   MathComp-Analysis, as a standalone module.

   Every lemma and theorem of the original keeps its name and its
   arguments, in the same order. No item is added. The statements change
   form in four ways, as in the ports of MatrixCoordinates, CoefficientMaps
   and the restated challenge ellipsoid_goe.

   1. Order on indices. With ssreflect loaded, (k <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statements of goe_basis_unit_norm, goe_basis_orthonormal and
      goe_matrix_coordinate_direction write (k <= n)%coq_nat, which is
      Stdlib's le. This is the same term that GoePairs writes as
      (k <= n)%nat, because GoePairs loads no MathComp module. The proofs
      write List.nth for Stdlib's nth, since nth alone is MathComp's seq.nth
      here.

   2. Norms. Coquelicot's norm becomes MathComp's norm (`|_|)%R, in
      goe_basis_unit_norm and goe_matrix_norm_bound. The norm on matrix n is
      the Frobenius norm and the norm on vector k the Euclidean norm, as in
      Coquelicot, because the port of MatrixDefinitions nests
      euclidean_product (analysis/README.md, difference 1). So both
      statements mean the same, constants included.

   3. Linear maps. Coquelicot's is_linear l in goe_matrix_linear becomes the
      conjunction
        linear l /\ exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound, the
      form of MatrixCoordinates and of group 2 of the restated challenge
      ellipsoid_goe (analysis/README.md, difference 2). It is equivalent to
      Coquelicot's record.

   4. Frechet derivatives. Coquelicot's filterdiff f (locally z) l in
      goe_matrix_frechet becomes is_diff z f l of MathComp-Analysis, as in
      MatrixCoordinates.

   The other statements keep the text of the original: goe_scale_positive,
   goe_scale_square, goe_basis_symmetric, goe_module_sum_entry,
   goe_matrix_symmetric, goe_matrix_trace and goe_basis_divergence.

   The proofs follow the original. Coquelicot's is_linear_comp becomes
   matrix_linear_comp of MatrixCoordinates, filterdiff_linear becomes
   matrix_linear_is_diff, and norm_ge_0 becomes normr_ge0. Coquelicot's
   is_linear_scal_l and is_linear_scal_r, the linearity of r |-> r *: B and
   of M |-> c *: M, are proved inline in goe_matrix_linear. Coquelicot's
   linear_scal, applied to the map B |-> trace_pair n B U, is replaced in
   goe_matrix_trace by the symmetry symmetric_trace_pair_comm of
   SymmetricBasis and trace_pair_scale of MatrixTrace. *)

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

Theorem goe_matrix_frechet n z : is_diff z (goe_matrix n) (goe_matrix n).
Proof. apply matrix_linear_is_diff; apply goe_matrix_linear. Qed.

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
