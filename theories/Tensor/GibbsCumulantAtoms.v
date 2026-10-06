From Stdlib Require Import Reals List Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Gibbs.CumulantDefinitions Gibbs.Cumulants
  Gibbs.WeightedAverageDefinitions Gibbs.WeightedAverageMoments
  Matrix.Definitions Matrix.EntriesAndLinearMaps Matrix.Trace
  Matrix.OperatorDefinitions Matrix.OperatorNorm Matrix.OperatorNormProperties
  Tensor.Definitions Tensor.ProjectiveNormBounds Tensor.GibbsDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Third cumulants of finite Gibbs laws as sums of rank-one trilinear forms
   of bounded cost. A list of atoms represents a trilinear form T on
   symmetric matrices (tensor_represents) when every atom has symmetric
   matrices B1, B2, B3 and T U V W is the sum over the atoms of
   c * trace_pair B1 U * trace_pair B2 V * trace_pair B3 W. The cost
   tensor_cost is the sum of |c| times the operator norms of B1, B2, B3.
   - trace_pair_left_add, trace_pair_left_zero, trace_pair_left_scale and
     matrix_weighted_sum_trace: trace_pair is linear in its first argument.
   - matrix_weighted_sum_operator_bound,
     matrix_probability_mean_operator_bound and
     matrix_centered_operator_bound: under a probability vector q, the mean
     of matrices of operator norm at most K has norm at most K, and a
     centered matrix B i - mean has norm at most 2 * K.
   - matrix_weighted_sum_symmetric and matrix_centered_symmetric: means and
     centered matrices of symmetric matrices are symmetric.
   - centered_trace_atoms_represents and centered_trace_atoms_cost_bound:
     the third cumulant weighted_matrix_cumulant of the pairings with
     symmetric matrices B i is represented by the atoms of the centered
     matrices, with cost at most 8 * K ^ 3.
   - gibbs_centered_trace_atoms_represents: the same for gibbs_cumulant3,
     the third cumulant under a finite Gibbs law.
   - tensor_scale_atoms_represents: scaling the coefficients of the atoms
     by a scales the form by a (and the cost by |a|). *)

Lemma trace_pair_left_add n (A B U : matrix n) :
  trace_pair n (matrix_add n A B) U = trace_pair n A U + trace_pair n B U.
Proof.
  have HL := proj1 (trace_pair_left_linear n U).
  have H := HL 1%R A B.
  rewrite scale1r in H.
  unfold matrix_add; rewrite H scale1r; reflexivity.
Qed.

Lemma trace_pair_left_zero n (U : matrix n) : trace_pair n (matrix_zero n) U = 0.
Proof.
  have H := trace_pair_left_add n (matrix_zero n) (matrix_zero n) U.
  have E : matrix_add n (matrix_zero n) (matrix_zero n) = matrix_zero n.
  { unfold matrix_add, matrix_zero; exact: addr0. }
  rewrite E in H; lra.
Qed.

Lemma trace_pair_left_scale n a (B U : matrix n) :
  trace_pair n (matrix_scale n a B) U = a * trace_pair n B U.
Proof.
  have HL := proj1 (trace_pair_left_linear n U).
  have H := HL a B (matrix_zero n).
  have E : (a *: B + matrix_zero n)%R = matrix_scale n a B.
  { unfold matrix_zero, matrix_scale; exact: addr0. }
  rewrite E in H; rewrite H (trace_pair_left_zero n U) addr0; reflexivity.
Qed.

Theorem matrix_weighted_sum_trace n q B I (U : matrix n) :
  trace_pair n (matrix_weighted_sum n q B I) U =
    weighted_average q I (fun i => trace_pair n (B i) U).
Proof.
  unfold weighted_average; induction I as [|i I IH]; simpl.
  - apply trace_pair_left_zero.
  - rewrite trace_pair_left_add trace_pair_left_scale IH; reflexivity.
Qed.

Theorem matrix_weighted_sum_operator_bound n q B I :
  matrix_operator_norm n (matrix_weighted_sum n q B I) <=
    weighted_average (fun i => Rabs (q i)) I (fun i => matrix_operator_norm n (B i)).
Proof.
  unfold weighted_average; induction I as [|i I IH]; simpl.
  - rewrite matrix_operator_norm_zero; lra.
  - eapply Rle_trans; [apply matrix_operator_norm_triangle|].
    rewrite matrix_operator_norm_scale; apply Rplus_le_compat; [apply Rle_refl|exact IH].
Qed.

Theorem matrix_probability_mean_operator_bound n q B I K :
  finite_probability q I ->
  (forall i, In i I -> matrix_operator_norm n (B i) <= K) ->
  matrix_operator_norm n (matrix_weighted_sum n q B I) <= K.
Proof.
  intros Hq HB.
  eapply Rle_trans; [apply matrix_weighted_sum_operator_bound|].
  assert (HE : weighted_average (fun i => Rabs (q i)) I (fun i => matrix_operator_norm n (B i)) =
    weighted_average q I (fun i => matrix_operator_norm n (B i))).
  { unfold weighted_average; apply gibbs_sum_ext; intros i Hi.
    rewrite (Rabs_pos_eq (q i) (proj1 Hq i Hi)); reflexivity. }
  rewrite HE.
  eapply Rle_trans with (weighted_average q I (fun _ => K)).
  - apply weighted_average_monotone; assumption.
  - rewrite (weighted_average_const q I K Hq); lra.
Qed.

Theorem matrix_centered_operator_bound n q B I K i :
  finite_probability q I ->
  (forall j, In j I -> matrix_operator_norm n (B j) <= K) -> In i I ->
  matrix_operator_norm n (matrix_centered n q B I i) <= 2 * K.
Proof.
  intros Hq HB Hi; unfold matrix_centered.
  pose proof (matrix_probability_mean_operator_bound n q B I K Hq HB) as HM.
  eapply Rle_trans; [apply matrix_operator_norm_triangle|].
  rewrite matrix_operator_norm_scale.
  replace (Rabs (-1)) with 1 by (rewrite Rabs_left; lra).
  specialize (HB i Hi); lra.
Qed.

Lemma matrix_zero_symmetric n : symmetric_matrix n (matrix_zero n).
Proof. intros i j Hi Hj; rewrite !matrix_entry_zero; reflexivity. Qed.

Lemma matrix_add_symmetric n (A B : matrix n) :
  symmetric_matrix n A -> symmetric_matrix n B -> symmetric_matrix n (matrix_add n A B).
Proof.
  intros HA HB i j Hi Hj.
  rewrite !matrix_entry_add (HA i j Hi Hj) (HB i j Hi Hj); reflexivity.
Qed.

Lemma matrix_scale_symmetric n a (B : matrix n) :
  symmetric_matrix n B -> symmetric_matrix n (matrix_scale n a B).
Proof.
  intros HB i j Hi Hj; rewrite !matrix_entry_scale (HB i j Hi Hj); reflexivity.
Qed.

Theorem matrix_weighted_sum_symmetric n q B I :
  (forall i, In i I -> symmetric_matrix n (B i)) ->
  symmetric_matrix n (matrix_weighted_sum n q B I).
Proof.
  induction I as [|i I IH]; intros HB; simpl.
  - apply matrix_zero_symmetric.
  - apply matrix_add_symmetric.
    + apply matrix_scale_symmetric, HB; simpl; auto.
    + apply IH; intros j Hj; apply HB; simpl; auto.
Qed.

Theorem matrix_centered_symmetric n q B I i :
  (forall j, In j I -> symmetric_matrix n (B j)) -> In i I ->
  symmetric_matrix n (matrix_centered n q B I i).
Proof.
  intros HB Hi; unfold matrix_centered; apply matrix_add_symmetric.
  - apply HB; exact Hi.
  - apply matrix_scale_symmetric, matrix_weighted_sum_symmetric; exact HB.
Qed.

Lemma matrix_centered_trace n q B I i (U : matrix n) :
  trace_pair n (matrix_centered n q B I i) U =
    trace_pair n (B i) U - weighted_average q I (fun j => trace_pair n (B j) U).
Proof.
  unfold matrix_centered.
  rewrite trace_pair_left_add trace_pair_left_scale matrix_weighted_sum_trace.
  ring.
Qed.

Lemma tensor_gibbs_finite_probability c f I :
  I <> [] -> finite_probability (gibbs_weight c f I) I.
Proof.
  intros HI; split.
  - intros; apply gibbs_weight_nonnegative; exact HI.
  - apply gibbs_weights_normalized; exact HI.
Qed.

Theorem matrix_gibbs_mean_trace n c f I B (U : matrix n) :
  trace_pair n (matrix_gibbs_mean n c f I B) U =
    gibbs_average c f I (fun i => trace_pair n (B i) U).
Proof. unfold matrix_gibbs_mean; rewrite matrix_weighted_sum_trace; reflexivity. Qed.

Theorem matrix_gibbs_mean_operator_bound n c f I B K :
  I <> [] -> (forall i, In i I -> matrix_operator_norm n (B i) <= K) ->
  matrix_operator_norm n (matrix_gibbs_mean n c f I B) <= K.
Proof.
  intros HI HB; unfold matrix_gibbs_mean; apply matrix_probability_mean_operator_bound.
  - apply tensor_gibbs_finite_probability; exact HI.
  - exact HB.
Qed.

Lemma diagonal_trace_atoms_value n q B I (U V W : matrix n) :
  tensor_value (diagonal_trace_atoms n q B I) U V W =
  weighted_average q I (fun i => trace_pair n (B i) U * trace_pair n (B i) V * trace_pair n (B i) W).
Proof.
  unfold diagonal_trace_atoms, weighted_average; induction I as [|i I IH]; simpl; [ring|].
  unfold atom_value; simpl; rewrite IH; ring.
Qed.

Lemma diagonal_trace_atoms_cost n q B I :
  tensor_cost (diagonal_trace_atoms n q B I) =
    weighted_average (fun i => Rabs (q i)) I (fun i => matrix_operator_norm n (B i) ^ 3).
Proof.
  unfold diagonal_trace_atoms, weighted_average; induction I as [|i I IH]; simpl; [ring|].
  unfold atom_cost; simpl; rewrite IH; simpl; ring.
Qed.

Theorem centered_trace_atoms_represents n q B I :
  (forall i, In i I -> symmetric_matrix n (B i)) ->
  tensor_represents (weighted_matrix_cumulant n q B I) (centered_trace_atoms n q B I).
Proof.
  intros HB; split.
  - intros a Ha; unfold centered_trace_atoms, diagonal_trace_atoms in Ha.
    apply in_map_iff in Ha; destruct Ha as [i [<- Hi]].
    unfold symmetric_atom; simpl; repeat split; apply matrix_centered_symmetric; assumption.
  - intros U V W HU HV HW; unfold weighted_matrix_cumulant, centered_trace_atoms.
    rewrite diagonal_trace_atoms_value; apply weighted_average_ext; intros i Hi.
    rewrite !matrix_centered_trace; reflexivity.
Qed.

Theorem centered_trace_atoms_cost_bound n q B I K :
  finite_probability q I ->
  (forall i, In i I -> matrix_operator_norm n (B i) <= K) ->
  tensor_cost (centered_trace_atoms n q B I) <= 8 * K ^ 3.
Proof.
  intros Hq HB; unfold centered_trace_atoms; rewrite diagonal_trace_atoms_cost.
  assert (HE : weighted_average (fun i => Rabs (q i)) I
    (fun i => matrix_operator_norm n (matrix_centered n q B I i) ^ 3) =
    weighted_average q I (fun i => matrix_operator_norm n (matrix_centered n q B I i) ^ 3)).
  { unfold weighted_average; apply gibbs_sum_ext; intros i Hi.
    rewrite (Rabs_pos_eq (q i) (proj1 Hq i Hi)); reflexivity. }
  rewrite HE.
  eapply Rle_trans with (weighted_average q I (fun _ => 8 * K ^ 3)).
  - apply weighted_average_monotone; [exact Hq|].
    intros i Hi; replace (8 * K ^ 3) with ((2 * K) ^ 3) by ring.
    apply pow_incr; split.
    + apply matrix_operator_norm_nonnegative.
    + apply matrix_centered_operator_bound; assumption.
  - rewrite (weighted_average_const q I (8 * K ^ 3) Hq); lra.
Qed.

Theorem gibbs_centered_trace_atoms_represents n c f I B :
  (forall i, In i I -> symmetric_matrix n (B i)) ->
  tensor_represents
    (fun U V W => gibbs_cumulant3 c f I (fun i => trace_pair n (B i) U)
      (fun i => trace_pair n (B i) V) (fun i => trace_pair n (B i) W))
    (centered_trace_atoms n (gibbs_weight c f I) B I).
Proof.
  intros HB.
  change (tensor_represents (weighted_matrix_cumulant n (gibbs_weight c f I) B I)
    (centered_trace_atoms n (gibbs_weight c f I) B I)).
  apply centered_trace_atoms_represents; exact HB.
Qed.

Lemma tensor_scale_atoms_value n a (atoms : list (trace_atom n)) U V W :
  tensor_value (tensor_scale_atoms a atoms) U V W = a * tensor_value atoms U V W.
Proof.
  unfold tensor_scale_atoms; induction atoms as [|t atoms IH]; simpl; [ring|].
  rewrite IH; unfold atom_value, tensor_scale_atom; simpl; ring.
Qed.

Lemma tensor_scale_atoms_cost n a (atoms : list (trace_atom n)) :
  tensor_cost (tensor_scale_atoms a atoms) = Rabs a * tensor_cost atoms.
Proof.
  unfold tensor_scale_atoms; induction atoms as [|t atoms IH]; simpl; [ring|].
  rewrite IH; unfold atom_cost, tensor_scale_atom; simpl; rewrite Rabs_mult; ring.
Qed.

Theorem tensor_scale_atoms_represents n a (T : matrix n -> matrix n -> matrix n -> R) atoms :
  tensor_represents T atoms -> tensor_represents (fun U V W => a * T U V W) (tensor_scale_atoms a atoms).
Proof.
  intros [HS HT]; split.
  - intros t Ht; unfold tensor_scale_atoms in Ht; apply in_map_iff in Ht.
    destruct Ht as [s [<- Hs]]; apply HS in Hs.
    exact Hs.
  - intros U V W HU HV HW.
    rewrite tensor_scale_atoms_value (HT U V W HU HV HW); reflexivity.
Qed.
