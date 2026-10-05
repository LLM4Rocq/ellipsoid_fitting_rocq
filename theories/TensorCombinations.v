From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsWeights MomentDefinitions FiniteMoments
  MatrixDefinitions OperatorDefinitions OperatorBounds TensorDefinitions TensorBounds
  TensorGibbsDefinitions TensorGibbs TensorCombinationsDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/TensorCombinations.v from Coquelicot to MathComp-Analysis.

   The original did not import Coquelicot. Its only Coquelicot content came
   through matrix n of MatrixDefinitions, through the record trace_atom and
   the predicates symmetric_matrix and tensor_represents of TensorDefinitions,
   through matrix_operator_norm of OperatorDefinitions, and through the
   lemmas of OperatorBounds, TensorBounds and TensorGibbs that it cites. The
   ports of these modules keep the same names, arguments, fields and values,
   so the text below is the original's, statements and proofs.

   MathComp is not imported here. So map, flat_map, In and the lists are
   Stdlib's, the tactics are Stdlib's (rewrite A, B keeps its meaning), and
   the arithmetic, Rabs and the order are Stdlib's, as before.
   weighted_average and finite_probability come from MomentDefinitions, and
   the lemmas cited about them from GibbsWeights and FiniteMoments. These
   modules never used Coquelicot and are unchanged. The meaning of every
   statement is unchanged. *)

Lemma tensor_weighted_join_value n q rows I (U V W : matrix n) :
  tensor_value (tensor_weighted_join n q rows I) U V W =
    weighted_average q I (fun i => tensor_value (rows i) U V W).
Proof.
  unfold tensor_weighted_join, weighted_average; induction I as [|i I IH]; simpl.
  - reflexivity.
  - rewrite tensor_value_append, tensor_scale_atoms_value, IH; reflexivity.
Qed.

Lemma tensor_weighted_join_cost n q rows I :
  tensor_cost (tensor_weighted_join n q rows I) =
    weighted_average (fun i => Rabs (q i)) I (fun i => tensor_cost (rows i)).
Proof.
  unfold tensor_weighted_join, weighted_average; induction I as [|i I IH]; simpl.
  - reflexivity.
  - rewrite tensor_cost_append, tensor_scale_atoms_cost, IH; reflexivity.
Qed.

Lemma tensor_weighted_join_probability_cost n q rows I :
  finite_probability q I ->
  tensor_cost (tensor_weighted_join n q rows I) =
    weighted_average q I (fun i => tensor_cost (rows i)).
Proof.
  intros [Hq _]; rewrite tensor_weighted_join_cost.
  unfold weighted_average; apply gibbs_sum_ext; intros i Hi.
  rewrite Rabs_pos_eq by (apply Hq; exact Hi); reflexivity.
Qed.

Theorem tensor_weighted_join_cost_bound n q rows I K :
  finite_probability q I ->
  (forall i, In i I -> tensor_cost (rows i) <= K) ->
  tensor_cost (tensor_weighted_join n q rows I) <= K.
Proof.
  intros Hq HK; rewrite tensor_weighted_join_probability_cost by exact Hq.
  eapply Rle_trans with (weighted_average q I (fun _ => K)).
  - apply weighted_average_monotone; assumption.
  - rewrite weighted_average_const by exact Hq; apply Rle_refl.
Qed.

Theorem tensor_weighted_join_represents n q rows I
    (T : nat -> matrix n -> matrix n -> matrix n -> R) :
  (forall i, In i I -> tensor_represents (T i) (rows i)) ->
  tensor_represents (fun U V W => weighted_average q I (fun i => T i U V W))
    (tensor_weighted_join n q rows I).
Proof.
  intros HT; split.
  - intros a Ha; unfold tensor_weighted_join in Ha; apply in_flat_map in Ha.
    destruct Ha as [i [Hi Ha]].
    exact (proj1 (tensor_scale_atoms_represents n (q i) (T i) (rows i) (HT i Hi)) a Ha).
  - intros U V W HU HV HW; rewrite tensor_weighted_join_value.
    apply weighted_average_ext; intros i Hi.
    apply (proj2 (HT i Hi)); assumption.
Qed.

Lemma tensor_swap23_atoms_value n atoms (U V W : matrix n) :
  tensor_value (tensor_swap23_atoms n atoms) U V W = tensor_value atoms U W V.
Proof.
  unfold tensor_swap23_atoms; induction atoms as [|a atoms IH]; simpl; [reflexivity|].
  rewrite IH; unfold atom_value; simpl; ring.
Qed.

Lemma tensor_swap23_atoms_cost n (atoms : list (trace_atom n)) :
  tensor_cost (tensor_swap23_atoms n atoms) = tensor_cost atoms.
Proof.
  unfold tensor_swap23_atoms; induction atoms as [|a atoms IH]; simpl; [reflexivity|].
  rewrite IH; unfold atom_cost; simpl; ring.
Qed.

Theorem tensor_swap23_atoms_represents n
    (T : matrix n -> matrix n -> matrix n -> R) atoms :
  tensor_represents T atoms ->
  tensor_represents (fun U V W => T U W V) (tensor_swap23_atoms n atoms).
Proof.
  intros [HS HT]; split.
  - intros a Ha; unfold tensor_swap23_atoms in Ha; apply in_map_iff in Ha.
    destruct Ha as [b [<- Hb]]; specialize (HS b Hb).
    unfold symmetric_atom in *; simpl; tauto.
  - intros U V W HU HV HW; rewrite tensor_swap23_atoms_value.
    apply HT; assumption.
Qed.

Lemma tensor_rotate_atoms_value n atoms (U V W : matrix n) :
  tensor_value (tensor_rotate_atoms n atoms) U V W = tensor_value atoms V W U.
Proof.
  unfold tensor_rotate_atoms; induction atoms as [|a atoms IH]; simpl; [reflexivity|].
  rewrite IH; unfold atom_value; simpl; ring.
Qed.

Lemma tensor_rotate_atoms_cost n (atoms : list (trace_atom n)) :
  tensor_cost (tensor_rotate_atoms n atoms) = tensor_cost atoms.
Proof.
  unfold tensor_rotate_atoms; induction atoms as [|a atoms IH]; simpl; [reflexivity|].
  rewrite IH; unfold atom_cost; simpl; ring.
Qed.

Theorem tensor_rotate_atoms_represents n
    (T : matrix n -> matrix n -> matrix n -> R) atoms :
  tensor_represents T atoms ->
  tensor_represents (fun U V W => T V W U) (tensor_rotate_atoms n atoms).
Proof.
  intros [HS HT]; split.
  - intros a Ha; unfold tensor_rotate_atoms in Ha; apply in_map_iff in Ha.
    destruct Ha as [b [<- Hb]]; specialize (HS b Hb).
    unfold symmetric_atom in *; simpl; tauto.
  - intros U V W HU HV HW; rewrite tensor_rotate_atoms_value.
    apply HT; assumption.
Qed.

Lemma mixed_trace_atoms_value n q B1 B2 B3 I (U V W : matrix n) :
  tensor_value (mixed_trace_atoms n q B1 B2 B3 I) U V W =
    weighted_average q I (fun i =>
      trace_pair n (B1 i) U * trace_pair n (B2 i) V * trace_pair n (B3 i) W).
Proof.
  unfold mixed_trace_atoms, weighted_average; induction I as [|i I IH]; simpl; [reflexivity|].
  rewrite IH; unfold atom_value; simpl; ring.
Qed.

Lemma mixed_trace_atoms_cost n q B1 B2 B3 I :
  tensor_cost (mixed_trace_atoms n q B1 B2 B3 I) =
    weighted_average (fun i => Rabs (q i)) I (fun i =>
      matrix_operator_norm n (B1 i) * matrix_operator_norm n (B2 i) *
        matrix_operator_norm n (B3 i)).
Proof.
  unfold mixed_trace_atoms, weighted_average; induction I as [|i I IH]; simpl; [reflexivity|].
  rewrite IH; unfold atom_cost; simpl; ring.
Qed.

Theorem mixed_trace_atoms_represents n q B1 B2 B3 I :
  (forall i, In i I -> symmetric_matrix n (B1 i)) ->
  (forall i, In i I -> symmetric_matrix n (B2 i)) ->
  (forall i, In i I -> symmetric_matrix n (B3 i)) ->
  tensor_represents (fun U V W => weighted_average q I (fun i =>
    trace_pair n (B1 i) U * trace_pair n (B2 i) V * trace_pair n (B3 i) W))
    (mixed_trace_atoms n q B1 B2 B3 I).
Proof.
  intros H1 H2 H3; split.
  - intros a Ha; unfold mixed_trace_atoms in Ha; apply in_map_iff in Ha.
    destruct Ha as [i [<- Hi]]; unfold symmetric_atom; simpl; repeat split; auto.
  - intros U V W HU HV HW; symmetry; apply mixed_trace_atoms_value.
Qed.

Lemma mixed_trace_atoms_probability_cost n q B1 B2 B3 I :
  finite_probability q I ->
  tensor_cost (mixed_trace_atoms n q B1 B2 B3 I) =
    weighted_average q I (fun i =>
      matrix_operator_norm n (B1 i) * matrix_operator_norm n (B2 i) *
        matrix_operator_norm n (B3 i)).
Proof.
  intros [Hq _]; rewrite mixed_trace_atoms_cost.
  unfold weighted_average; apply gibbs_sum_ext; intros i Hi.
  rewrite Rabs_pos_eq by (apply Hq; exact Hi); reflexivity.
Qed.

Theorem mixed_trace_atoms_cost_bound n q B1 B2 B3 I K1 K2 K3 :
  finite_probability q I -> 0 <= K1 -> 0 <= K2 -> 0 <= K3 ->
  (forall i, In i I -> matrix_operator_norm n (B1 i) <= K1) ->
  (forall i, In i I -> matrix_operator_norm n (B2 i) <= K2) ->
  (forall i, In i I -> matrix_operator_norm n (B3 i) <= K3) ->
  tensor_cost (mixed_trace_atoms n q B1 B2 B3 I) <= K1 * K2 * K3.
Proof.
  intros Hq HK1 HK2 HK3 H1 H2 H3; rewrite mixed_trace_atoms_probability_cost by exact Hq.
  eapply Rle_trans with (weighted_average q I (fun _ => K1 * K2 * K3)).
  - apply weighted_average_monotone; [exact Hq|]; intros i Hi.
    apply Rmult_le_compat.
    + apply Rmult_le_pos; apply matrix_operator_norm_nonnegative.
    + apply matrix_operator_norm_nonnegative.
    + apply Rmult_le_compat; try apply matrix_operator_norm_nonnegative; auto.
    + apply H3; exact Hi.
  - rewrite weighted_average_const by exact Hq; apply Rle_refl.
Qed.
