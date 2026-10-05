From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions
  MomentDefinitions FiniteMoments MatrixDefinitions MatrixGibbsDefinitions
  MatrixSecondDefinitions MatrixThirdDefinitions OperatorDefinitions TensorDefinitions
  TensorBounds TensorGibbsDefinitions TensorGibbs TensorCombinationsDefinitions
  TensorCombinations TensorNestedDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/TensorNestedRepresentation.v from Coquelicot to
   MathComp-Analysis. The original did not import Coquelicot. Its only
   Coquelicot content came through matrix n and trace_pair of
   MatrixDefinitions, through the record trace_atom and the predicates
   symmetric_matrix and tensor_represents of TensorDefinitions, and through
   the definitions and lemmas of the matrix, tensor and nested modules it
   cites. The ports of these modules keep the same names, arguments, fields
   and values, so the text below is the original's, statements and proofs.

   MathComp is not imported here. So the lists, In, map and [] are Stdlib's,
   the tactics are Stdlib's (rewrite A, B keeps its meaning), and the
   arithmetic, including the powers gamma ^ 2 and beta ^ 2, the products and
   the minus signs of - beta and - beta * gamma, is Stdlib's, as before.
   gibbs_average, gibbs_covariance, gibbs_cumulant3 and weighted_average come
   from modules that never used Coquelicot and are unchanged. The only change
   of notation upstream is in symmetric_matrix, whose port writes the order
   on indices as (i <= n)%coq_nat, Stdlib's le, as the original meant. The
   meaning of every statement is unchanged. *)

Lemma nested_mean_matrix_trace n gamma offset coeff S (A U : matrix n) y :
  trace_pair n (nested_mean_matrix n gamma offset coeff S A y) U =
    matrix_inner_derivative n gamma offset coeff S A U y.
Proof.
  unfold nested_mean_matrix, matrix_inner_derivative; apply matrix_gibbs_mean_trace.
Qed.

Lemma nested_inner_center_trace n gamma offset coeff S (A U : matrix n) y s :
  trace_pair n (nested_inner_center n gamma offset coeff S A y s) U =
    trace_pair n (coeff y s) U - matrix_inner_derivative n gamma offset coeff S A U y.
Proof.
  unfold nested_inner_center; rewrite matrix_centered_trace; reflexivity.
Qed.

Lemma nested_outer_center_trace n beta gamma offset coeff Y S (A U : matrix n) y :
  trace_pair n (nested_outer_center n beta gamma offset coeff Y S A y) U =
    matrix_inner_derivative n gamma offset coeff S A U y -
    weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (matrix_inner_derivative n gamma offset coeff S A U).
Proof.
  unfold nested_outer_center; rewrite matrix_centered_trace, nested_mean_matrix_trace.
  f_equal; apply weighted_average_ext; intros i Hi; apply nested_mean_matrix_trace.
Qed.

Lemma nested_gibbs_covariance_right_centered c f I u v :
  gibbs_covariance c f I u v =
    gibbs_average c f I (fun i => u i * (v i - gibbs_average c f I v)).
Proof.
  transitivity (gibbs_average c f I (fun i => u i * v i + (- gibbs_average c f I v) * u i)).
  - rewrite gibbs_average_add, gibbs_average_scale; unfold gibbs_covariance; ring.
  - apply gibbs_average_ext; intros; ring.
Qed.

Theorem nested_inner_atom_rows_represents n gamma offset coeff S (A : matrix n) y :
  (forall s, In s S -> symmetric_matrix n (coeff y s)) ->
  tensor_represents (fun U V W => matrix_inner_cumulant n gamma offset coeff S A U V W y)
    (nested_inner_atom_rows n gamma offset coeff S A y).
Proof.
  intros HC; unfold nested_inner_atom_rows, nested_inner_weights, matrix_inner_cumulant.
  apply gibbs_centered_trace_atoms_represents; exact HC.
Qed.

Theorem nested_inner_atoms_represents n beta gamma offset coeff Y S (A : matrix n) :
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  tensor_represents (fun U V W =>
    gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (fun y => matrix_inner_cumulant n gamma offset coeff S A U V W y))
    (nested_inner_atoms n beta gamma offset coeff Y S A).
Proof.
  intros HC; unfold nested_inner_atoms.
  change (tensor_represents (fun U V W =>
    weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (fun y => matrix_inner_cumulant n gamma offset coeff S A U V W y))
    (tensor_weighted_join n (nested_outer_weights n beta gamma offset coeff Y S A)
      (nested_inner_atom_rows n gamma offset coeff S A) Y)).
  apply tensor_weighted_join_represents; intros y Hy.
  apply nested_inner_atom_rows_represents; intros s Hs; apply HC; assumption.
Qed.

Lemma nested_inner_center_covariance n gamma offset coeff S (A U V : matrix n) y :
  S <> [] ->
  weighted_average (nested_inner_weights n gamma offset coeff S A y) S
    (fun s => trace_pair n (nested_inner_center n gamma offset coeff S A y s) U *
      trace_pair n (nested_inner_center n gamma offset coeff S A y s) V) =
    matrix_inner_covariance n gamma offset coeff S A U V y.
Proof.
  intros HS; unfold matrix_inner_covariance; rewrite gibbs_covariance_centered by exact HS.
  apply gibbs_average_ext; intros s Hs; rewrite !nested_inner_center_trace; reflexivity.
Qed.

Lemma nested_covariance_atom_rows_value n beta gamma offset coeff Y S (A U V W : matrix n) y :
  S <> [] ->
  tensor_value (nested_covariance_atom_rows n beta gamma offset coeff Y S A y) U V W =
    matrix_inner_covariance n gamma offset coeff S A U V y *
      trace_pair n (nested_outer_center n beta gamma offset coeff Y S A y) W.
Proof.
  intros HS; unfold nested_covariance_atom_rows; rewrite mixed_trace_atoms_value.
  transitivity (weighted_average (nested_inner_weights n gamma offset coeff S A y) S
    (fun s => trace_pair n (nested_outer_center n beta gamma offset coeff Y S A y) W *
      (trace_pair n (nested_inner_center n gamma offset coeff S A y s) U *
       trace_pair n (nested_inner_center n gamma offset coeff S A y s) V))).
  - apply weighted_average_ext; intros; ring.
  - rewrite weighted_average_scale, nested_inner_center_covariance by exact HS; ring.
Qed.

Theorem nested_covariance_atom_rows_represents n beta gamma offset coeff Y S (A : matrix n) y :
  S <> [] -> In y Y ->
  (forall z s, In z Y -> In s S -> symmetric_matrix n (coeff z s)) ->
  tensor_represents (fun U V W =>
    matrix_inner_covariance n gamma offset coeff S A U V y *
      trace_pair n (nested_outer_center n beta gamma offset coeff Y S A y) W)
    (nested_covariance_atom_rows n beta gamma offset coeff Y S A y).
Proof.
  intros HS Hy HC; split.
  - intros a Ha; unfold nested_covariance_atom_rows, mixed_trace_atoms in Ha.
    apply in_map_iff in Ha; destruct Ha as [s [<- Hs]].
    unfold symmetric_atom; simpl; split.
    + unfold nested_inner_center; apply matrix_centered_symmetric; [intros; apply HC|]; assumption.
    + split.
      * unfold nested_inner_center; apply matrix_centered_symmetric; [intros; apply HC|]; assumption.
      * unfold nested_outer_center; apply matrix_centered_symmetric; [|exact Hy].
        intros z Hz; unfold nested_mean_matrix, matrix_gibbs_mean.
        apply matrix_weighted_sum_symmetric; intros t Ht; apply HC; assumption.
  - intros U V W HU HV HW; symmetry; apply nested_covariance_atom_rows_value; exact HS.
Qed.

Theorem nested_covariance_atoms_represents n beta gamma offset coeff Y S (A : matrix n) :
  S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  tensor_represents (fun U V W =>
    gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (fun y => matrix_inner_covariance n gamma offset coeff S A U V y)
      (matrix_inner_derivative n gamma offset coeff S A W))
    (nested_covariance_atoms n beta gamma offset coeff Y S A).
Proof.
  intros HS HC.
  assert (HR : tensor_represents (fun U V W =>
    weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (fun y => matrix_inner_covariance n gamma offset coeff S A U V y *
        trace_pair n (nested_outer_center n beta gamma offset coeff Y S A y) W))
    (nested_covariance_atoms n beta gamma offset coeff Y S A)).
  { unfold nested_covariance_atoms; apply tensor_weighted_join_represents; intros y Hy.
    apply nested_covariance_atom_rows_represents; assumption. }
  split; [exact (proj1 HR)|].
  intros U V W HU HV HW; rewrite <- (proj2 HR U V W HU HV HW).
  rewrite nested_gibbs_covariance_right_centered.
  apply gibbs_average_ext; intros y Hy; rewrite nested_outer_center_trace; reflexivity.
Qed.

Theorem nested_outer_atoms_represents n beta gamma offset coeff Y S (A : matrix n) :
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  tensor_represents (fun U V W =>
    gibbs_cumulant3 (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_derivative n gamma offset coeff S A U)
      (matrix_inner_derivative n gamma offset coeff S A V)
      (matrix_inner_derivative n gamma offset coeff S A W))
    (nested_outer_atoms n beta gamma offset coeff Y S A).
Proof.
  intros HC.
  assert (HR : tensor_represents
    (weighted_matrix_cumulant n (nested_outer_weights n beta gamma offset coeff Y S A)
      (nested_mean_matrix n gamma offset coeff S A) Y)
    (nested_outer_atoms n beta gamma offset coeff Y S A)).
  { unfold nested_outer_atoms; apply centered_trace_atoms_represents; intros y Hy.
    unfold nested_mean_matrix, matrix_gibbs_mean; apply matrix_weighted_sum_symmetric.
    intros s Hs; apply HC; assumption. }
  split; [exact (proj1 HR)|].
  intros U V W HU HV HW; rewrite <- (proj2 HR U V W HU HV HW).
  unfold gibbs_cumulant3, weighted_matrix_cumulant.
  apply gibbs_average_ext; intros y Hy.
  rewrite !nested_mean_matrix_trace.
  assert (HE : forall H : matrix n,
    weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (fun z => trace_pair n (nested_mean_matrix n gamma offset coeff S A z) H) =
    weighted_average (nested_outer_weights n beta gamma offset coeff Y S A) Y
      (matrix_inner_derivative n gamma offset coeff S A H)).
  { intros H; apply weighted_average_ext; intros z Hz; apply nested_mean_matrix_trace. }
  rewrite !HE; reflexivity.
Qed.

Theorem nested_third_atoms_represents n beta gamma offset coeff Y S (A : matrix n) :
  S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  tensor_represents (matrix_nested_third_derivative n beta gamma offset coeff Y S A)
    (nested_third_atoms n beta gamma offset coeff Y S A).
Proof.
  intros HS HC.
  pose proof (nested_inner_atoms_represents n beta gamma offset coeff Y S A HC) as HI.
  pose proof (nested_covariance_atoms_represents n beta gamma offset coeff Y S A HS HC) as HM.
  pose proof (nested_outer_atoms_represents n beta gamma offset coeff Y S A HC) as HO.
  pose proof (tensor_swap23_atoms_represents n _ _ HM) as HMS.
  pose proof (tensor_rotate_atoms_represents n _ _ HM) as HMR.
  pose proof (tensor_represents_add n _ _ _ _ HMS HMR) as HMP.
  pose proof (tensor_represents_add n _ _ _ _ HM HMP) as HMA.
  pose proof (tensor_scale_atoms_represents n (gamma ^ 2) _ _ HI) as HSI.
  pose proof (tensor_scale_atoms_represents n (- beta * gamma) _ _ HMA) as HSM.
  pose proof (tensor_scale_atoms_represents n (beta ^ 2) _ _ HO) as HSO.
  pose proof (tensor_represents_add n _ _ _ _ HSM HSO) as HREST.
  pose proof (tensor_represents_add n _ _ _ _ HSI HREST) as HR.
  split; [exact (proj1 HR)|].
  intros U V W HU HV HW.
  unfold nested_third_atoms; rewrite <- (proj2 HR U V W HU HV HW).
  unfold matrix_nested_third_derivative; ring.
Qed.
