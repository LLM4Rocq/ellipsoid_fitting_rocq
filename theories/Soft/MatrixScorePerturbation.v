From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Chaos.CubicMassBounds Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Gibbs.MatrixDefinitions
  Gibbs.MatrixSecondDerivativeDefinitions
  Gibbs.MatrixThirdDerivativeDefinitions Gibbs.MatrixThirdDerivative
  Tensor.Definitions Tensor.GibbsCumulantAtoms Tensor.ProjectiveSum
  Soft.MatrixDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Perturbation of one block of the soft matrix scores.
   soft_matrix_scores_perturbation: for i in a duplicate-free index list
   I, adding M to the block A i (soft_matrix_block_add) turns the scores
   soft_matrix_scores n y B I into the affine scores
   matrix_affine_scores of M, whose offsets are the old scores and whose
   coefficients are soft_matrix_coefficients n y B i. On the way: the
   exchange of two coordinate sums, the symmetry of trace_pair, and the sum
   over I of a function that vanishes off the index i
   (soft_matrix_single_sum).

   With ssreflect loaded, if d then a else b on a decision
   d : {j = i} + {j <> i} elaborates to a test on the boolean is_left d.
   The statement of soft_matrix_single_sum and the proof of
   soft_matrix_scores_perturbation therefore write the match
   match Nat.eq_dec j i with left _ => x | right _ => 0 end. *)

Lemma soft_matrix_coordinate_sum_add n f g :
  coordinate_sum n (fun i => f i + g i) = coordinate_sum n f + coordinate_sum n g.
Proof. revert f g; induction n; intros f g; simpl; [ring|rewrite IHn; ring]. Qed.

Lemma soft_matrix_coordinate_sum_swap n m f :
  coordinate_sum n (fun i => coordinate_sum m (f i)) =
    coordinate_sum m (fun j => coordinate_sum n (fun i => f i j)).
Proof.
  revert f; induction n; intros f; simpl; [reflexivity|].
  rewrite soft_matrix_coordinate_sum_add IHn; reflexivity.
Qed.

Lemma soft_matrix_trace_pair_swap n (A B : matrix n) : trace_pair n A B = trace_pair n B A.
Proof.
  unfold trace_pair; rewrite soft_matrix_coordinate_sum_swap.
  apply coordinate_sum_ext; intros i Hi; apply coordinate_sum_ext; intros j Hj; ring.
Qed.

Lemma soft_matrix_single_sum I i x :
  NoDup I -> In i I -> finite_sum (fun j => match Nat.eq_dec j i with left _ => x | right _ => 0 end) I = x.
Proof.
  induction I as [|j I IH]; intros HD Hi; [contradiction|].
  inversion HD as [|j' I' Hnot Htail]; subst.
  simpl in Hi |- *; destruct (Nat.eq_dec j i) as [Heq|Hne].
  - subst j.
    assert (HZ : finite_sum (fun j => match Nat.eq_dec j i with left _ => x | right _ => 0 end) I = 0).
    { transitivity (finite_sum (fun _ => 0) I).
      - apply gibbs_sum_ext; intros j Hj; destruct (Nat.eq_dec j i); [subst; contradiction|reflexivity].
      - apply gibbs_sum_zero. }
    rewrite HZ; ring.
  - destruct Hi as [Heq|Hi]; [contradiction|].
    rewrite (IH Htail Hi); ring.
Qed.

Theorem soft_matrix_scores_perturbation n y B I (A : nat -> matrix n) i (M : matrix n) :
  NoDup I -> In i I ->
  soft_matrix_scores n y B I (soft_matrix_block_add n A i M) =
    matrix_affine_scores n (soft_matrix_scores n y B I A) (soft_matrix_coefficients n y B i) M.
Proof.
  intros HD Hi; apply functional_extensionality; intros z.
  apply functional_extensionality; intros s.
  unfold soft_matrix_scores at 1.
  transitivity (finite_sum (fun j => y z j * trace_pair n (B s) (A j) +
    match Nat.eq_dec j i with left _ => y z i * trace_pair n (B s) M | right _ => 0 end) I).
  - apply gibbs_sum_ext; intros j Hj; unfold soft_matrix_block_add.
    destruct (Nat.eq_dec j i); [subst; rewrite trace_pair_add; ring|ring].
  - rewrite gibbs_sum_add (soft_matrix_single_sum I i _ HD Hi).
    unfold matrix_affine_scores, soft_matrix_coefficients; rewrite trace_pair_left_scale; reflexivity.
Qed.
