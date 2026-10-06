(* Clipped quadratic data-feature scores.
   For d = S n and N rows, the clipped feature of row i of a list xs is
   paper_main_data_feature n (fun j => clip U (nth (i * d + j) xs 0)), with
   the clip max(-U, min(U, z)) of Gaussian.LipschitzClip
   (paper_main_data_clipped_feature). For symmetric B with operator norm at
   most k and weights y with Euclidean norm at most 1, the score
   sum_i y_i <Wclip_i(xs), B> is 2 k U-Lipschitz in the Euclidean distance
   of all N * d coordinates, with no sqrt N loss
   (paper_main_data_clipped_score_lipschitz, an instance of
   paper_main_data_contraction_score_lipschitz of
   Data.ClippedScore). When every sample coordinate has absolute
   value at most U, the clipped rows are the head features of the sample
   (paper_main_data_clipped_feature_head,
   paper_main_data_clipped_score_head). N = 0 and U = 0 are covered. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval boolp.
From mathcomp Require Import classical_sets functions reals Rstruct.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Matrix.Definitions Matrix.OperatorDefinitions PaperMainDefinitions
  Geometry.Psd Geometry.HeadFeature Gordon.Lipschitz Gaussian.LipschitzClip
  Spectral.SymmetricBilinear Spectral.Transport Data.FeatureMoments
  Data.FeatureMomentsRow Data.ClippedScore.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

(* 1. The clipped feature and score. *)
Definition paper_main_data_clipped_feature U n (i : nat) (xs : list R) : 'M[R]_(S n) :=
  paper_main_data_feature n
    (fun j => paper_main_gaussian_clip U (List.nth (i * S n + j)%N xs 0)).

Definition paper_main_data_clipped_score U n N (B : 'M[R]_(S n)) (y : nat -> R)
    (xs : list R) : R :=
  finite_sum (fun i => y i * paper_main_pairing (paper_main_data_clipped_feature U n i xs) B)
    (List.seq 0 N).

Lemma pmdcl_score_generic U n N B y xs :
  paper_main_data_clipped_score U n N B y xs =
  pmdc_score (paper_main_gaussian_clip U) n N B y xs.
Proof. by []. Qed.

(* 2. The score is 2kU-Lipschitz, with no sqrt N loss. *)
Theorem paper_main_data_clipped_score_lipschitz U n N (B : 'M[R]_(S n))
    (y : nat -> R) k xs ys :
  0 <= U -> paper_main_symmetric B -> 0 <= k ->
  matrix_operator_norm n (paper_main_matrix_from_public n B) <= k ->
  euclidean_norm y (List.seq 0 N) <= 1 ->
  Rabs (paper_main_data_clipped_score U n N B y xs -
        paper_main_data_clipped_score U n N B y ys) <=
    2 * k * U * paper_main_gordon_distance (N * S n) xs ys.
Proof.
move=> HU HB Hk HA Hy; rewrite !pmdcl_score_generic.
apply: (paper_main_data_contraction_score_lipschitz _ U) => //.
- by move=> z; exact: paper_main_gaussian_clip_bound.
- exact: paper_main_gaussian_clip_lipschitz.
Qed.

(* 3. When every coordinate has absolute value at most U, the clipped rows
   are the head features. *)
Lemma pmdcl_index N n i j :
  (i < N)%N -> (j < S n)%N -> (i * S n + j < N * S n)%N.
Proof.
move=> Hi Hj.
apply: (leq_trans (n := (i * S n + S n)%N)); first by rewrite ltn_add2l.
by rewrite -mulSnr leq_mul2r Hi orbT.
Qed.

Theorem paper_main_data_clipped_feature_head U n N (x : paper_main_sample N (S n)) i :
  (forall l, (l < N * S n)%N -> Rabs (List.nth l (tval x) 0) <= U) ->
  (i < N)%N ->
  paper_main_data_clipped_feature U n i (tval x) = paper_main_head_feature x i.
Proof.
move=> Hx Hi; rewrite paper_main_data_feature_head.
apply: pmdf_data_feature_ext => j.
apply: paper_main_gaussian_clip_eq; apply: Hx.
exact: pmdcl_index Hi (ltn_ord j).
Qed.

Theorem paper_main_data_clipped_score_head U n N (B : 'M[R]_(S n)) (y : nat -> R)
    (x : paper_main_sample N (S n)) :
  (forall l, (l < N * S n)%N -> Rabs (List.nth l (tval x) 0) <= U) ->
  paper_main_data_clipped_score U n N B y (tval x) =
  finite_sum (fun i => y i * paper_main_pairing (paper_main_head_feature x i) B)
    (List.seq 0 N).
Proof.
move=> Hx; apply: finite_sum_ext => i /in_seq [_ Hi].
have Hi' : (i < N)%N by apply/ssrnat.ltP; lia.
by rewrite (paper_main_data_clipped_feature_head U n N x i Hx Hi').
Qed.
