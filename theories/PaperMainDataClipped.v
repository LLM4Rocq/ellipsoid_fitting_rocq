(* Clipped quadratic data-feature scores (G11, checkpoint A).
   For d = S n and N rows, the clipped public feature of row i of a list xs is
   paper_main_data_feature n (fun j => clip U (nth (i * d + j) xs 0)), with the
   checked clip of PaperMainGaussianLipschitzClip. The full score
   sum_i y_i <Wclip_i(xs), B> is 2 k U-Lipschitz in the Euclidean distance of
   all N * d coordinates, with no sqrt N loss. When every sample coordinate has
   absolute value at most U, the clipped rows are the head features of the
   sample. N = 0 and U = 0 are covered. No length, rotation, tail or
   concentration assumption is used. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval boolp.
From mathcomp Require Import classical_sets functions reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums MatrixDefinitions
  OperatorDefinitions PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHeadFeature PaperMainGordonLipschitz PaperMainGaussianLipschitzClip
  PaperMainSymmetricBilinear PaperMainMatrixTransport PaperMainDataFeatureMoments
  PaperMainDataFeatureMomentsRow PaperMainDataClippedScore.
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

(* 2. Checkpoint A row estimates for the clip. *)
Theorem paper_main_data_clipped_row_norm U n i xs :
  0 <= U ->
  pmdc_norm (paper_main_symmetric_column n
    (fun j => paper_main_gaussian_clip U (List.nth (i * S n + j)%N xs 0))) <=
  U * sqrt (INR (S n)).
Proof.
move=> HU; apply: (pmdc_row_norm (paper_main_gaussian_clip U) U n i xs).
by move=> z; exact: paper_main_gaussian_clip_bound.
Qed.

Theorem paper_main_data_clipped_row_dist U n i xs ys :
  pmdc_norm (paper_main_symmetric_column n
      (fun j => paper_main_gaussian_clip U (List.nth (i * S n + j)%N xs 0)) -
    paper_main_symmetric_column n
      (fun j => paper_main_gaussian_clip U (List.nth (i * S n + j)%N ys 0)))%R <=
  sqrt (finite_sum (fun j => (List.nth (i * S n + j)%N xs 0 -
    List.nth (i * S n + j)%N ys 0) ^ 2) (List.seq 0 (S n))).
Proof.
apply: (pmdc_row_dist (paper_main_gaussian_clip U) n i xs ys).
exact: paper_main_gaussian_clip_lipschitz.
Qed.

Theorem paper_main_data_clipped_dist_blocks N n (xs ys : list R) :
  finite_sum (fun i => finite_sum (fun j => (List.nth (i * S n + j)%N xs 0 -
    List.nth (i * S n + j)%N ys 0) ^ 2) (List.seq 0 (S n))) (List.seq 0 N) =
  paper_main_gordon_distance (N * S n) xs ys ^ 2.
Proof. exact: pmdc_dist_blocks. Qed.

(* 3. The full score is 2kU-Lipschitz, with no sqrt N loss. *)
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

(* 4. Off the coordinate exception the clipped rows are the head features. *)
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

(* 5. The edge cases N = 0 and U = 0. *)
Corollary paper_main_data_clipped_score_N0 U n (B : 'M[R]_(S n)) (y : nat -> R) xs :
  paper_main_data_clipped_score U n 0 B y xs = 0.
Proof. by []. Qed.

(* At N = 0 the coordinate condition is empty and the identity still holds. *)
Corollary paper_main_data_clipped_score_head_N0 U n (B : 'M[R]_(S n)) (y : nat -> R)
    (x : paper_main_sample 0 (S n)) :
  paper_main_data_clipped_score U n 0 B y (tval x) =
  finite_sum (fun i => y i * paper_main_pairing (paper_main_head_feature x i) B)
    (List.seq 0 0).
Proof.
apply: paper_main_data_clipped_score_head => l Hl; exfalso.
by move: Hl; rewrite mul0n ltn0.
Qed.

Lemma pmdcl_clip_zero z : paper_main_gaussian_clip 0 z = 0.
Proof.
have H := paper_main_gaussian_clip_bound 0 z (Rle_refl 0).
have H1 := Rle_abs (paper_main_gaussian_clip 0 z).
have H2 := Rle_abs (- paper_main_gaussian_clip 0 z).
rewrite Rabs_Ropp in H2; lra.
Qed.

(* At U = 0 every clipped row is 0, so the clipped feature is the data
   feature of the zero row, whatever the list. *)
Corollary paper_main_data_clipped_feature_U0 n i xs :
  paper_main_data_clipped_feature 0 n i xs = paper_main_data_feature n (fun _ => 0).
Proof.
by apply: pmdf_data_feature_ext => j; rewrite pmdcl_clip_zero.
Qed.

(* At U = 0 the coordinate condition says the sample is 0, and the head
   features agree with the clipped ones. *)
Corollary paper_main_data_clipped_feature_head_U0 n N (x : paper_main_sample N (S n)) i :
  (forall l, (l < N * S n)%N -> List.nth l (tval x) 0 = 0) ->
  (i < N)%N ->
  paper_main_data_clipped_feature 0 n i (tval x) = paper_main_head_feature x i.
Proof.
move=> Hx Hi; apply: paper_main_data_clipped_feature_head => // l Hl.
by rewrite (Hx l Hl) Rabs_R0; exact: Rle_refl.
Qed.

(* At U = 0 the clipped score does not depend on the list. *)
Corollary paper_main_data_clipped_score_U0 n N (B : 'M[R]_(S n)) (y : nat -> R) xs ys :
  paper_main_data_clipped_score 0 n N B y xs = paper_main_data_clipped_score 0 n N B y ys.
Proof.
by apply: finite_sum_ext => i _; rewrite !paper_main_data_clipped_feature_U0.
Qed.
