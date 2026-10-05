(* Positive support in the spread and the tiny tail cases. Deterministic.

   Family W : nat -> 'M[R]_d on the indices seq 0 n. The score of a dual
   vector y at S is sum_(i < n) y_i <W_i, S> (paper_main_support_score),
   written as paper_main_public_soft_minimax writes its scores. A unit y
   splits along a head J into the head part and the tail part. r is the tail
   norm and t is the normalized tail vector paper_main_tail_list_vector of
   PaperMainHeadTailDecompositionLog.
   - paper_main_support_spread: if S annihilates the head, the score of y is
     r times the score of t (paper_main_support_score_tail). So a positive
     score for t gives a positive score for y.
   - paper_main_support_tiny: assume r <= eps <= 1/2, a head Gram bound
     mu |c|^2 <= |sum c_i W_i|_F^2 for c supported on J, a full bound
     |sum c_i W_i|_F <= A |c|, and some S0 with a I <= S0 <= b I that
     annihilates the head. Then |sum u_i W_i|_F >= sqrt mu / 2 and
     |sum v_i W_i|_F <= A eps for the head part u and the tail part v of y.
     If moreover 0 < delta < a and A eps (b + delta) sqrt d < delta sqrt mu / 2,
     the perturbation lemma paper_main_support_positive
     (PaperMainHeadTailSupport) gives some S with
     (a - delta) I <= S <= (b + delta) I at which y has a positive score. *)
From Stdlib Require Import Reals List Lia Lra Psatz PeanoNat Permutation.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From EllipsoidFitting Require Import Definitions Peeling FiniteSets HeadTail SoftDefinitions
  GaussianCovarianceSums PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature
  PaperMainGeometryHeadCorrection PaperMainMatrixDuality PaperMainHeadTailDecompositionLog
  PaperMainHeadTailSupport.
Import GRing.Theory Num.Theory Order.TTheory.
Import ListNotations.
Open Scope R_scope.

Section Split.
Variables (d n : nat) (W : nat -> 'M[R]_d).

(* 1. Scores and combinations. *)
Definition paper_main_support_score (y : nat -> R) (S : 'M[R]_d) : R :=
  finite_sum (fun i => y i * paper_main_pairing (W i) S) (List.seq 0 n).

Definition paper_main_support_combination (c : nat -> R) : 'M[R]_d :=
  (\sum_(i < n) c i *: W i)%R.

Lemma paper_main_support_score_pairing y S :
  paper_main_support_score y S = paper_main_pairing (paper_main_support_combination y) S.
Proof.
rewrite /paper_main_support_score /paper_main_support_combination pmh_pairing_suml.
by rewrite paper_main_finite_sum_public.
Qed.

Lemma pmhss_combinationD c1 c2 :
  paper_main_support_combination (fun i => c1 i + c2 i) =
  (paper_main_support_combination c1 + paper_main_support_combination c2)%R.
Proof.
rewrite /paper_main_support_combination -big_split /=.
by apply: eq_bigr => i _; rewrite scalerDl.
Qed.

Lemma pmhss_combination_symmetric c :
  (forall i, (i < n)%nat -> paper_main_symmetric (W i)) ->
  paper_main_symmetric (paper_main_support_combination c).
Proof.
move=> HW a b; rewrite /paper_main_support_combination !summxE.
by apply: eq_bigr => i _; rewrite !mxE (HW i) //.
Qed.

(* 2. The spread case. *)
Lemma pmhss_head_filter_in J i :
  In i (filter (fun i => negb (pmhtl_out J i)) (List.seq 0 n)) -> In i J.
Proof.
move=> /filter_In [_ H]; move: H; rewrite /pmhtl_out.
by case: (in_dec Nat.eq_dec i J).
Qed.

Theorem paper_main_support_score_tail y J S :
  (forall i, In i J -> paper_main_pairing (W i) S = 0) ->
  0 < euclidean_norm y (tail_indices n J) ->
  paper_main_support_score y S =
  euclidean_norm y (tail_indices n J) *
    paper_main_support_score (paper_main_tail_list_vector y n J) S.
Proof.
move=> HJ Hr; rewrite /paper_main_support_score.
rewrite (pmhtl_split (fun i => y i * paper_main_pairing (W i) S) n J).
rewrite (pmhtl_split (fun i => paper_main_tail_list_vector y n J i *
  paper_main_pairing (W i) S) n J).
have H0 : forall w : nat -> R,
    finite_sum (fun i => w i * paper_main_pairing (W i) S)
      (filter (fun i => negb (pmhtl_out J i)) (List.seq 0 n)) = 0.
  move=> w; rewrite -(finite_sum_zero (filter (fun i => negb (pmhtl_out J i)) (List.seq 0 n))).
  apply: finite_sum_ext => i Hi.
  by rewrite (HJ i (pmhss_head_filter_in J i Hi)) Rmult_0_r.
rewrite !H0 !Rplus_0_r -finite_sum_scale.
apply: finite_sum_ext => i Hi.
rewrite /paper_main_tail_list_vector.
case: (in_dec Nat.eq_dec i (tail_indices n J)) => [_|//].
by field; lra.
Qed.

Theorem paper_main_support_spread y J S :
  (forall i, In i J -> paper_main_pairing (W i) S = 0) ->
  0 < euclidean_norm y (tail_indices n J) ->
  0 < paper_main_support_score (paper_main_tail_list_vector y n J) S ->
  0 < paper_main_support_score y S.
Proof.
move=> HJ Hr Ht; rewrite (paper_main_support_score_tail y J S HJ Hr).
exact: Rmult_lt_0_compat.
Qed.

(* 3. Head and tail parts of y. *)
Definition paper_main_head_part (y : nat -> R) (J : list nat) : nat -> R :=
  fun i => if in_dec Nat.eq_dec i J then y i else 0.

Definition paper_main_tail_part (y : nat -> R) (J : list nat) : nat -> R :=
  fun i => if in_dec Nat.eq_dec i J then 0 else y i.

Lemma pmhss_parts_sum y J i :
  paper_main_head_part y J i + paper_main_tail_part y J i = y i.
Proof.
rewrite /paper_main_head_part /paper_main_tail_part.
by case: (in_dec Nat.eq_dec i J) => [HiJ|HiJ] /=; ring.
Qed.

Lemma pmhss_tail_part_mass y J :
  squared_norm (paper_main_tail_part y J) (List.seq 0 n) = squared_norm y (tail_indices n J).
Proof.
rewrite /squared_norm (pmhtl_split (fun i => paper_main_tail_part y J i ^ 2) n J).
have H0 : finite_sum (fun i => paper_main_tail_part y J i ^ 2)
    (filter (fun i => negb (pmhtl_out J i)) (List.seq 0 n)) = 0.
  rewrite -(finite_sum_zero (filter (fun i => negb (pmhtl_out J i)) (List.seq 0 n))).
  apply: finite_sum_ext => i Hi.
  rewrite /paper_main_tail_part.
  case: (in_dec Nat.eq_dec i J) => [HiJ|HiJ] /=; first by ring.
  by have := pmhss_head_filter_in J i Hi.
rewrite H0 Rplus_0_r; apply: finite_sum_ext => i Hi.
rewrite /paper_main_tail_part; case: (in_dec Nat.eq_dec i J) => [HiJ|HiJ] //=.
by have /outside_in [_ H] := Hi.
Qed.

Lemma pmhss_head_part_mass y J :
  NoDup J -> incl J (List.seq 0 n) ->
  squared_norm (paper_main_head_part y J) (List.seq 0 n) = squared_norm y J.
Proof.
move=> HJ Hincl.
rewrite /squared_norm (pmhtl_split (fun i => paper_main_head_part y J i ^ 2) n J).
have H0 : finite_sum (fun i => paper_main_head_part y J i ^ 2) (tail_indices n J) = 0.
  rewrite -(finite_sum_zero (tail_indices n J)).
  apply: finite_sum_ext => i Hi.
  rewrite /paper_main_head_part; case: (in_dec Nat.eq_dec i J) => [HiJ|HiJ] /=; last by ring.
  by have /outside_in [_ H] := Hi.
rewrite H0 Rplus_0_l.
have E : finite_sum (fun i => paper_main_head_part y J i ^ 2)
    (filter (fun i => negb (pmhtl_out J i)) (List.seq 0 n)) =
    finite_sum (fun i => y i ^ 2) (filter (fun i => negb (pmhtl_out J i)) (List.seq 0 n)).
  apply: finite_sum_ext => i Hi.
  rewrite /paper_main_head_part; case: (in_dec Nat.eq_dec i J) => [HiJ|HiJ] //=.
  by have := pmhss_head_filter_in J i Hi.
rewrite E -!pmhtl_energy_finite_sum.
exact: energy_permutation (pmhtl_head_permutation n J HJ Hincl).
Qed.

Lemma pmhss_head_pairing0 y J S0 :
  (forall i, In i J -> paper_main_pairing (W i) S0 = 0) ->
  paper_main_pairing (paper_main_support_combination (paper_main_head_part y J)) S0 = 0.
Proof.
move=> HJ; rewrite -paper_main_support_score_pairing /paper_main_support_score.
rewrite -(finite_sum_zero (List.seq 0 n)); apply: finite_sum_ext => i _.
rewrite /paper_main_head_part; case: (in_dec Nat.eq_dec i J) => [HiJ|HiJ] /=.
  by rewrite (HJ i HiJ) Rmult_0_r.
by rewrite Rmult_0_l.
Qed.

(* 4. The tiny case. *)
Theorem paper_main_support_tiny (y : nat -> R) (J : list nat) (S0 : 'M[R]_d)
    (a b delta mu A eps : R) :
  (forall i, (i < n)%nat -> paper_main_symmetric (W i)) ->
  euclidean_norm y (List.seq 0 n) = 1 -> NoDup J -> incl J (List.seq 0 n) ->
  euclidean_norm y (tail_indices n J) <= eps -> eps <= 1 / 2 -> 0 < mu ->
  (forall c : nat -> R, (forall i, ~ In i J -> c i = 0) ->
    mu * squared_norm c (List.seq 0 n) <=
      paper_main_frobenius (paper_main_support_combination c) ^ 2) ->
  (forall c : nat -> R,
    paper_main_frobenius (paper_main_support_combination c) <=
      A * euclidean_norm c (List.seq 0 n)) ->
  0 < delta -> delta < a ->
  paper_main_loewner_le (a *: 1%:M)%R S0 -> paper_main_loewner_le S0 (b *: 1%:M)%R ->
  (forall i, In i J -> paper_main_pairing (W i) S0 = 0) ->
  A * eps * (b + delta) * sqrt (INR d) < delta * (sqrt mu / 2) ->
  exists S : 'M[R]_d,
    paper_main_loewner_le ((a - delta) *: 1%:M)%R S /\
    paper_main_loewner_le S ((b + delta) *: 1%:M)%R /\
    0 < paper_main_support_score y S.
Proof.
move=> HW Hy HJ Hincl Hr Heps Hmu HG HA Hd0 Hda Hlo Hup HS0 Hcond.
set u := paper_main_head_part y J.
set v := paper_main_tail_part y J.
(* The head has mass 1 - r^2 >= 3/4. *)
have Hsplit := paper_main_head_tail_mass_split y n J HJ Hincl.
have Hy2 := pmhtl_unit y _ Hy.
have Hu2 : squared_norm u (List.seq 0 n) = squared_norm y J by exact: pmhss_head_part_mass.
have Hv2 : squared_norm v (List.seq 0 n) = squared_norm y (tail_indices n J).
  exact: pmhss_tail_part_mass.
have Ht0 : 0 <= squared_norm y (tail_indices n J).
  by apply: finite_sum_nonneg => i _; exact: pow2_ge_0.
have Hrsq : squared_norm y (tail_indices n J) = euclidean_norm y (tail_indices n J) ^ 2.
  by rewrite /euclidean_norm pow2_sqrt.
have Hr0 : 0 <= euclidean_norm y (tail_indices n J) by exact: sqrt_pos.
have Hu34 : 3 / 4 <= squared_norm u (List.seq 0 n).
  rewrite Hu2; nra.
(* |sum u_i W_i|_F >= sqrt mu / 2 and |sum v_i W_i|_F <= A eps. *)
have Hu0 : forall i, ~ In i J -> u i = 0.
  by move=> i Hi; rewrite /u /paper_main_head_part; case: (in_dec Nat.eq_dec i J).
have HMu : sqrt mu / 2 <= paper_main_frobenius (paper_main_support_combination u).
  have H := HG u Hu0.
  have HF0 : 0 <= paper_main_frobenius (paper_main_support_combination u).
    by apply/RleP; exact: pmh_frobenius_ge0.
  have Hsm := sqrt_pos mu.
  have Hsq : sqrt mu * sqrt mu = mu by exact: sqrt_sqrt (Rlt_le _ _ Hmu).
  set F := paper_main_frobenius _ in H HF0 *.
  nra.
have HA0 : 0 <= A.
  have H := HA y; rewrite Hy Rmult_1_r in H.
  apply: Rle_trans H; apply/RleP; exact: pmh_frobenius_ge0.
have HMv : paper_main_frobenius (paper_main_support_combination v) <= A * eps.
  apply: Rle_trans (HA v) _; apply: Rmult_le_compat_l => //.
  have -> : euclidean_norm v (List.seq 0 n) = euclidean_norm y (tail_indices n J).
    by rewrite /euclidean_norm Hv2.
  exact: Hr.
(* The perturbation lemma paper_main_support_positive. *)
have HMus := pmhss_combination_symmetric u HW.
have H0 : paper_main_pairing (paper_main_support_combination u) S0 = 0.
  exact: pmhss_head_pairing0.
have Hs : Num.sqrt (d%:R : R) = sqrt (INR d) by rewrite RsqrtE INRE.
have Hh : 0 < sqrt mu / 2 by apply: Rdiv_lt_0_compat; [exact: sqrt_lt_R0 | lra].
have Hc' : ((A * eps) * (b + delta) * Num.sqrt d%:R < delta * (sqrt mu / 2))%R.
  by rewrite Hs; apply/RltP; exact: Hcond.
have [S [B1 [B2 B3]]] := paper_main_support_positive d S0
  (paper_main_support_combination u) (paper_main_support_combination v)
  a b delta (sqrt mu / 2) (A * eps) HMus (introT RltP Hd0) (introT RltP Hda) Hlo Hup H0
  (introT RltP Hh) (introT RleP HMu) (introT RleP HMv) Hc'.
exists S; split => //; split => //.
have Ecomb : paper_main_support_combination y =
    (paper_main_support_combination u + paper_main_support_combination v)%R.
  rewrite -pmhss_combinationD /paper_main_support_combination.
  by apply: eq_bigr => i _; rewrite pmhss_parts_sum.
rewrite paper_main_support_score_pairing Ecomb.
exact/RltP.
Qed.

End Split.
