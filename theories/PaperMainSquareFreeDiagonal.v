(* The diagonal of the square-free feature Gram matrix under the Gaussian
   law: an explicit bound on the bad event (eq:R2-diag and eq:diag-limit
   of the paper).
   For a sample of N rows of d coordinates, S_i is the squared norm of row
   i and Q_i the sum of the fourth powers. By paper_main_squarefree_gram_diag
   (PaperMainFeatureGramBlocks), (V V^T)_ii = S_i^2 - Q_i
   (paper_main_squarefree_diag_list).
   - Deterministic step (paper_main_row_diag_bound): suppose
     |S_i - d| < eta d and every coordinate of row i has |x_ia| < U. Then
     Q_i <= U^2 S_i, and
     |(V V^T)_ii / d^2 - 1| < eta (2 + eta) + U^2 (1 + eta) / d.
   - Events on gaussian_product_law (N * d): the bad event is some row with
     eps < |(V V^T)_ii / d^2 - 1|. When
     eta (2 + eta) + U^2 (1 + eta) / d <= eps, it lies inside the union of
     the row events eta d <= |S_i - d| and the coordinate event at U
     (paper_main_squarefree_diag_event_sub).
   - Bound (paper_main_squarefree_diag_bound):
       P(bad) <= N 2 exp (-(eta d)^2 / (4 d + 4 eta d)) + 2 N d exp (- U^2 / 2).
     The row tails come from the weighted-square Chernoff bound
     paper_main_weighted_square_two_sided_tail with row-indicator weights,
     the coordinate tail from paper_main_data_coordinate_tail. Every event
     is measurable. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import ereal measure lebesgue_measure.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity GaussianFiniteSums
  GaussianProbabilityProductDefinitions PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHeadCoefficients PaperMainMatrixDuality PaperMainDataHeadOperator
  PaperMainGaussianUnion PaperMainGaussianGordonTail PaperMainDataSampleTail
  PaperMainGaussianWeightedSquare PaperMainGaussianWeightedSquareLaw
  PaperMainFeatureGramBlocks.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* 1. Row statistics of the list of N * d coordinates. *)
Definition paper_main_row_sq (d i : nat) (xs : list R) : R :=
  finite_sum (fun a => List.nth (i * d + a)%N xs 0 ^ 2) (List.seq 0 d).

Definition paper_main_row_quart (d i : nat) (xs : list R) : R :=
  finite_sum (fun a => List.nth (i * d + a)%N xs 0 ^ 4) (List.seq 0 d).

Lemma paper_main_squarefree_diag_list N d (x : paper_main_sample N d) (i : 'I_N) :
  (paper_main_squarefree_block N d x *m (paper_main_squarefree_block N d x)^T)%R i i =
  paper_main_row_sq d i (tval x) ^ 2 - paper_main_row_quart d i (tval x).
Proof.
rewrite paper_main_squarefree_gram_diag pmh_vec_dot.
rewrite /paper_main_row_sq /paper_main_row_quart !paper_main_finite_sum_public.
rewrite RminusE !RpowE.
by congr (_ ^+ 2 - _)%R; apply: eq_bigr => a _; rewrite /paper_main_point !mxE ?RpowE.
Qed.

(* 2. The deterministic row estimate. *)
Lemma paper_main_row_diag_bound (D S Q eta U eps : R) :
  0 < D -> 0 < eta -> 0 <= S -> 0 <= Q -> Q <= U ^ 2 * S ->
  Rabs (S - D) < eta * D ->
  eta * (2 + eta) + U ^ 2 * (1 + eta) / D <= eps ->
  Rabs ((S ^ 2 - Q) / D ^ 2 - 1) < eps.
Proof.
move=> HD Heta HS HQ HQS HSD Heps.
set r := S / D.
have Hr0 : 0 <= r by apply: Rmult_le_pos => //; apply: Rlt_le; exact: Rinv_0_lt_compat.
have HrD : r * D = S by rewrite /r; field; lra.
have Hr1 : Rabs (r - 1) < eta.
  have [H1 H2] := Rabs_def2 _ _ HSD.
  rewrite -HrD in H1 H2.
  by apply: Rabs_def1; nra.
have Hrl : r < 1 + eta by have := Rle_abs (r - 1); lra.
have Hsq : Rabs (r ^ 2 - 1) < eta * (2 + eta).
  have E : r ^ 2 - 1 = (r - 1) * (r + 1) by ring.
  have Hr1p : 0 <= r + 1 by lra.
  rewrite E Rabs_mult (Rabs_pos_eq _ Hr1p).
  have := Rabs_pos (r - 1); nra.
have HqD : Q / D ^ 2 <= U ^ 2 * (1 + eta) / D.
  have HD2 : 0 < D ^ 2 by nra.
  have E1 : Q / D ^ 2 <= U ^ 2 * S / D ^ 2.
    by apply: Rmult_le_compat_r => //; apply: Rlt_le; exact: Rinv_0_lt_compat.
  have E2 : U ^ 2 * S / D ^ 2 = U ^ 2 * r / D by rewrite /r; field; lra.
  have HU2 := pow2_ge_0 U.
  have E3 : U ^ 2 * r / D <= U ^ 2 * (1 + eta) / D.
    apply: Rmult_le_compat_r; first by apply: Rlt_le; exact: Rinv_0_lt_compat.
    by apply: Rmult_le_compat_l => //; lra.
  lra.
have Hq0 : 0 <= Q / D ^ 2.
  by apply: Rmult_le_pos => //; apply: Rlt_le; apply: Rinv_0_lt_compat; nra.
have E : (S ^ 2 - Q) / D ^ 2 - 1 = (r ^ 2 - 1) - Q / D ^ 2.
  by rewrite /r; field; lra.
rewrite E; apply: Rle_lt_trans (Rabs_triang _ _) _.
rewrite Rabs_Ropp (Rabs_pos_eq _ Hq0); lra.
Qed.

(* 3. Row-indicator weights: the weighted square of row i is S_i - d. *)
Definition paper_main_row_weight (d i : nat) (k : nat) : R :=
  if ((i * d <= k) && (k < i * d + d))%N then 1 else 0.

Lemma pmsd_weight_block d i r a :
  (a < d)%N -> paper_main_row_weight d i (r * d + a) = if Nat.eqb r i then 1 else 0.
Proof.
move=> Ha; rewrite /paper_main_row_weight.
have Hlt : (r * d + a < r * d + d)%N by rewrite ltn_add2l.
case: (ltngtP r i) => [Hri|Hri|<-]; last first.
- by rewrite Nat.eqb_refl leq_addr ltn_add2l Ha.
- have Hne : Nat.eqb r i = false by apply/Nat.eqb_neq => H; move: Hri; rewrite H ltnn.
  rewrite Hne; case: andP => // [[_ H]].
  have H' : (i * d + d <= r * d)%N by rewrite -mulSnr leq_mul2r Hri orbT.
  by have := leq_trans H H'; rewrite ltnNge leq_addr.
- have Hne : Nat.eqb r i = false by apply/Nat.eqb_neq => H; move: Hri; rewrite H ltnn.
  rewrite Hne; case: andP => // [[H _]].
  have H' : (r * d + d <= i * d)%N by rewrite -mulSnr leq_mul2r Hri orbT.
  by have := leq_trans Hlt H'; rewrite ltnNge H.
Qed.

Lemma pmsd_weighted_row N d i (xs : list R) :
  (i < N)%coq_nat ->
  paper_main_weighted_square (N * d) (paper_main_row_weight d i) xs =
  paper_main_row_sq d i xs - INR d.
Proof.
move=> Hi; rewrite /paper_main_weighted_square.
rewrite (pmdo_sum_blocks N d (fun k => paper_main_row_weight d i k *
  (List.nth k xs 0 ^ 2 - 1))).
have E : finite_sum (fun r => finite_sum (fun a => paper_main_row_weight d i (r * d + a) *
    (List.nth (r * d + a)%N xs 0 ^ 2 - 1)) (List.seq 0 d)) (List.seq 0 N) =
  finite_sum (fun r => if Nat.eqb r i then
    finite_sum (fun a => List.nth (i * d + a)%N xs 0 ^ 2 - 1) (List.seq 0 d) else 0)
    (List.seq 0 N).
  apply: finite_sum_ext => r _; case: (Nat.eqb_spec r i) => [->|Hne].
    apply: finite_sum_ext => a /List.in_seq [_ Ha].
    have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
    by rewrite (pmsd_weight_block _ _ _ _ Ha') Nat.eqb_refl Rmult_1_l.
  rewrite -(finite_sum_zero (List.seq 0 d)); apply: finite_sum_ext => a /List.in_seq [_ Ha].
  have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
  rewrite (pmsd_weight_block _ _ _ _ Ha').
  by move/Nat.eqb_neq: Hne => ->; rewrite Rmult_0_l.
rewrite E finite_sum_delta // finite_sum_minus finite_sum_const List.length_seq.
by rewrite /paper_main_row_sq Rmult_1_r.
Qed.

Lemma pmsd_weight_mass N d i :
  (i < N)%coq_nat ->
  finite_sum (fun k => paper_main_row_weight d i k ^ 2) (List.seq 0 (N * d)) = INR d.
Proof.
move=> Hi.
rewrite (pmdo_sum_blocks N d (fun k => paper_main_row_weight d i k ^ 2)).
have E : finite_sum (fun r => finite_sum (fun a => paper_main_row_weight d i (r * d + a) ^ 2)
    (List.seq 0 d)) (List.seq 0 N) =
  finite_sum (fun r => if Nat.eqb r i then INR d else 0) (List.seq 0 N).
  apply: finite_sum_ext => r _; case: (Nat.eqb_spec r i) => [->|Hne].
    have Hc : INR d = finite_sum (fun _ => 1) (List.seq 0 d).
      by rewrite finite_sum_const List.length_seq Rmult_1_r.
    rewrite Hc; apply: finite_sum_ext => a /List.in_seq [_ Ha].
    have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
    by rewrite (pmsd_weight_block _ _ _ _ Ha') Nat.eqb_refl; ring.
  rewrite -(finite_sum_zero (List.seq 0 d)); apply: finite_sum_ext => a /List.in_seq [_ Ha].
  have Ha' : (a < d)%N by apply/ssrnat.ltP; lia.
  rewrite (pmsd_weight_block _ _ _ _ Ha').
  by move/Nat.eqb_neq: Hne => ->; ring.
by rewrite E finite_sum_delta.
Qed.

(* 4. Continuity and measurability. *)
Lemma pmsd_index_lt N d i a :
  (i < N)%coq_nat -> (a < d)%coq_nat -> ((i * d + a)%N < N * d)%coq_nat.
Proof. by move=> Hi Ha; rewrite -!multE -!plusE; nia. Qed.

Lemma pmsd_ge_measurable D (F : list R -> R) c :
  finite_joint_continuous D F ->
  measurable [set x : D.-tuple (measurableTypeR R) | Rle c (F (tval x))].
Proof.
move=> HF.
have -> : [set x : D.-tuple (measurableTypeR R) | Rle c (F (tval x))] =
    [set x | Rle ((fun xs => (-1) * F xs) (tval x)) (- c)].
  by apply/seteqP; split => x /= H; lra.
exact: (paper_main_gaussian_continuous_le_measurable D (fun xs => (-1) * F xs) (- c)
  (finite_joint_continuous_scale D F (-1) HF)).
Qed.

Lemma pmsd_gt_measurable D (F : list R -> R) c :
  finite_joint_continuous D F ->
  measurable [set x : D.-tuple (measurableTypeR R) | Rlt c (F (tval x))].
Proof.
move=> HF.
have -> : [set x : D.-tuple (measurableTypeR R) | Rlt c (F (tval x))] =
    ~` [set x | Rle (F (tval x)) c].
  apply/seteqP; split => x /=; first by move=> H1 H2; lra.
  by move=> H; apply: Rnot_le_lt.
apply: measurableC; exact: paper_main_gaussian_continuous_le_measurable.
Qed.

Lemma pmsd_power_continuous N d i a k :
  (i < N)%coq_nat -> (a < d)%coq_nat ->
  finite_joint_continuous (N * d) (fun xs => List.nth (i * d + a)%N xs 0 ^ k).
Proof.
move=> Hi Ha; elim: k => [|k IH].
  by apply: (finite_joint_continuous_ext _ (fun _ => 1)) => [xs _ //|];
    exact: finite_joint_continuous_constant.
apply: (finite_joint_continuous_ext _ (fun xs => List.nth (i * d + a)%N xs 0 *
  List.nth (i * d + a)%N xs 0 ^ k)) => [xs _ //|].
apply: finite_joint_continuous_mult => //.
exact: finite_joint_continuous_nth (pmsd_index_lt N d i a Hi Ha).
Qed.

Lemma pmsd_row_power_continuous N d i k :
  (i < N)%coq_nat ->
  finite_joint_continuous (N * d)
    (fun xs => finite_sum (fun a => List.nth (i * d + a)%N xs 0 ^ k) (List.seq 0 d)).
Proof.
move=> Hi.
apply: (finite_joint_continuous_sum (N * d) (List.seq 0 d)
  (fun a xs => List.nth (i * d + a)%N xs 0 ^ k)).
move=> a /List.in_seq [_ Ha]; apply: pmsd_power_continuous => //; lia.
Qed.

Lemma pmsd_diag_value_continuous N d i :
  (i < N)%coq_nat ->
  finite_joint_continuous (N * d) (fun xs =>
    Rabs ((paper_main_row_sq d i xs ^ 2 - paper_main_row_quart d i xs) / INR d ^ 2 - 1)).
Proof.
move=> Hi; apply: finite_joint_continuous_abs.
apply: finite_joint_continuous_minus; last exact: finite_joint_continuous_constant.
apply: (finite_joint_continuous_ext _ (fun xs => / INR d ^ 2 *
  (paper_main_row_sq d i xs ^ 2 - paper_main_row_quart d i xs))).
  by move=> xs _; rewrite /Rdiv Rmult_comm.
apply: finite_joint_continuous_scale; apply: finite_joint_continuous_minus.
  apply: (finite_joint_continuous_ext _ (fun xs => paper_main_row_sq d i xs *
    paper_main_row_sq d i xs)); first by move=> xs _; ring.
  by apply: finite_joint_continuous_mult; exact: pmsd_row_power_continuous.
exact: pmsd_row_power_continuous.
Qed.

(* 5. The events. *)
Definition paper_main_squarefree_diag_event N d (eps : R) : set (paper_main_sample N d) :=
  [set x | exists i : 'I_N, Rlt eps (Rabs ((paper_main_squarefree_block N d x *m
    (paper_main_squarefree_block N d x)^T)%R i i / INR d ^ 2 - 1))].

Definition paper_main_row_norm_event N d (eta : R) : set (paper_main_sample N d) :=
  paper_main_finite_event_union (List.seq 0 N)
    (fun i => [set x | Rle (eta * INR d) (Rabs (paper_main_row_sq d i (tval x) - INR d))]).

Lemma pmsd_diag_event_union N d eps :
  paper_main_squarefree_diag_event N d eps =
  paper_main_finite_event_union (List.seq 0 N) (fun i => [set x : paper_main_sample N d |
    Rlt eps (Rabs ((paper_main_row_sq d i (tval x) ^ 2 - paper_main_row_quart d i (tval x)) /
      INR d ^ 2 - 1))]).
Proof.
apply/seteqP; split => x.
- move=> [i H]; apply/paper_main_finite_event_union_member.
  exists i; split; first by apply/List.in_seq; split; [lia | apply/ssrnat.ltP; exact: ltn_ord].
  by rewrite paper_main_squarefree_diag_list in H.
- move/paper_main_finite_event_union_member => [i [/List.in_seq [_ Hi] H]].
  have Hi' : (i < N)%N by apply/ssrnat.ltP; lia.
  by exists (Ordinal Hi'); rewrite paper_main_squarefree_diag_list.
Qed.

Theorem paper_main_squarefree_diag_event_measurable N d eps :
  measurable (paper_main_squarefree_diag_event N d eps).
Proof.
rewrite pmsd_diag_event_union; apply: paper_main_gaussian_union_measurable.
move=> i /List.in_seq [_ Hi].
exact: (pmsd_gt_measurable (N * d) _ eps (pmsd_diag_value_continuous N d i ltac:(lia))).
Qed.

Theorem paper_main_row_norm_event_measurable N d eta :
  measurable (paper_main_row_norm_event N d eta).
Proof.
apply: paper_main_gaussian_union_measurable => i /List.in_seq [_ Hi].
apply: (pmsd_ge_measurable (N * d) (fun xs => Rabs (paper_main_row_sq d i xs - INR d))).
apply: finite_joint_continuous_abs; apply: finite_joint_continuous_minus.
  exact: pmsd_row_power_continuous.
exact: finite_joint_continuous_constant.
Qed.

(* 6. The inclusion and the explicit bound. *)
Theorem paper_main_squarefree_diag_event_sub N d eps eta U :
  (0 < d)%N -> 0 < eta -> 0 <= U ->
  eta * (2 + eta) + U ^ 2 * (1 + eta) / INR d <= eps ->
  paper_main_squarefree_diag_event N d eps `<=`
  paper_main_row_norm_event N d eta `|` paper_main_data_coordinate_event N d U.
Proof.
move=> Hd Heta HU Heps x [i Hi].
case: (pselect (paper_main_row_norm_event N d eta x)) => Hrow; first by left.
case: (pselect (paper_main_data_coordinate_event N d U x)) => Hcoord; first by right.
exfalso.
have HD : 0 < INR d by apply: lt_0_INR; apply/ssrnat.ltP.
have HSD : Rabs (paper_main_row_sq d i (tval x) - INR d) < eta * INR d.
  apply: Rnot_le_lt => H; apply: Hrow; apply/paper_main_finite_event_union_member.
  exists i; split => //; apply/List.in_seq; split; [lia | apply/ssrnat.ltP; exact: ltn_ord].
have Hco : forall a, (a < d)%coq_nat -> Rabs (List.nth (i * d + a)%N (tval x) 0) < U.
  move=> a Ha; apply: Rnot_le_lt => H; apply: Hcoord.
  have Ha' : (a < d)%N by apply/ssrnat.ltP.
  by exists i, (Ordinal Ha'); rewrite pmds_point_entry.
have HS0 : 0 <= paper_main_row_sq d i (tval x).
  by apply: finite_sum_nonneg => a _; exact: pow2_ge_0.
have HQ0 : 0 <= paper_main_row_quart d i (tval x).
  apply: finite_sum_nonneg => a _.
  have -> : forall z : R, z ^ 4 = (z ^ 2) ^ 2 by move=> z; ring.
  exact: pow2_ge_0.
have HQ : paper_main_row_quart d i (tval x) <= U ^ 2 * paper_main_row_sq d i (tval x).
  rewrite /paper_main_row_quart /paper_main_row_sq -finite_sum_scale.
  apply: finite_sum_le => a /List.in_seq [_ Ha].
  set z := List.nth _ _ _.
  have Hz : Rabs z < U by exact: Hco a ltac:(lia).
  have Hz2 : z ^ 2 <= U ^ 2.
    rewrite -(pow2_abs z); apply: pow_incr; split; [exact: Rabs_pos | lra].
  have := pow2_ge_0 z; nra.
have Hb := paper_main_row_diag_bound (INR d) _ _ eta U eps HD Heta HS0 HQ0 HQ HSD Heps.
rewrite paper_main_squarefree_diag_list in Hi; lra.
Qed.

Lemma pmsd_row_tail N d eta i :
  (0 < d)%N -> 0 < eta -> (i < N)%coq_nat ->
  (gaussian_product_law (N * d)
    [set x | Rle (eta * INR d) (Rabs (paper_main_row_sq d i (tval x) - INR d))] <=
    (2 * exp (- (eta * INR d) ^ 2 / (4 * INR d + 4 * (eta * INR d))))%:E)%E.
Proof.
move=> Hd Heta Hi.
have HD : 0 < INR d by apply: lt_0_INR; apply/ssrnat.ltP.
have -> : [set x : (N * d).-tuple (measurableTypeR R) |
    Rle (eta * INR d) (Rabs (paper_main_row_sq d i (tval x) - INR d))] =
  [set x | Rle (eta * INR d)
    (Rabs (paper_main_weighted_square (N * d) (paper_main_row_weight d i) (tval x)))].
  by apply/seteqP; split => x /=; rewrite pmsd_weighted_row.
have Hw : forall k, (k < N * d)%coq_nat -> Rabs (paper_main_row_weight d i k) <= 1.
  move=> k _; rewrite /paper_main_row_weight.
  by case: ifP => _; [rewrite Rabs_R1 | rewrite Rabs_R0]; lra.
have Hu : 0 < eta * INR d by apply: Rmult_lt_0_compat.
have Hden : 0 < finite_sum (fun k => paper_main_row_weight d i k ^ 2) (List.seq 0 (N * d)) +
    1 * (eta * INR d).
  by rewrite pmsd_weight_mass //; lra.
have H := paper_main_weighted_square_two_sided_tail (N * d) (paper_main_row_weight d i) 1
  (eta * INR d) Hw Rle_0_1 Hu Hden.
by rewrite pmsd_weight_mass // Rmult_1_r in H.
Qed.

Theorem paper_main_squarefree_diag_bound N d eps eta U :
  (0 < d)%N -> 0 < eta -> 0 < U ->
  eta * (2 + eta) + U ^ 2 * (1 + eta) / INR d <= eps ->
  measurable (paper_main_squarefree_diag_event N d eps) /\
  (paper_main_probability N d (paper_main_squarefree_diag_event N d eps) <=
    (INR N * (2 * exp (- (eta * INR d) ^ 2 / (4 * INR d + 4 * (eta * INR d)))) +
     2 * INR N * INR d * exp (- U ^ 2 / 2))%:E)%E.
Proof.
move=> Hd Heta HU Heps.
split; first exact: paper_main_squarefree_diag_event_measurable.
have Hsub := paper_main_squarefree_diag_event_sub N d eps eta U Hd Heta (Rlt_le _ _ HU) Heps.
have Hrow := paper_main_row_norm_event_measurable N d eta.
have [Hcm Hcb] := paper_main_data_coordinate_tail N d U HU.
have Hbad := paper_main_squarefree_diag_event_measurable N d eps.
rewrite /paper_main_probability in Hcb *.
have HM : (gaussian_product_law (N * d) (paper_main_squarefree_diag_event N d eps) <=
    gaussian_product_law (N * d)
      (paper_main_row_norm_event N d eta `|` paper_main_data_coordinate_event N d U))%E.
  by apply: le_measure; rewrite ?inE; [exact: Hbad | exact: measurableU | exact: Hsub].
apply: (le_trans HM); apply: (le_trans (measureU2 _ Hrow Hcm)).
rewrite EFinD; apply: leeD; last exact: Hcb.
have HU' := paper_main_gaussian_union_bound (N * d) (List.seq 0 N)
  (fun i => [set x : (N * d).-tuple (measurableTypeR R) |
    Rle (eta * INR d) (Rabs (paper_main_row_sq d i (tval x) - INR d))])
  (2 * exp (- (eta * INR d) ^ 2 / (4 * INR d + 4 * (eta * INR d)))).
rewrite List.length_seq in HU'; apply: HU'.
- move=> i /List.in_seq [_ Hi].
  apply: (pmsd_ge_measurable (N * d) (fun xs => Rabs (paper_main_row_sq d i xs - INR d))).
  apply: finite_joint_continuous_abs; apply: finite_joint_continuous_minus.
    exact: pmsd_row_power_continuous.
  exact: finite_joint_continuous_constant.
- by move=> i /List.in_seq [_ Hi]; apply: pmsd_row_tail => //; lia.
Qed.
