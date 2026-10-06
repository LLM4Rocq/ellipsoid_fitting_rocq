From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Soft.Definitions Matrix.Definitions
  Matrix.OperatorDefinitions Goe.Definitions Joint.Definitions
  Chaos.SecondOrderDefinitions Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Soft.MatrixDefinitions
  Soft.MinimaxDerivativeDefinitions Soft.LowerThirdDefinitions
  Soft.BlockScoreBounds Soft.LowerDerivativeBounds Gibbs.ThirdDerivativeBounds
  Matrix.OperatorNorm Soft.Extrema Goe.MatrixBasis Joint.ObservableGrowth
  Matrix.BlockInjection Matrix.BlockBasis Row.ArrayDefinitions
  Row.ObservableDefinitions Row.DecoderRegularity Row.ObservableBounds
  Row.ObservableContinuity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Regularity of the row observables gaussian_row_velocity and
   gaussian_row_remainder for arbitrary finite score data y and B: both are
   jointly continuous and bounded by polynomials of degree 2 in the
   coordinates (multirow_row_observables_regular). Row.ObservableBounds
   proves these bounds when each y z is a unit vector and the operator
   norms of the B s are at most k; this module drops both hypotheses.

   The score lower_block_scores y B z s U is at most
   sqrt (n + 1) * (sum_i |y z i|) * |B s|_op * |U| in absolute value
   (multirow_block_score_bound_general), so the finite families Y and S
   give the uniform constant
   K = sqrt (n + 1) * (sum_{z in Y} sum_i |y z i|) * (sum_{s in S} |B s|_op)
   (multirow_block_score_bound_uniform). With K, the generic lemmas
   lower_first_uniform_bound (Soft.LowerDerivativeBounds) and lower_third_uniform_bound
   (Gibbs.ThirdDerivativeBounds) bound the first and third derivatives, and the
   argument of Row.ObservableBounds gives the growth in the row pair and the
   polynomial bounds. The continuity comes from Row.ObservableContinuity,
   which needs no norm hypothesis. *)

Local Ltac mfs_norm_nonneg := apply/RleP; apply normr_ge0.

(* Finite sums: termwise comparison, extensionality and scaling. *)
Lemma multirow_finite_sum_le (f g : nat -> R) (I : list nat) :
  (forall i, In i I -> f i <= g i) -> finite_sum f I <= finite_sum g I.
Proof.
  intros H; induction I as [|i I IH]; simpl; [lra|].
  apply Rplus_le_compat; [apply H; left; reflexivity|].
  apply IH; intros j Hj; apply H; right; exact Hj.
Qed.

Lemma multirow_finite_sum_ext (f g : nat -> R) (I : list nat) :
  (forall i, In i I -> f i = g i) -> finite_sum f I = finite_sum g I.
Proof.
  intros H; induction I as [|i I IH]; simpl; [reflexivity|].
  rewrite (H i (List.in_eq i I)) (IH (fun j Hj => H j (List.in_cons i j I Hj))); reflexivity.
Qed.

Lemma multirow_finite_sum_scale (c : R) (f : nat -> R) (I : list nat) :
  finite_sum (fun i => c * f i) I = c * finite_sum f I.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma multirow_finite_sum_scale_r (c : R) (f : nat -> R) (I : list nat) :
  finite_sum (fun i => f i * c) I = finite_sum f I * c.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

(* The score of one pair (z, s) in the direction U, for arbitrary y and B. *)
Lemma multirow_block_score_bound_general n m (y : nat -> nat -> R) (B : nat -> matrix n)
    z s (U : block_array n m) :
  Rabs (lower_block_scores n m y B z s U) <=
    sqrt (INR (Datatypes.S n)) *
      finite_sum (fun i => Rabs (y z i)) (List.seq 0 (Datatypes.S m)) *
      matrix_operator_norm n (B s) * (`|U|)%R.
Proof.
  unfold lower_block_scores, soft_matrix_scores.
  eapply Rle_trans; [apply lower_finite_sum_abs|].
  set (c := sqrt (INR (Datatypes.S n)) * matrix_operator_norm n (B s) * (`|U|)%R).
  replace (sqrt (INR (Datatypes.S n)) *
      finite_sum (fun i => Rabs (y z i)) (List.seq 0 (Datatypes.S m)) *
      matrix_operator_norm n (B s) * (`|U|)%R)
    with (finite_sum (fun i => Rabs (y z i)) (List.seq 0 (Datatypes.S m)) * c)
    by (unfold c; ring).
  rewrite <- multirow_finite_sum_scale_r.
  apply multirow_finite_sum_le; intros i _.
  rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos|].
  unfold c.
  eapply Rle_trans; [apply trace_pair_operator_frobenius_bound|].
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos; [apply sqrt_pos|apply matrix_operator_norm_nonnegative].
  - apply lower_tuple_entry_norm_bound.
Qed.

(* A uniform constant over the finite families Y and S. *)
Lemma multirow_block_score_bound_uniform n m (y : nat -> nat -> R) (B : nat -> matrix n)
    (Y S : list nat) :
  exists K : R, 0 <= K /\
    forall z s (U : block_array n m), In z Y -> In s S ->
      Rabs (lower_block_scores n m y B z s U) <= K * (`|U|)%R.
Proof.
  set (SY := finite_sum (fun z => finite_sum (fun i => Rabs (y z i)) (List.seq 0 (Datatypes.S m))) Y).
  set (SB := finite_sum (fun s => matrix_operator_norm n (B s)) S).
  assert (HY0 : 0 <= SY).
  { apply finite_sum_nonnegative; intros z _; apply finite_sum_nonnegative; intros i _; apply Rabs_pos. }
  assert (HB0 : 0 <= SB).
  { apply finite_sum_nonnegative; intros s _; apply matrix_operator_norm_nonnegative. }
  exists (sqrt (INR (Datatypes.S n)) * SY * SB); split.
  { apply Rmult_le_pos; [apply Rmult_le_pos; [apply sqrt_pos|exact HY0]|exact HB0]. }
  intros z s U Hz Hs.
  eapply Rle_trans; [apply multirow_block_score_bound_general|].
  assert (Hz' : finite_sum (fun i => Rabs (y z i)) (List.seq 0 (Datatypes.S m)) <= SY).
  { unfold SY.
    apply (finite_sum_member (fun z => finite_sum (fun i => Rabs (y z i)) (List.seq 0 (Datatypes.S m))) Y z);
      [|exact Hz].
    intros z' _; apply finite_sum_nonnegative; intros i _; apply Rabs_pos. }
  assert (Hs' : matrix_operator_norm n (B s) <= SB).
  { unfold SB.
    apply (finite_sum_member (fun s => matrix_operator_norm n (B s)) S s);
      [intros s' _; apply matrix_operator_norm_nonnegative|exact Hs]. }
  assert (Hz0 : 0 <= finite_sum (fun i => Rabs (y z i)) (List.seq 0 (Datatypes.S m)))
    by (apply finite_sum_nonnegative; intros i _; apply Rabs_pos).
  assert (HU : 0 <= (`|U|)%R) by mfs_norm_nonneg.
  apply Rmult_le_compat_r; [exact HU|].
  apply Rmult_le_compat.
  - apply Rmult_le_pos; [apply sqrt_pos|exact Hz0].
  - apply matrix_operator_norm_nonnegative.
  - apply Rmult_le_compat_l; [apply sqrt_pos|exact Hz'].
  - exact Hs'.
Qed.

(* The first and third derivatives of Phi in any directions, with the
   general constant. *)
Lemma multirow_lower_block_first_bound_general n m beta gamma y B Y S K
    (A U : block_array n m) :
  Y <> [] -> S <> [] ->
  (forall z s (P : block_array n m), In z Y -> In s S ->
    Rabs (lower_block_scores n m y B z s P) <= K * (`|P|)%R) ->
  Rabs (lower_block_first n m beta gamma y B Y S A U) <= K * (`|U|)%R.
Proof.
  intros HY HS HK; apply lower_first_uniform_bound; try assumption.
  intros z s Hz Hs; apply HK; assumption.
Qed.

Lemma multirow_lower_block_third_bound_general n m beta gamma y B Y S K
    (A U V W : block_array n m) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= K ->
  (forall z s (P : block_array n m), In z Y -> In s S ->
    Rabs (lower_block_scores n m y B z s P) <= K * (`|P|)%R) ->
  Rabs (lower_block_third n m beta gamma y B Y S A U V W) <=
    8 * K ^ 3 * (beta + gamma) ^ 2 * (`|U|)%R * (`|V|)%R * (`|W|)%R.
Proof.
  intros Hb Hg HY HS HK0 HK; apply lower_third_uniform_bound; try assumption.
  intros z s Hz Hs P; apply HK; assumption.
Qed.

(* Injected into row i: the shape of block_injected_uniform_bounds of
   Row.ObservableBounds, without the unit-vector and norm hypotheses. *)
Lemma multirow_block_injected_uniform_bounds n m beta gamma y B Y S i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] ->
  exists L1 L3 : R, 0<=L1 /\ 0<=L3 /\ forall A U V W,
    Rabs (lower_block_first n m beta gamma y B Y S A (block_inject n m i U)) <= L1*(`|U|)%R /\
    Rabs (lower_block_third n m beta gamma y B Y S A
      (block_inject n m i U) (block_inject n m i V) (block_inject n m i W)) <=
      L3*(`|U|)%R*(`|V|)%R*(`|W|)%R.
Proof.
  intros Hb Hg HY HS.
  destruct (multirow_block_score_bound_uniform n m y B Y S) as [K [HK HKs]].
  destruct (proj2 (block_inject_linear n m i)) as [L [HL Hnorm]].
  set (K3 := 8*K^3*(beta+gamma)^2).
  assert (H3 : 0<=K3).
  { unfold K3; apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow_le; exact HK]|apply pow2_ge_0]. }
  exists (K*L), (K3*L^3); split; [apply Rmult_le_pos; lra|].
  split; [apply Rmult_le_pos; [exact H3|apply pow_le; lra]|].
  intros A U V W; split.
  - eapply Rle_trans;
      [apply (multirow_lower_block_first_bound_general n m beta gamma y B Y S K); assumption|].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact HK|apply Hnorm].
  - eapply Rle_trans;
      [apply (multirow_lower_block_third_bound_general n m beta gamma y B Y S K); assumption|].
    change (K3*(`|block_inject n m i U|)%R*(`|block_inject n m i V|)%R*
      (`|block_inject n m i W|)%R<=K3*L^3*(`|U|)%R*(`|V|)%R*(`|W|)%R).
    replace (K3*L^3*(`|U|)%R*(`|V|)%R*(`|W|)%R) with
      (K3*(L*(`|U|)%R)*(L*(`|V|)%R)*(L*(`|W|)%R)) by ring.
    apply Rmult_le_compat; try mfs_norm_nonneg.
    + apply Rmult_le_pos; [apply Rmult_le_pos; [exact H3|mfs_norm_nonneg]|mfs_norm_nonneg].
    + apply Rmult_le_compat; try mfs_norm_nonneg.
      * apply Rmult_le_pos; [exact H3|mfs_norm_nonneg].
      * apply Rmult_le_compat_l; [exact H3|apply Hnorm].
      * apply Hnorm.
    + apply Hnorm.
Qed.

(* Growth in the row pair, as row_observables_uniform_pair_growth. *)
Theorem multirow_row_observables_uniform_pair_growth n m beta gamma y B Y S t i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] ->
  exists CV CR : R, 0<=CV /\ 0<=CR /\
  forall (A : block_array n m)
    (q : euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))),
    Rabs (lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (joint_quadratic_input n (fst q))) / (2*sqrt t) -
      lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (goe_matrix n (snd q))) / (2*sqrt (1-t))) <= CV*(1+(`|q|)%R)^2 /\
    Rabs (chaos_contraction n (fun U V W => lower_block_third n m beta gamma y B Y S A
      (block_inject n m i U) (block_inject n m i V) (block_inject n m i W)) (fst q)) <=
      CR*(1+(`|q|)%R)^2.
Proof.
  intros Hb Hg HY HS.
  destruct (multirow_block_injected_uniform_bounds n m beta gamma y B Y S i Hb Hg HY HS)
    as [L1 [L3 [H1 [H3 HC]]]].
  set (KW := INR (Datatypes.S n)^2 * Rabs (/sqrt (INR (Datatypes.S n)))).
  set (KG := goe_scale n * INR (Datatypes.S (goe_vector_index n))).
  set (KR := /2 * INR (Datatypes.S n)^2 * L3 * (2*INR (Datatypes.S n)^2)^3).
  assert (HW : 0<=KW) by (unfold KW; apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos]).
  assert (HG : 0<=KG) by (unfold KG; apply Rmult_le_pos; [pose proof (goe_scale_positive n); lra|apply pos_INR]).
  assert (HR : 0<=KR).
  { unfold KR; apply Rmult_le_pos.
    - apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|exact H3].
    - apply pow_le; apply Rmult_le_pos; [lra|apply pow2_ge_0]. }
  exists (Rabs (/(2*sqrt t))*L1*KW+Rabs (/(2*sqrt (1-t)))*L1*KG), KR.
  split.
  { apply Rplus_le_le_0_compat; apply Rmult_le_pos;
      try (apply Rmult_le_pos; [apply Rabs_pos|exact H1]); assumption. }
  split; [exact HR|]; intros A q.
  assert (HX : (`|fst q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_fst).
  assert (HZ : (`|snd q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_snd).
  assert (HN : 0<=(`|q|)%R) by mfs_norm_nonneg.
  assert (HNX : 0<=(`|fst q|)%R) by mfs_norm_nonneg.
  assert (HP : Rabs (lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (joint_quadratic_input n (fst q))))
    <= (L1*KW)*(1+(`|q|)%R)^2).
  { eapply Rle_trans;
      [apply (proj1 (HC A (joint_quadratic_input n (fst q)) (matrix_zero n) (matrix_zero n)))|].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact H1|].
    eapply Rle_trans; [apply joint_quadratic_input_norm|].
    apply Rmult_le_compat_l; [exact HW|nra]. }
  assert (HQ : Rabs (lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (goe_matrix n (snd q))))
    <= (L1*KG)*(1+(`|q|)%R)^2).
  { eapply Rle_trans;
      [apply (proj1 (HC A (goe_matrix n (snd q)) (matrix_zero n) (matrix_zero n)))|].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact H1|].
    eapply Rle_trans; [apply goe_matrix_norm_bound|].
    change (KG*(`|snd q|)%R <= KG*(1+(`|q|)%R)^2).
    apply Rmult_le_compat_l; [exact HG|nra]. }
  split.
  - eapply Rle_trans; [apply Rabs_triang|].
    unfold Rdiv; rewrite Rabs_Ropp !Rabs_mult.
    replace ((Rabs (/(2*sqrt t))*L1*KW+Rabs (/(2*sqrt (1-t)))*L1*KG)*(1+(`|q|)%R)^2) with
      (Rabs (/(2*sqrt t))*((L1*KW)*(1+(`|q|)%R)^2)+
       Rabs (/(2*sqrt (1-t)))*((L1*KG)*(1+(`|q|)%R)^2)) by ring.
    rewrite (Rmult_comm _ (Rabs (/(2*sqrt t)))) (Rmult_comm _ (Rabs (/(2*sqrt (1-t))))).
    apply Rplus_le_compat; apply Rmult_le_compat_l; try apply Rabs_pos; assumption.
  - eapply Rle_trans;
      [apply row_chaos_contraction_norm_bound; [exact H3|intros; apply (proj2 (HC A _ _ _))]|].
    change (KR*(1+(`|fst q|)%R)^2<=KR*(1+(`|q|)%R)^2).
    apply Rmult_le_compat_l; [exact HR|nra].
Qed.

(* Degree-2 polynomial bounds in the coordinates, as
   gaussian_row_observables_polynomial_bounds. *)
Theorem multirow_row_observables_polynomial_bounds n m beta gamma y B Y S t i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> (i<=m)%coq_nat ->
  exists CV CR : R,
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat CV 2
      (gaussian_row_velocity n m beta gamma y B Y S t i) /\
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat CR 2
      (gaussian_row_remainder n m beta gamma y B Y S t i).
Proof.
  intros Hb Hg HY HS Hi.
  destruct (multirow_row_observables_uniform_pair_growth n m beta gamma y B Y S t i Hb Hg HY HS)
    as [CV [CR [HV [HR HC]]]].
  exists CV, CR; split; split; try assumption; intros xs HL;
    destruct (HC (gaussian_row_array n m t xs) (gaussian_row_pair n i xs)) as [HVB HRB].
  - eapply Rle_trans; [exact HVB|apply Rmult_le_compat_l; [exact HV|apply (gaussian_row_pair_squared_weight n m i xs Hi HL)]].
  - eapply Rle_trans; [exact HRB|apply Rmult_le_compat_l; [exact HR|apply (gaussian_row_pair_squared_weight n m i xs Hi HL)]].
Qed.

(* Regularity of both observables: continuity from Row.ObservableContinuity,
   which needs no norm hypothesis, and the bounds above. *)
Theorem multirow_row_observables_regular n m beta gamma y B Y S t i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> (i<=m)%coq_nat ->
  finite_joint_continuous (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_row_velocity n m beta gamma y B Y S t i) /\
  finite_joint_continuous (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_row_remainder n m beta gamma y B Y S t i) /\
  exists CV CR : R,
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat CV 2
      (gaussian_row_velocity n m beta gamma y B Y S t i) /\
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat CR 2
      (gaussian_row_remainder n m beta gamma y B Y S t i).
Proof.
  intros Hb Hg HY HS Hi; split.
  - apply gaussian_row_velocity_continuous; assumption.
  - split; [apply gaussian_row_remainder_continuous; assumption|].
    apply (multirow_row_observables_polynomial_bounds n m beta gamma y B Y S t i); assumption.
Qed.
