From Stdlib Require Import Reals Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  OperatorBounds OperatorProperties.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/NormEquivalence.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements change form in the ways of the ports of
   MatrixCoordinates, OperatorBounds and OperatorProperties.

   1. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. The norms are
      those of MatrixDefinitions: the Euclidean norm on vectors and on
      tuples, the Frobenius norm on matrices, and the absolute value on R, as
      in Coquelicot. The port of MatrixDefinitions keeps Coquelicot's product
      norm sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2) through
      euclidean_product, so the constants of the bounds below are unchanged:
      the Frobenius norm of a matrix lies between its operator norm and
      sqrt (INR (S n)) times its operator norm. Comparisons, products, powers
      and square roots around these norms are Stdlib's, as before.

   2. NormedModule R_AbsRing becomes normedModType R, and R_NormedModule
      becomes R^o.

   3. The order on indices (i <= n)%nat of the original is Stdlib's Peano
      order. With ssreflect loaded, (i <= n)%nat means ssrnat's boolean leq,
      so the statements write (i <= n)%coq_nat, which is Stdlib's le.

   The meaning of every statement is unchanged. *)

Lemma normeq_coordinate_sum_nonnegative n f :
  (forall i, (i <= n)%coq_nat -> 0 <= f i) -> 0 <= coordinate_sum n f.
Proof.
  revert f; induction n; intros f H; simpl.
  - apply H; lia.
  - apply Rplus_le_le_0_compat; [apply H; lia|apply IHn; intros; apply H; lia].
Qed.

Lemma normeq_coordinate_sum_le n f g :
  (forall i, (i <= n)%coq_nat -> f i <= g i) ->
  coordinate_sum n f <= coordinate_sum n g.
Proof.
  revert f g; induction n; intros f g H; simpl.
  - apply H; lia.
  - apply Rplus_le_compat; [apply H; lia|apply IHn; intros; apply H; lia].
Qed.

Lemma normeq_coordinate_sum_scale n a f :
  coordinate_sum n (fun i => a * f i) = a * coordinate_sum n f.
Proof.
  revert f; induction n; intros f; simpl; [ring|].
  rewrite (IHn (fun i => f (S i))); ring.
Qed.

Lemma normeq_coordinate_sum_const n a :
  coordinate_sum n (fun _ => a) = INR (S n) * a.
Proof.
  induction n; simpl coordinate_sum.
  - simpl; ring.
  - rewrite IHn (S_INR (S n)); ring.
Qed.

Lemma normeq_coordinate_sum_add n f g :
  coordinate_sum n (fun i => f i + g i) = coordinate_sum n f + coordinate_sum n g.
Proof.
  revert f g; induction n; intros f g; simpl; [ring|].
  rewrite (IHn (fun i => f (S i)) (fun i => g (S i))); ring.
Qed.

Lemma normeq_coordinate_sum_swap n m f :
  coordinate_sum n (fun i => coordinate_sum m (f i)) =
    coordinate_sum m (fun j => coordinate_sum n (fun i => f i j)).
Proof.
  revert f; induction n; intros f; simpl; [reflexivity|].
  rewrite (normeq_coordinate_sum_add m (f O)
    (fun j => coordinate_sum n (fun i => f (S i) j))).
  rewrite (IHn (fun i => f (S i))); reflexivity.
Qed.

Lemma normeq_coordinate_square_zero n f :
  coordinate_sum n (fun i => f i ^ 2) = 0 ->
  forall i, (i <= n)%coq_nat -> f i = 0.
Proof.
  revert f; induction n; intros f H i Hi.
  - assert (i = 0)%nat by lia; subst; simpl in H; nra.
  - change (f O ^ 2 + coordinate_sum n (fun i => f (S i) ^ 2) = 0) in H.
    assert (Ht : 0 <= coordinate_sum n (fun i => f (S i) ^ 2)).
    { apply normeq_coordinate_sum_nonnegative; intros; apply pow2_ge_0. }
    destruct i as [|i]; [nra|].
    apply (IHn (fun i => f (S i))); [nra|lia].
Qed.

Lemma normeq_coordinate_square_combination n f g a b :
  coordinate_sum n (fun i => (a * f i + b * g i) ^ 2) =
    a ^ 2 * coordinate_sum n (fun i => f i ^ 2) +
    2 * a * b * coordinate_sum n (fun i => f i * g i) +
    b ^ 2 * coordinate_sum n (fun i => g i ^ 2).
Proof.
  revert f g; induction n; intros f g; cbn [coordinate_sum]; [ring|].
  rewrite (IHn (fun i => f (S i)) (fun i => g (S i))); ring.
Qed.

Theorem coordinate_cauchy_schwarz_squared n f g :
  coordinate_sum n (fun i => f i * g i) ^ 2 <=
    coordinate_sum n (fun i => f i ^ 2) * coordinate_sum n (fun i => g i ^ 2).
Proof.
  set (a := coordinate_sum n (fun i => f i ^ 2)).
  set (b := coordinate_sum n (fun i => g i ^ 2)).
  set (c := coordinate_sum n (fun i => f i * g i)).
  assert (Hb : 0 <= b).
  { unfold b; apply normeq_coordinate_sum_nonnegative; intros; apply pow2_ge_0. }
  destruct (Req_dec b 0) as [Hz|Hz].
  - assert (Hc : c = 0).
    { unfold c; transitivity (coordinate_sum n (fun _ => 0)).
      - apply coordinate_sum_ext; intros i Hi.
        rewrite (normeq_coordinate_square_zero n g Hz i Hi); ring.
      - apply operator_coordinate_sum_zero. }
    rewrite Hz Hc; nra.
  - assert (Hp : 0 < b) by lra.
    assert (H : 0 <= coordinate_sum n (fun i => (b * f i + (- c) * g i) ^ 2)).
    { apply normeq_coordinate_sum_nonnegative; intros; apply pow2_ge_0. }
    rewrite (normeq_coordinate_square_combination n f g b (- c)) in H.
    fold a b c in H.
    apply (Rmult_le_reg_l b); [exact Hp|nra].
Qed.

Theorem tuple_norm_squared (V : normedModType R) n
    (x : tuple_NormedModule V n) :
  (`|x|)%R ^ 2 =
    coordinate_sum n (fun i => (`|tuple_entry V n i x|)%R ^ 2).
Proof.
  induction n as [|n IH]; [reflexivity|].
  destruct x as [a xs].
  change (sqrt ((`|a|)%R ^ 2 + (`|xs : tuple_NormedModule V n|)%R ^ 2) ^ 2 =
    (`|a|)%R ^ 2 +
      coordinate_sum n (fun i => (`|tuple_entry V n i xs|)%R ^ 2)).
  assert (Ha : 0 <= (`|a|)%R ^ 2) by apply pow2_ge_0.
  assert (Hx : 0 <= (`|xs : tuple_NormedModule V n|)%R ^ 2) by apply pow2_ge_0.
  rewrite (pow2_sqrt _ (Rplus_le_le_0_compat _ _ Ha Hx)).
  rewrite (IH xs); reflexivity.
Qed.

Theorem matrix_frobenius_norm_squared n (A : matrix n) :
  (`|A|)%R ^ 2 = coordinate_sum n
    (fun i => coordinate_sum n (fun j => matrix_entry n A i j ^ 2)).
Proof.
  transitivity (coordinate_sum n (fun i =>
    (`|tuple_entry (tuple_NormedModule R^o n) n i A|)%R ^ 2)).
  - exact (tuple_norm_squared (tuple_NormedModule R^o n) n A).
  - apply coordinate_sum_ext; intros i Hi.
    exact (vector_norm_squared n
      (tuple_entry (tuple_NormedModule R^o n) n i A)).
Qed.

Theorem matrix_action_frobenius_bound n (A : matrix n) (x : vector n) :
  (`|matrix_action n A x|)%R <= (`|A|)%R * (`|x|)%R.
Proof.
  assert (Hrow : forall i, (i <= n)%coq_nat ->
    vector_entry n (matrix_action n A x) i ^ 2 <=
      (`|x|)%R ^ 2 * coordinate_sum n (fun j => matrix_entry n A i j ^ 2)).
  { intros i Hi; rewrite (matrix_action_entry n A x i Hi).
    pose proof (coordinate_cauchy_schwarz_squared n
      (matrix_entry n A i) (vector_entry n x)) as H.
    rewrite -(vector_norm_squared n x) in H; nra. }
  pose proof (normeq_coordinate_sum_le n
    (fun i => vector_entry n (matrix_action n A x) i ^ 2)
    (fun i => (`|x|)%R ^ 2 *
      coordinate_sum n (fun j => matrix_entry n A i j ^ 2)) Hrow) as H.
  rewrite -(vector_norm_squared n (matrix_action n A x)) in H.
  rewrite (normeq_coordinate_sum_scale n ((`|x|)%R ^ 2)
    (fun i => coordinate_sum n (fun j => matrix_entry n A i j ^ 2))) in H.
  rewrite -(matrix_frobenius_norm_squared n A) in H.
  assert (HA : 0 <= (`|A|)%R) by (apply/RleP; apply normr_ge0).
  assert (Hx : 0 <= (`|x|)%R) by (apply/RleP; apply normr_ge0).
  assert (HAx : 0 <= (`|matrix_action n A x|)%R)
    by (apply/RleP; apply normr_ge0).
  assert (Hprod : 0 <= (`|A|)%R * (`|x|)%R) by (apply Rmult_le_pos; assumption).
  nra.
Qed.

Theorem matrix_operator_norm_le_frobenius n (A : matrix n) :
  matrix_operator_norm n A <= (`|A|)%R.
Proof.
  apply matrix_operator_norm_upper; intros x Hx.
  pose proof (matrix_action_frobenius_bound n A x).
  assert (HA : 0 <= (`|A|)%R) by (apply/RleP; apply normr_ge0).
  nra.
Qed.

Theorem operator_basis_vector_norm n j :
  (j <= n)%coq_nat -> (`|operator_basis_vector n j|)%R = 1.
Proof.
  intros Hj.
  assert (Hsq : (`|operator_basis_vector n j|)%R ^ 2 = 1).
  { rewrite vector_norm_squared.
    transitivity (coordinate_sum n
      (fun i => 1 * (if Nat.eqb i j then 1 else 0))).
    - apply coordinate_sum_ext; intros i Hi.
      unfold vector_entry, operator_basis_vector.
      rewrite (tuple_entry_build R^o n i _ Hi).
      destruct (Nat.eqb i j); ring.
    - apply operator_coordinate_sum_select; exact Hj. }
  assert (H0 : 0 <= (`|operator_basis_vector n j|)%R)
    by (apply/RleP; apply normr_ge0).
  nra.
Qed.

Theorem matrix_frobenius_column_identity n (A : matrix n) :
  (`|A|)%R ^ 2 = coordinate_sum n
    (fun j => (`|matrix_action n A (operator_basis_vector n j)|)%R ^ 2).
Proof.
  rewrite (matrix_frobenius_norm_squared n A).
  rewrite (normeq_coordinate_sum_swap n n (fun i j => matrix_entry n A i j ^ 2)).
  apply coordinate_sum_ext; intros j Hj.
  rewrite (vector_norm_squared n (matrix_action n A (operator_basis_vector n j))).
  apply coordinate_sum_ext; intros i Hi.
  rewrite (matrix_action_basis_entry n A i j Hi Hj); reflexivity.
Qed.

Theorem matrix_frobenius_operator_squared_bound n (A : matrix n) :
  (`|A|)%R ^ 2 <= INR (S n) * matrix_operator_norm n A ^ 2.
Proof.
  rewrite (matrix_frobenius_column_identity n A).
  rewrite -(normeq_coordinate_sum_const n (matrix_operator_norm n A ^ 2)).
  apply normeq_coordinate_sum_le; intros j Hj.
  apply pow_incr; split; [apply/RleP; apply normr_ge0|].
  apply matrix_action_unit_bound.
  rewrite (operator_basis_vector_norm n j Hj); lra.
Qed.

Theorem matrix_frobenius_le_sqrt_dimension_operator n (A : matrix n) :
  (`|A|)%R <= sqrt (INR (S n)) * matrix_operator_norm n A.
Proof.
  pose proof (matrix_frobenius_operator_squared_bound n A) as H.
  assert (Hd : 0 <= INR (S n)) by (apply pos_INR).
  assert (HE : (sqrt (INR (S n)) * matrix_operator_norm n A) ^ 2 =
    INR (S n) * matrix_operator_norm n A ^ 2).
  { rewrite Rpow_mult_distr (pow2_sqrt _ Hd); reflexivity. }
  rewrite -HE in H.
  assert (HA : 0 <= (`|A|)%R) by (apply/RleP; apply normr_ge0).
  assert (Hp : 0 <= sqrt (INR (S n)) * matrix_operator_norm n A).
  { apply Rmult_le_pos; [apply sqrt_pos|apply matrix_operator_norm_nonnegative]. }
  nra.
Qed.

Theorem matrix_frobenius_le_dimension_operator n (A : matrix n) :
  (`|A|)%R <= INR (S n) * matrix_operator_norm n A.
Proof.
  eapply Rle_trans; [apply matrix_frobenius_le_sqrt_dimension_operator|].
  apply Rmult_le_compat_r; [apply matrix_operator_norm_nonnegative|].
  assert (Hd : 1 <= INR (S n)) by (change (INR 1 <= INR (S n)); apply le_INR; lia).
  pose proof (sqrt_pos (INR (S n))) as Hs.
  pose proof (pow2_sqrt (INR (S n)) ltac:(lra)) as Hsq; nra.
Qed.

(* Both norms are the existing concrete norms: the induced Euclidean
   operator norm and the iterated Euclidean product norm of
   MatrixDefinitions, which is Coquelicot's. *)
Theorem matrix_norm_equivalence n (A : matrix n) :
  matrix_operator_norm n A <= (`|A|)%R /\
  (`|A|)%R <= INR (S n) * matrix_operator_norm n A.
Proof.
  split; [apply matrix_operator_norm_le_frobenius|
    apply matrix_frobenius_le_dimension_operator].
Qed.

(* Applying this to a difference of matrices gives both inclusions between
   norm neighborhoods, without replacing either concrete norm definition. *)
Theorem matrix_norm_ball_comparison n (A : matrix n) eps :
  0 < eps ->
  ((`|A|)%R < eps -> matrix_operator_norm n A < eps) /\
  (matrix_operator_norm n A < eps / INR (S n) -> (`|A|)%R < eps).
Proof.
  intros Heps; split.
  - intros H; pose proof (matrix_operator_norm_le_frobenius n A); lra.
  - intros H.
    assert (Hd : 0 < INR (S n)) by (apply lt_0_INR; lia).
    assert (Hlt : INR (S n) * matrix_operator_norm n A <
      INR (S n) * (eps / INR (S n))).
    { apply Rmult_lt_compat_l; assumption. }
    replace (INR (S n) * (eps / INR (S n))) with eps in Hlt by (field; lra).
    pose proof (matrix_frobenius_le_dimension_operator n A); lra.
Qed.
