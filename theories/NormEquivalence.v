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

(* Coordinate sums and Euclidean norms of tuples and matrices. Elementary
   rules for coordinate_sum, and coordinate_cauchy_schwarz_squared:
   (sum f g)^2 <= (sum f^2) (sum g^2). tuple_norm_squared: the squared
   norm of a tuple is the sum of the squared norms of its entries; so the
   squared Frobenius norm of a matrix is the sum of its squared entries
   (matrix_frobenius_norm_squared), and the sum of the squared norms of
   its columns A e_j (matrix_frobenius_column_identity). The basis vectors
   e_j have norm 1 (operator_basis_vector_norm). Indices are compared with
   Stdlib's order le, written (i <= n)%coq_nat. *)

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
