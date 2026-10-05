From Stdlib Require Import Reals Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions OperatorBounds.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/OperatorProperties.v from Coquelicot to MathComp-Analysis.

   Every definition and lemma of the original keeps its name and its
   arguments, in the same order. The statements change form in the ways of
   the ports of MatrixCoordinates and OperatorBounds.

   1. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. The norms are
      those of MatrixDefinitions: the Euclidean norm on vectors, the
      Frobenius norm on matrices, and the absolute value on R, as in
      Coquelicot. Comparisons, products and absolute values around these
      norms are Stdlib's, as before.

   2. Coquelicot's zero, plus and scal on vectors become MathComp's 0%R,
      + and *:, which are componentwise on the nested pairs as before.
      NormedModule R_AbsRing becomes normedModType R, and R_NormedModule
      becomes R^o.

   3. Coquelicot's is_linear l is stated, as in MatrixCoordinates, as the
      conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound. The
      meaning is the same, constants included.

   4. The order on indices (j <= n)%nat of the original is Stdlib's Peano
      order. With ssreflect loaded, (j <= n)%nat means ssrnat's boolean leq,
      so the statements write (j <= n)%coq_nat, which is Stdlib's le.

   The meaning of every statement is unchanged. *)

Lemma real_norm_scal_exact {V : normedModType R} (a : R) (x : V) :
  (`|(a *: x)%R|)%R = Rabs a * (`|x|)%R.
Proof. by rewrite normrZ RabsE. Qed.

Lemma matrix_action_left_linear n (x : vector n) :
  linear (fun A : matrix n => matrix_action n A x) /\
  exists M : R, 0 < M /\
    forall A : matrix n, (`|matrix_action n A x|)%R <= M * (`|A|)%R.
Proof.
  unfold matrix_action; apply tuple_build_linear; intros i Hi.
  apply coordinate_sum_linear; intros j Hj.
  have E : (fun A : matrix n => matrix_entry n A i j * vector_entry n x j) =
    (fun A : matrix n => vector_entry n x j * matrix_entry n A i j).
  { apply funext; intros A; apply Rmult_comm. }
  destruct (matrix_linear_scale (vector_entry n x j)
    (fun A : matrix n => matrix_entry n A i j) (matrix_entry_linear n i j))
    as [L [M [HM HB]]].
  split.
  - rewrite E; exact L.
  - exists M; split; [exact HM|]; intros A.
    rewrite (Rmult_comm (matrix_entry n A i j)); exact (HB A).
Qed.

(* The map A |-> matrix_action n A x, packed as a MathComp linear map, so
   that linearD, linearZ and linear0 apply to it. *)
Local Definition operator_left_action n (x : vector n) :
    {linear matrix_NormedModule n -> vector_NormedModule n} :=
  HB.pack (fun A : matrix n => matrix_action n A x)
    (GRing.isLinear.Build R (matrix_NormedModule n) (vector_NormedModule n)
      *:%R (fun A : matrix n => matrix_action n A x)
      (proj1 (matrix_action_left_linear n x))).

Lemma matrix_action_add n (A B : matrix n) (x : vector n) :
  matrix_action n (matrix_add n A B) x =
  (matrix_action n A x + matrix_action n B x)%R.
Proof. exact (linearD (operator_left_action n x) A B). Qed.

Lemma matrix_action_scale n c (A : matrix n) (x : vector n) :
  matrix_action n (matrix_scale n c A) x = (c *: matrix_action n A x)%R.
Proof. exact (linearZ_LR (operator_left_action n x) c A). Qed.

Lemma matrix_action_zero n (x : vector n) :
  matrix_action n (matrix_zero n) x = 0%R.
Proof. exact (linear0 (operator_left_action n x)). Qed.

Lemma matrix_action_unit_bound n (A : matrix n) (x : vector n) :
  (`|x|)%R <= 1 -> (`|matrix_action n A x|)%R <= matrix_operator_norm n A.
Proof.
  intros Hx; apply (proj1 (matrix_operator_norm_lub n A)).
  exists x; split; [exact Hx|reflexivity].
Qed.

Theorem matrix_action_norm_bound n (A : matrix n) (x : vector n) :
  (`|matrix_action n A x|)%R <= matrix_operator_norm n A * (`|x|)%R.
Proof.
  destruct (Req_dec (`|x|)%R 0) as [Hx|Hx].
  - have HE : x = 0%R by apply: normr0_eq0; exact Hx.
    rewrite Hx HE linear0 normr0 Rmult_0_r; exact (Rle_refl 0).
  - have H0 : 0 <= (`|x|)%R by apply/RleP; apply normr_ge0.
    have Hpos : 0 < (`|x|)%R by lra.
    set c := Rinv (`|x|)%R.
    have Hc : 0 < c by apply Rinv_0_lt_compat.
    have Hunit : (`|(c *: x)%R|)%R <= 1.
    { rewrite real_norm_scal_exact (Rabs_pos_eq c (Rlt_le _ _ Hc)).
      unfold c; rewrite (Rinv_l _ Hx); exact (Rle_refl 1). }
    have H := matrix_action_unit_bound n A _ Hunit.
    rewrite linearZ real_norm_scal_exact (Rabs_pos_eq c (Rlt_le _ _ Hc)) in H.
    apply (Rmult_le_reg_l c); [exact Hc|].
    replace (c * (matrix_operator_norm n A * (`|x|)%R)) with
      (matrix_operator_norm n A) by (unfold c; field; exact Hx).
    exact H.
Qed.

Theorem matrix_operator_norm_triangle n (A B : matrix n) :
  matrix_operator_norm n (matrix_add n A B) <=
  matrix_operator_norm n A + matrix_operator_norm n B.
Proof.
  apply matrix_operator_norm_upper; intros x Hx.
  rewrite matrix_action_add.
  apply (Rle_trans _ ((`|matrix_action n A x|)%R + (`|matrix_action n B x|)%R)).
  - apply/RleP; exact (ler_normD _ _).
  - apply Rplus_le_compat; apply matrix_action_unit_bound; exact Hx.
Qed.

Theorem matrix_operator_norm_zero n : matrix_operator_norm n (matrix_zero n) = 0.
Proof.
  apply Rle_antisym; [|apply matrix_operator_norm_nonnegative].
  apply matrix_operator_norm_upper; intros x Hx.
  rewrite matrix_action_zero normr0; exact (Rle_refl 0).
Qed.

Lemma matrix_operator_norm_scale_le n c (A : matrix n) :
  matrix_operator_norm n (matrix_scale n c A) <= Rabs c * matrix_operator_norm n A.
Proof.
  apply matrix_operator_norm_upper; intros x Hx.
  rewrite matrix_action_scale real_norm_scal_exact.
  apply Rmult_le_compat_l; [apply Rabs_pos|apply matrix_action_unit_bound; exact Hx].
Qed.

Theorem matrix_operator_norm_scale n c (A : matrix n) :
  matrix_operator_norm n (matrix_scale n c A) = Rabs c * matrix_operator_norm n A.
Proof.
  destruct (Req_dec c 0) as [->|Hc].
  - have H0 : matrix_scale n 0 A = matrix_zero n by exact: scale0r.
    rewrite H0 matrix_operator_norm_zero Rabs_R0; ring.
  - apply Rle_antisym; [apply matrix_operator_norm_scale_le|].
    have H := matrix_operator_norm_scale_le n (/ c) (matrix_scale n c A).
    have HE : matrix_scale n (/ c) (matrix_scale n c A) = A.
    { unfold matrix_scale; rewrite scalerA -RmultE (Rinv_l c Hc).
      exact: scale1r. }
    rewrite HE Rabs_inv in H.
    have Habs : 0 < Rabs c by apply Rabs_pos_lt; exact Hc.
    apply (Rmult_le_reg_l (/ Rabs c)); [apply Rinv_0_lt_compat; exact Habs|].
    replace (/ Rabs c * (Rabs c * matrix_operator_norm n A)) with
      (matrix_operator_norm n A) by (field; lra).
    exact H.
Qed.

Lemma operator_coordinate_sum_zero n : coordinate_sum n (fun _ => 0) = 0.
Proof. induction n; simpl; lra. Qed.

Lemma operator_coordinate_sum_select n j f :
  (j <= n)%coq_nat ->
  coordinate_sum n (fun i => f i * (if Nat.eqb i j then 1 else 0)) = f j.
Proof.
  revert j f; induction n as [|n IH]; intros [|j] f Hj; simpl.
  - ring.
  - lia.
  - have HZ : coordinate_sum n (fun i => f (S i) * 0) = 0.
    { transitivity (coordinate_sum n (fun _ => 0));
        [|apply operator_coordinate_sum_zero].
      apply coordinate_sum_ext; intros; ring. }
    rewrite HZ; ring.
  - rewrite (IH j (fun i => f (S i)) ltac:(lia)); ring.
Qed.

Definition operator_basis_vector n j : vector n :=
  tuple_build R^o n (fun i => if Nat.eqb i j then 1 else 0).

Lemma matrix_action_basis_entry n (A : matrix n) i j :
  (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  vector_entry n (matrix_action n A (operator_basis_vector n j)) i =
    matrix_entry n A i j.
Proof.
  intros Hi Hj; rewrite (matrix_action_entry n A _ i Hi).
  transitivity (coordinate_sum n (fun k =>
    matrix_entry n A i k * (if Nat.eqb k j then 1 else 0))).
  - apply coordinate_sum_ext; intros k Hk.
    unfold vector_entry, operator_basis_vector.
    rewrite (tuple_entry_build R^o n k _ Hk); reflexivity.
  - apply operator_coordinate_sum_select; exact Hj.
Qed.
