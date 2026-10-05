From Stdlib Require Import Reals Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates.
From EllipsoidFitting Require Import OperatorDefinitions OperatorDefinitionsAux.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/OperatorBounds.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements change form in the ways of the port of
   MatrixCoordinates.

   1. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. The norms are
      those of MatrixDefinitions: the Euclidean norm on vectors and on tuples,
      the Frobenius norm on matrices, and the absolute value on R, as in
      Coquelicot. Comparisons, products and powers around these norms are
      Stdlib's, as before.

   2. Coquelicot's is_linear l is stated, as in MatrixCoordinates, as the
      conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound. The
      meaning is the same, constants included.

   3. The order on indices (i <= n)%nat of the original is Stdlib's Peano
      order. With ssreflect loaded, (i <= n)%nat means ssrnat's boolean leq,
      so the statements write (i <= n)%coq_nat, which is Stdlib's le.

   4. matrix_operator_norm is now MathComp's sup of the unit image, not
      Coquelicot's real (Lub_Rbar _); OperatorDefinitions explains why the
      value is the same. matrix_operator_norm_lub keeps its statement, with
      Stdlib's is_lub. Its proof uses matrix_operator_norm_is_lub of
      OperatorDefinitionsAux in place of Coquelicot's Lub_Rbar_correct.

   The port adds one item, marked below: a Hierarchy Builder instance that
   declares matrix_action n A a linear map. *)

(* Declaring matrix_action n A a linear map makes HB report canonical
   projections that duplicate existing ones. Rocq ignores the duplicates; the
   warning is silenced in this file only. *)
Local Set Warnings "-redundant-canonical-projection".

Lemma tuple_build_linear {U V : normedModType R} n (F : nat -> U -> V) :
  (forall i, (i <= n)%coq_nat ->
    linear (F i) /\
    exists M : R, 0 < M /\ forall x : U, (`|F i x|)%R <= M * (`|x|)%R) ->
  linear (fun x => tuple_build V n (fun i => F i x)) /\
    exists M : R, 0 < M /\
      forall x : U, (`|tuple_build V n (fun i => F i x)|)%R <= M * (`|x|)%R.
Proof.
  revert F; induction n as [|n IH]; intros F HF; simpl.
  - apply HF; lia.
  - destruct (HF O ltac:(lia)) as [L0 [M0 [HM0 HB0]]].
    destruct (IH (fun i => F (S i)) ltac:(intros i Hi; apply HF; lia))
      as [LS [MS [HMS HBS]]].
    split.
    + intros a u v; simpl.
      change ((F O (a *: u + v)%R,
               tuple_build V n (fun i => F (S i) (a *: u + v)%R)) =
        ((a *: F O u + F O v)%R,
         (a *: tuple_build V n (fun i => F (S i) u) +
          tuple_build V n (fun i => F (S i) v))%R)).
      rewrite L0; f_equal; apply LS.
    + exists (M0 + MS); split; [lra|]; intros x.
      set (p := (F O x, tuple_build V n (fun i => F (S i) x)) :
        tuple_NormedModule V (S n)).
      apply (Rle_trans _ ((`|p.1|)%R + (`|p.2|)%R)).
      * apply/RleP; exact (euclidean_product_norm_le p).
      * change ((`|F O x|)%R + (`|tuple_build V n (fun i => F (S i) x)|)%R <=
          (M0 + MS) * (`|x|)%R).
        specialize (HB0 x); specialize (HBS x); lra.
Qed.

Lemma vector_abs_square (x : R) : Rabs x ^ 2 = x ^ 2.
Proof. destruct (Rcase_abs x); [rewrite Rabs_left | rewrite Rabs_right]; nra. Qed.

Lemma vector_norm_squared n (x : vector n) :
  (`|x|)%R ^ 2 = coordinate_sum n (fun i => vector_entry n x i ^ 2).
Proof.
  induction n as [|n IH].
  - change ((`|x : R^o|)%R ^ 2 = x ^ 2).
    rewrite -RabsE; apply vector_abs_square.
  - destruct x as [a xs].
    change (sqrt ((`|a : R^o|)%R ^ 2 + (`|xs : vector n|)%R ^ 2) ^ 2 =
      a ^ 2 + coordinate_sum n (fun i => vector_entry n xs i ^ 2)).
    assert (Ha : 0 <= (`|a : R^o|)%R ^ 2) by apply pow2_ge_0.
    assert (Hx : 0 <= (`|xs : vector n|)%R ^ 2) by apply pow2_ge_0.
    rewrite pow2_sqrt; [lra|].
    rewrite -RabsE vector_abs_square IH; reflexivity.
Qed.

Lemma matrix_action_entry n (A : matrix n) (x : vector n) i :
  (i <= n)%coq_nat -> vector_entry n (matrix_action n A x) i =
    coordinate_sum n (fun j => matrix_entry n A i j * vector_entry n x j).
Proof.
  intros Hi; unfold matrix_action, vector_entry.
  exact (tuple_entry_build R^o n i _ Hi).
Qed.

Lemma matrix_action_linear n (A : matrix n) :
  linear (matrix_action n A) /\
  exists M : R, 0 < M /\
    forall x : vector n, (`|matrix_action n A x|)%R <= M * (`|x|)%R.
Proof.
  unfold matrix_action; apply tuple_build_linear; intros i Hi.
  apply coordinate_sum_linear; intros j Hj.
  apply matrix_linear_scale, tuple_entry_linear.
Qed.

(* Added by the port. matrix_action n A is a {linear _ -> _} of MathComp, so
   that linearD, linearZ, linear0 and the other lemmas about linear maps
   apply to it directly, in place of Coquelicot's linear_plus, linear_scal
   and linear_zero. The instance changes no statement. *)
HB.instance Definition _ n (A : matrix n) :=
  GRing.isLinear.Build R (vector_NormedModule n) (vector_NormedModule n) *:%R
    (matrix_action n A) (proj1 (matrix_action_linear n A)).

Lemma matrix_unit_image_zero n (A : matrix n) : matrix_unit_image n A 0.
Proof.
  exists 0%R; split.
  - rewrite normr0; exact Rle_0_1.
  - rewrite linear0 normr0; reflexivity.
Qed.

Theorem matrix_operator_norm_lub n (A : matrix n) :
  is_lub (matrix_unit_image n A) (matrix_operator_norm n A).
Proof.
  apply matrix_operator_norm_is_lub.
  - destruct (proj2 (matrix_action_linear n A)) as [M [HM Hbound]].
    exists M; intros r [x [Hx ->]].
    specialize (Hbound x); nra.
  - exists 0; apply matrix_unit_image_zero.
Qed.

Theorem matrix_operator_norm_nonnegative n (A : matrix n) :
  0 <= matrix_operator_norm n A.
Proof.
  apply (proj1 (matrix_operator_norm_lub n A)), matrix_unit_image_zero.
Qed.

Theorem matrix_operator_norm_upper n (A : matrix n) C :
  (forall x : vector n, (`|x|)%R <= 1 -> (`|matrix_action n A x|)%R <= C) ->
  matrix_operator_norm n A <= C.
Proof.
  intros HC; apply (proj2 (matrix_operator_norm_lub n A)).
  intros r [x [Hx ->]]; apply HC; exact Hx.
Qed.
