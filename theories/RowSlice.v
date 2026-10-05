From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights Cubic
  MatrixDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions
  MatrixThirdDefinitions MatrixThird OperatorDefinitions TensorDefinitions TensorSum
  SoftMatrixDefinitions SoftMatrixCalculus SoftMatrix RowSliceDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of the inner module RowSlice of theories/ComparisonProofs.v from
   Coquelicot to MathComp-Analysis. The source is
   build/agent2/unbundled/RowSlice.v.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. No item is added. Nine statements keep the text of the original:
   soft_matrix_block_replace_current, soft_matrix_block_replace_as_add,
   soft_matrix_row_scores, soft_matrix_row_shared_scores,
   soft_matrix_row_shared_inner, soft_matrix_row_phi,
   soft_matrix_third_rebase, soft_matrix_row_third and
   soft_matrix_row_third_at_current. They mention only the definitions of
   the ported modules, Stdlib's arithmetic, the lists, In and NoDup, whose
   meaning the ports keep. The three others change form in the ways of the
   ports of SoftMatrixCalculus and SoftMatrix, which they apply.

   1. Frechet derivatives. In soft_matrix_row_actual_derivatives,
      Coquelicot's filterdiff f (locally M) l becomes is_diff M f l of
      MathComp-Analysis (README difference 2): f is differentiable at M and
      its differential 'd f M is l. Both say that l is linear and continuous
      and that f (M + H) = f M + l H + o(H) as H tends to 0. On matrix n the
      norm is the Frobenius norm of MatrixDefinitions, as in Coquelicot. The
      real-valued maps given to is_diff are typed into R^o, the normed module
      view of R, which is R by definition, as in
      ((fun H => ...) : matrix n -> R^o).

   2. Extended reals. In soft_matrix_row_projective_sum and
      soft_matrix_row_radial_sum, Coquelicot's Finite r and real x on Rbar
      become MathComp's EFin r and fine x on \bar R, as in the ports of
      TensorDefinitions, TensorSum and SoftMatrix. projective_operator_norm
      is the infimum of the same set of costs in both libraries, and
      N = EFin (fine N) says, as N = Finite (real N) did, that N is a real
      number.

   So these statements say the same thing as in the original.

   In the proofs, Coquelicot's plus_zero_l becomes MathComp's add0r, since
   matrix_add and matrix_zero are MathComp's + and 0 on matrix n in the port
   of MatrixDefinitions, and filterdiff_ext becomes rewriting the function
   with funext. Stdlib's "rewrite ... by tac" is written in the forms that
   ssreflect accepts. *)

Lemma soft_matrix_block_replace_current n (A : nat -> matrix n) i :
  soft_matrix_block_replace n A i (A i) = A.
Proof.
  apply functional_extensionality; intros j; unfold soft_matrix_block_replace.
  destruct (Nat.eq_dec j i); [subst; reflexivity|reflexivity].
Qed.

Lemma soft_matrix_block_replace_as_add n (A : nat -> matrix n) i M :
  soft_matrix_block_replace n A i M =
    soft_matrix_block_add n (soft_matrix_block_replace n A i (matrix_zero n)) i M.
Proof.
  apply functional_extensionality; intros j.
  unfold soft_matrix_block_replace, soft_matrix_block_add.
  destruct (Nat.eq_dec j i); [|reflexivity].
  unfold matrix_add, matrix_zero; symmetry; exact (@add0r (matrix_NormedModule n) M).
Qed.

Theorem soft_matrix_row_scores n y B I (A : nat -> matrix n) i M :
  NoDup I -> In i I ->
  matrix_affine_scores n (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) M =
  soft_matrix_scores n y B I (soft_matrix_block_replace n A i M).
Proof.
  intros HD Hi; rewrite soft_matrix_block_replace_as_add.
  symmetry; apply soft_matrix_scores_perturbation; assumption.
Qed.

Theorem soft_matrix_row_shared_scores n y B I (A : nat -> matrix n) i :
  NoDup I -> In i I ->
  matrix_affine_scores n (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) (A i) = soft_matrix_scores n y B I A.
Proof.
  intros HD Hi; rewrite (soft_matrix_row_scores n y B I A i (A i) HD Hi).
  apply f_equal; apply soft_matrix_block_replace_current.
Qed.

Theorem soft_matrix_row_shared_inner n gamma y B I S (A : nat -> matrix n) i :
  NoDup I -> In i I ->
  matrix_inner_values n gamma (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) S (A i) = soft_matrix_inner n gamma y B I S A.
Proof.
  intros HD Hi; unfold matrix_inner_values, soft_matrix_inner.
  rewrite (soft_matrix_row_shared_scores n y B I A i HD Hi); reflexivity.
Qed.

Theorem soft_matrix_row_phi n beta gamma y B I Y S (A : nat -> matrix n) i M :
  NoDup I -> In i I ->
  soft_minimax beta gamma
    (matrix_affine_scores n (soft_matrix_row_offset n y B I A i)
      (soft_matrix_coefficients n y B i) M) Y S =
  soft_matrix_phi n beta gamma y B I Y S (soft_matrix_block_replace n A i M).
Proof.
  intros HD Hi; unfold soft_matrix_phi.
  rewrite (soft_matrix_row_scores n y B I A i M HD Hi); reflexivity.
Qed.

Lemma soft_matrix_third_rebase n beta gamma H coeff Y S (M U V W : matrix n) :
  matrix_nested_third_derivative n beta gamma (matrix_affine_scores n H coeff M)
    coeff Y S (matrix_zero n) U V W =
  matrix_nested_third_derivative n beta gamma H coeff Y S M U V W.
Proof.
  unfold matrix_nested_third_derivative, matrix_inner_cumulant,
    matrix_inner_covariance, matrix_inner_derivative, matrix_inner_values.
  rewrite !matrix_affine_scores_at_zero; reflexivity.
Qed.

Theorem soft_matrix_row_third n beta gamma y B I Y S (A : nat -> matrix n) i M U V W :
  NoDup I -> In i I ->
  matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) Y S M U V W =
  soft_matrix_third n beta gamma y B I Y S (soft_matrix_block_replace n A i M) i U V W.
Proof.
  intros HD Hi; unfold soft_matrix_third.
  rewrite <- (soft_matrix_row_scores n y B I A i M HD Hi).
  symmetry; apply soft_matrix_third_rebase.
Qed.

Theorem soft_matrix_row_third_at_current n beta gamma y B I Y S
    (A : nat -> matrix n) i :
  NoDup I -> In i I ->
  matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) Y S (A i) =
  soft_matrix_third n beta gamma y B I Y S A i.
Proof.
  intros HD Hi; apply functional_extensionality; intros U.
  apply functional_extensionality; intros V; apply functional_extensionality; intros W.
  rewrite (soft_matrix_row_third n beta gamma y B I Y S A i (A i) U V W HD Hi).
  rewrite soft_matrix_block_replace_current; reflexivity.
Qed.

Theorem soft_matrix_row_actual_derivatives n beta gamma y B I Y S
    (A : nat -> matrix n) i M :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> NoDup I -> In i I ->
  is_diff M
    ((fun H => soft_matrix_phi n beta gamma y B I Y S
      (soft_matrix_block_replace n A i H)) : matrix n -> R^o)
    (matrix_nested_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
      (soft_matrix_coefficients n y B i) Y S M) /\
  forall U : matrix n,
  is_diff M
    ((fun H => matrix_nested_derivative n beta gamma
      (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S H U)
      : matrix n -> R^o)
    (matrix_nested_second_derivative n beta gamma
      (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S M U) /\
  forall V : matrix n,
  is_diff M
    ((fun H => matrix_nested_second_derivative n beta gamma
      (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S H U V)
      : matrix n -> R^o)
    (soft_matrix_third n beta gamma y B I Y S
      (soft_matrix_block_replace n A i M) i U V).
Proof.
  intros Hb Hg HY HS HD Hi.
  destruct (matrix_nested_soft_minimax_third_frechet n beta gamma
    (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i)
    Y S Hb Hg HY HS M) as [HF Hrest].
  split.
  - have -> : (fun H => soft_matrix_phi n beta gamma y B I Y S
        (soft_matrix_block_replace n A i H)) =
      (fun H => soft_minimax beta gamma
        (matrix_affine_scores n (soft_matrix_row_offset n y B I A i)
          (soft_matrix_coefficients n y B i) H) Y S).
    { apply: funext => H; symmetry; apply soft_matrix_row_phi; assumption. }
    exact HF.
  - intros U; destruct (Hrest U) as [Hsecond Hthird]; split; [exact Hsecond|].
    intros V; assert (HE : matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S M U V =
      soft_matrix_third n beta gamma y B I Y S (soft_matrix_block_replace n A i M) i U V).
    { apply functional_extensionality; intros W; apply soft_matrix_row_third; assumption. }
    rewrite <- HE; exact (Hthird V).
Qed.

Theorem soft_matrix_row_projective_sum n beta gamma y B I Y S
    (A : nat -> matrix n) theta k :
  0 < beta -> 0 < gamma -> 0 <= k -> 0 < theta -> Y <> [] -> S <> [] -> NoDup I ->
  (forall z, In z Y -> euclidean_norm (y z) I = 1) ->
  (forall z i, In z Y -> In i I -> Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  (forall i, In i I ->
    let N := projective_operator_norm (matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S (A i)) in
    N = EFin (fine N) /\ 0 <= fine N) /\
  finite_sum (fun i => fine (projective_operator_norm (matrix_nested_third_derivative n beta gamma
    (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S (A i)))) I <=
    10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n)).
Proof.
  intros Hb Hg Hk Htheta HY HS HD Hunit Hcap Hsym HB.
  destruct (soft_matrix_projective_sum_bound n beta gamma y B I Y S A theta k
    Hb Hg Hk Htheta HY HS Hunit Hcap Hsym HB) as [Hfinite Hsum].
  split.
  - intros i Hi.
    rewrite (soft_matrix_row_third_at_current n beta gamma y B I Y S A i HD Hi).
    exact (Hfinite i Hi).
  - erewrite gibbs_sum_ext; [exact Hsum|].
    intros i Hi; rewrite (soft_matrix_row_third_at_current n beta gamma y B I Y S A i HD Hi).
    reflexivity.
Qed.

Theorem soft_matrix_row_radial_sum n beta gamma y B I Y S
    (A : nat -> matrix n) theta k (radius : nat -> R) Rmax :
  0 < beta -> 0 < gamma -> 0 <= k -> 0 < theta -> Y <> [] -> S <> [] -> NoDup I ->
  (forall z, In z Y -> euclidean_norm (y z) I = 1) ->
  (forall z i, In z Y -> In i I -> Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  0 <= Rmax -> (forall i, In i I -> radius i <= Rmax) ->
  finite_sum (fun i => radius i * fine (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
      (soft_matrix_coefficients n y B i) Y S (A i)))) I <=
  Rmax * (10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n))).
Proof.
  intros Hb Hg Hk Htheta HY HS HD Hunit Hcap Hsym HB HR Hr.
  destruct (soft_matrix_row_projective_sum n beta gamma y B I Y S A theta k
    Hb Hg Hk Htheta HY HS HD Hunit Hcap Hsym HB) as [Hfinite Hsum].
  eapply Rle_trans with (finite_sum (fun i => Rmax * fine (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
      (soft_matrix_coefficients n y B i) Y S (A i)))) I).
  - apply cubic_sum_le; intros i Hi; apply Rmult_le_compat_r.
    + exact (proj2 (Hfinite i Hi)).
    + apply Hr; exact Hi.
  - rewrite cubic_sum_scale; apply Rmult_le_compat_l; assumption.
Qed.
