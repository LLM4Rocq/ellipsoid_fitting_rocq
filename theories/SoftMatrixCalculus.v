From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights Cubic
  MatrixDefinitions MatrixCoordinates MatrixTrace MatrixGibbsDefinitions
  MatrixSecondDefinitions MatrixThirdDefinitions MatrixThird TensorDefinitions
  TensorGibbs TensorSum SoftMatrixDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/SoftMatrixCalculus.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. No lemma is added. All statements but one keep the
   text of the original. They mention only the definitions of the ported
   modules, Stdlib's arithmetic, the lists, In and NoDup, whose meaning the
   ports keep.

   The statement that changes is soft_matrix_coordinate_derivatives, in the
   ways of the port of MatrixThird, which it applies.

   1. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0. On matrix n the
      norm is the Frobenius norm of MatrixDefinitions, as in Coquelicot.

   2. Real-valued maps. A map into R given to is_diff is written with
      codomain R^o, the normed module view of R, as in
      ((fun M => ...) : matrix n -> R^o). R^o is R by definition, so the
      maps are the same.

   So the conclusion says the same thing as in the original.

   One change of notation. With ssreflect loaded, if d then a else b on a
   decision d : {j = i} + {j <> i} elaborates to if is_left d then a else b,
   a test on the boolean is_left d, which is not the term of the original.
   The statement of soft_matrix_single_sum, and the two proofs that state a
   sum of the same shape, therefore write the match that the original's
   if Nat.eq_dec j i then x else 0 stands for, as
   match Nat.eq_dec j i with left _ => x | right _ => 0 end. The term is the
   original's, and so is the meaning.

   In the proofs, Coquelicot's plus_zero_r becomes MathComp's addr0, since
   matrix_add and matrix_zero are MathComp's + and 0 on matrix n in the
   port of MatrixDefinitions, and filterdiff_ext becomes rewriting the
   function with funext. Stdlib's "rewrite A, B" and "rewrite ... by tac"
   are written in the forms that ssreflect accepts. *)

Lemma soft_matrix_coordinate_sum_add n f g :
  coordinate_sum n (fun i => f i + g i) = coordinate_sum n f + coordinate_sum n g.
Proof. revert f g; induction n; intros f g; simpl; [ring|rewrite IHn; ring]. Qed.

Lemma soft_matrix_coordinate_sum_swap n m f :
  coordinate_sum n (fun i => coordinate_sum m (f i)) =
    coordinate_sum m (fun j => coordinate_sum n (fun i => f i j)).
Proof.
  revert f; induction n; intros f; simpl; [reflexivity|].
  rewrite soft_matrix_coordinate_sum_add IHn; reflexivity.
Qed.

Lemma soft_matrix_trace_pair_swap n (A B : matrix n) : trace_pair n A B = trace_pair n B A.
Proof.
  unfold trace_pair; rewrite soft_matrix_coordinate_sum_swap.
  apply coordinate_sum_ext; intros i Hi; apply coordinate_sum_ext; intros j Hj; ring.
Qed.

Theorem soft_matrix_scores_trace_product n y B I (A : nat -> matrix n) z s :
  soft_matrix_scores n y B I A z s =
    finite_sum (fun i => y z i * matrix_trace n (matrix_mul n (A i) (B s))) I.
Proof.
  unfold soft_matrix_scores; apply gibbs_sum_ext; intros i Hi.
  rewrite soft_matrix_trace_pair_swap trace_pair_is_trace_product; reflexivity.
Qed.

Lemma soft_matrix_block_add_zero n (A : nat -> matrix n) i :
  soft_matrix_block_add n A i (matrix_zero n) = A.
Proof.
  apply functional_extensionality; intros j; unfold soft_matrix_block_add.
  destruct (Nat.eq_dec j i); [|reflexivity].
  unfold matrix_add, matrix_zero; exact: addr0.
Qed.

Lemma soft_matrix_block_add_symmetric n (A : nat -> matrix n) i (M : matrix n) I :
  (forall j, In j I -> symmetric_matrix n (A j)) -> symmetric_matrix n M ->
  forall j, In j I -> symmetric_matrix n (soft_matrix_block_add n A i M j).
Proof.
  intros HA HM j Hj; unfold soft_matrix_block_add; destruct (Nat.eq_dec j i).
  - apply matrix_add_symmetric; [apply HA; exact Hj|exact HM].
  - apply HA; exact Hj.
Qed.

Lemma soft_matrix_single_sum I i x :
  NoDup I -> In i I -> finite_sum (fun j => match Nat.eq_dec j i with left _ => x | right _ => 0 end) I = x.
Proof.
  induction I as [|j I IH]; intros HD Hi; [contradiction|].
  inversion HD as [|j' I' Hnot Htail]; subst.
  simpl in Hi |- *; destruct (Nat.eq_dec j i) as [Heq|Hne].
  - subst j.
    assert (HZ : finite_sum (fun j => match Nat.eq_dec j i with left _ => x | right _ => 0 end) I = 0).
    { transitivity (finite_sum (fun _ => 0) I).
      - apply gibbs_sum_ext; intros j Hj; destruct (Nat.eq_dec j i); [subst; contradiction|reflexivity].
      - apply gibbs_sum_zero. }
    rewrite HZ; ring.
  - destruct Hi as [Heq|Hi]; [contradiction|].
    rewrite (IH Htail Hi); ring.
Qed.

Theorem soft_matrix_scores_perturbation n y B I (A : nat -> matrix n) i (M : matrix n) :
  NoDup I -> In i I ->
  soft_matrix_scores n y B I (soft_matrix_block_add n A i M) =
    matrix_affine_scores n (soft_matrix_scores n y B I A) (soft_matrix_coefficients n y B i) M.
Proof.
  intros HD Hi; apply functional_extensionality; intros z.
  apply functional_extensionality; intros s.
  unfold soft_matrix_scores at 1.
  transitivity (finite_sum (fun j => y z j * trace_pair n (B s) (A j) +
    match Nat.eq_dec j i with left _ => y z i * trace_pair n (B s) M | right _ => 0 end) I).
  - apply gibbs_sum_ext; intros j Hj; unfold soft_matrix_block_add.
    destruct (Nat.eq_dec j i); [subst; rewrite trace_pair_add; ring|ring].
  - rewrite gibbs_sum_add (soft_matrix_single_sum I i _ HD Hi).
    unfold matrix_affine_scores, soft_matrix_coefficients; rewrite trace_pair_left_scale; reflexivity.
Qed.

Theorem soft_matrix_phi_perturbation n beta gamma y B I Y S (A : nat -> matrix n) i M :
  NoDup I -> In i I ->
  soft_matrix_phi n beta gamma y B I Y S (soft_matrix_block_add n A i M) =
    soft_minimax beta gamma
      (matrix_affine_scores n (soft_matrix_scores n y B I A) (soft_matrix_coefficients n y B i) M) Y S.
Proof.
  intros HD Hi; unfold soft_matrix_phi; rewrite (soft_matrix_scores_perturbation n y B I A i M HD Hi).
  reflexivity.
Qed.

Lemma soft_matrix_first_rebase n beta gamma H coeff Y S (M U : matrix n) :
  matrix_nested_derivative n beta gamma (matrix_affine_scores n H coeff M) coeff Y S (matrix_zero n) U =
    matrix_nested_derivative n beta gamma H coeff Y S M U.
Proof.
  unfold matrix_nested_derivative, matrix_inner_derivative, matrix_inner_values.
  rewrite !matrix_affine_scores_at_zero; reflexivity.
Qed.

Lemma soft_matrix_second_rebase n beta gamma H coeff Y S (M U V : matrix n) :
  matrix_nested_second_derivative n beta gamma (matrix_affine_scores n H coeff M) coeff
    Y S (matrix_zero n) U V = matrix_nested_second_derivative n beta gamma H coeff Y S M U V.
Proof.
  unfold matrix_nested_second_derivative, matrix_inner_covariance, matrix_inner_derivative, matrix_inner_values.
  rewrite !matrix_affine_scores_at_zero; reflexivity.
Qed.

Theorem soft_matrix_coordinate_derivatives n beta gamma y B I Y S (A : nat -> matrix n) i :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> NoDup I -> In i I ->
  is_diff (matrix_zero n)
    ((fun M => soft_matrix_phi n beta gamma y B I Y S (soft_matrix_block_add n A i M))
      : matrix n -> R^o)
    (soft_matrix_first n beta gamma y B I Y S A i) /\
  forall U : matrix n,
  is_diff (matrix_zero n)
    ((fun M => soft_matrix_first n beta gamma y B I Y S (soft_matrix_block_add n A i M) i U)
      : matrix n -> R^o)
    (soft_matrix_second n beta gamma y B I Y S A i U) /\
  forall V : matrix n,
  is_diff (matrix_zero n)
    ((fun M => soft_matrix_second n beta gamma y B I Y S (soft_matrix_block_add n A i M) i U V)
      : matrix n -> R^o)
    (soft_matrix_third n beta gamma y B I Y S A i U V).
Proof.
  intros Hb Hg HY HS HD Hi.
  destruct (matrix_nested_soft_minimax_third_frechet n beta gamma (soft_matrix_scores n y B I A)
    (soft_matrix_coefficients n y B i) Y S Hb Hg HY HS (matrix_zero n)) as [Hfirst Hrest].
  split.
  - have -> : (fun M => soft_matrix_phi n beta gamma y B I Y S (soft_matrix_block_add n A i M)) =
      (fun M => soft_minimax beta gamma
        (matrix_affine_scores n (soft_matrix_scores n y B I A) (soft_matrix_coefficients n y B i) M) Y S).
    { apply: funext => M; apply soft_matrix_phi_perturbation; assumption. }
    exact Hfirst.
  - intros U; destruct (Hrest U) as [Hsecond Hthird]; split.
    + have -> : (fun M => soft_matrix_first n beta gamma y B I Y S (soft_matrix_block_add n A i M) i U) =
        (fun M => matrix_nested_derivative n beta gamma (soft_matrix_scores n y B I A)
          (soft_matrix_coefficients n y B i) Y S M U).
      { apply: funext => M; unfold soft_matrix_first.
        rewrite (soft_matrix_scores_perturbation n y B I A i M HD Hi).
        apply soft_matrix_first_rebase. }
      exact Hsecond.
    + intros V.
      have -> : (fun M => soft_matrix_second n beta gamma y B I Y S (soft_matrix_block_add n A i M) i U V) =
        (fun M => matrix_nested_second_derivative n beta gamma (soft_matrix_scores n y B I A)
          (soft_matrix_coefficients n y B i) Y S M U V).
      { apply: funext => M; unfold soft_matrix_second.
        rewrite (soft_matrix_scores_perturbation n y B I A i M HD Hi).
        apply soft_matrix_second_rebase. }
      exact (Hthird V).
Qed.
