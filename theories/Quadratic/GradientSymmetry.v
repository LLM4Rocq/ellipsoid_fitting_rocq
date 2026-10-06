From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions Tensor.Definitions
  Tensor.GibbsDefinitions Gibbs.NestedGradientDefinitions
  Gibbs.MatrixNestedGradient Gibbs.HessianDefinitions Gibbs.NestedHessian
  Analysis.FrechetUniqueness Quadratic.Definitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Symmetry of the gradient of the soft minimax of matrices and of its
   derivatives. The derivative of a map with symmetric matrix values is
   symmetric, by uniqueness of the derivative of each entry
   (quadratic_symmetric_frechet). So, when every coefficient coeff y s is
   symmetric, the gradient matrix_nested_gradient and its first and second
   derivatives are symmetric (quadratic_nested_gradient_symmetric,
   quadratic_nested_gradient_derivative_symmetric,
   quadratic_nested_gradient_second_symmetric). *)

Theorem quadratic_symmetric_frechet {E : normedModType R} n
    (F dF : E -> matrix n) (x : E) :
  (forall z, symmetric_matrix n (F z)) -> is_diff x F dF ->
  forall u, symmetric_matrix n (dF u).
Proof.
  intros HS HF u i j Hi Hj.
  assert (Hij : is_diff x
    ((fun z => matrix_entry n (F z) i j) : E -> R^o)
    (fun v => matrix_entry n (dF v) i j)).
  { exact (is_diff_comp HF (matrix_entry_frechet n (F x) i j)). }
  assert (Hji : is_diff x
    ((fun z => matrix_entry n (F z) i j) : E -> R^o)
    (fun v => matrix_entry n (dF v) j i)).
  { have Ez : ((fun z => matrix_entry n (F z) i j) : E -> R^o) =
      ((fun z => matrix_entry n (F z) j i) : E -> R^o).
    { apply: funext => z; apply HS; assumption. }
    rewrite Ez.
    exact (is_diff_comp HF (matrix_entry_frechet n (F x) j i)). }
  exact (scalar_frechet_unique _ _ _ x Hij Hji u).
Qed.

Lemma quadratic_weighted_sum_symmetric n q B I :
  (forall i, In i I -> symmetric_matrix n (B i)) ->
  symmetric_matrix n (matrix_weighted_sum n q B I).
Proof.
  induction I as [|a I IH]; intros HB i j Hi Hj; simpl.
  - rewrite !matrix_entry_zero; reflexivity.
  - rewrite !matrix_entry_add !matrix_entry_scale.
    rewrite (HB a (or_introl (Logic.eq_refl a)) i j Hi Hj).
    rewrite (IH (fun b Hb => HB b (or_intror Hb)) i j Hi Hj); reflexivity.
Qed.

Theorem quadratic_nested_gradient_symmetric n beta gamma offset coeff Y S (A : matrix n) :
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  symmetric_matrix n (matrix_nested_gradient n beta gamma offset coeff Y S A).
Proof.
  intros HC; unfold matrix_nested_gradient, matrix_inner_gradient, matrix_gibbs_mean.
  apply quadratic_weighted_sum_symmetric; intros y Hy.
  apply quadratic_weighted_sum_symmetric; intros s Hs; apply HC; assumption.
Qed.

Theorem quadratic_nested_gradient_derivative_symmetric n beta gamma offset coeff Y S (A U : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  symmetric_matrix n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A U).
Proof.
  intros Hb Hg HY HS HC.
  apply (@quadratic_symmetric_frechet (matrix_NormedModule n) n
    (matrix_nested_gradient n beta gamma offset coeff Y S)
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A) A).
  - intros; apply quadratic_nested_gradient_symmetric; exact HC.
  - apply matrix_nested_gradient_frechet; assumption.
Qed.

Theorem quadratic_nested_gradient_second_symmetric n beta gamma offset coeff Y S (A U V : matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  symmetric_matrix n (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A U V).
Proof.
  intros Hb Hg HY HS HC.
  apply (@quadratic_symmetric_frechet (matrix_NormedModule n) n
    (fun M => matrix_nested_gradient_derivative n beta gamma offset coeff Y S M U)
    (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A U) A).
  - intros; apply quadratic_nested_gradient_derivative_symmetric; assumption.
  - apply matrix_nested_gradient_second_frechet; assumption.
Qed.
