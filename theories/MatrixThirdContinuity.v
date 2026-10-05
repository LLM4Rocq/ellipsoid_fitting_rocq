From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions ThirdDefinitions
  MatrixDefinitions MatrixCoordinates MatrixTrace MatrixGibbsDefinitions MatrixGibbs
  MatrixSecondDefinitions MatrixSecond MatrixThirdDefinitions MatrixThird
  GradientDefinitions MatrixGradient HessianDefinitions MatrixHessian
  ContinuityDefinitions FiniteGibbsContinuity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Continuity in the matrix of the third derivative
   matrix_nested_third_derivative and of the arrays built from it. Every
   statement is continuity at one point A, {for A, continuous f}.
   - tuple_build_continuous, matrix_build_continuous,
     hessian_build_continuous and third_build_continuous: a tuple, a matrix
     or an array whose entries are maps from a topological space continuous
     at A is continuous at A.
   - matrix_nested_third_continuous: matrix_nested_third_derivative is
     continuous in the matrix. So are the arrays built from it,
     matrix_nested_gradient_second_derivative,
     matrix_nested_hessian_derivative and matrix_nested_third_coefficients
     (matrix_gradient_second_continuous,
     matrix_hessian_derivative_continuous and
     matrix_third_coefficients_continuous).
   When E is a concrete type, such as matrix n or R^o, plain apply does not
   find the topology of E by unification: use ssreflect's apply:, as in
   apply: matrix_build_continuous, or give E explicitly. *)

Theorem tuple_build_continuous {E : topologicalType} (V : normedModType R)
    n (F : nat -> E -> V) (A : E) :
  (forall i, (i <= n)%coq_nat -> {for A, continuous (F i)}) ->
  {for A, continuous (fun M => tuple_build V n (fun i => F i M))}.
Proof.
  revert F; induction n as [|n IH]; intros F HF; simpl.
  - apply HF; lia.
  - apply: euclidean_product_pair_continuous.
    + apply HF; lia.
    + apply IH; intros i Hi; apply HF; lia.
Qed.

Theorem matrix_build_continuous {E : topologicalType} n
    (F : nat -> nat -> E -> R) (A : E) :
  (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat -> {for A, continuous (F i j)}) ->
  {for A, continuous (fun M => matrix_build n (fun i j => F i j M))}.
Proof.
  intros HF; unfold matrix_build; apply tuple_build_continuous; intros i Hi.
  apply (tuple_build_continuous R^o n (F i)); intros j Hj; apply HF; assumption.
Qed.

Theorem hessian_build_continuous {E : topologicalType} n
    (F : nat -> nat -> E -> matrix n) (A : E) :
  (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat -> {for A, continuous (F i j)}) ->
  {for A, continuous (fun M => hessian_build n (fun i j => F i j M))}.
Proof.
  intros HF; unfold hessian_build; apply tuple_build_continuous; intros i Hi.
  apply tuple_build_continuous; intros j Hj; apply HF; assumption.
Qed.

Theorem third_build_continuous {E : topologicalType} n
    (F : nat -> nat -> E -> hessian_array n) (A : E) :
  (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat -> {for A, continuous (F i j)}) ->
  {for A, continuous (fun M => third_build n (fun i j => F i j M))}.
Proof.
  intros HF; unfold third_build; apply tuple_build_continuous; intros i Hi.
  apply tuple_build_continuous; intros j Hj; apply HF; assumption.
Qed.

Lemma matrix_affine_score_continuous n offset coeff (A : matrix n) y s :
  {for A, continuous (fun M => matrix_affine_scores n offset coeff M y s)}.
Proof.
  have [HD _] := matrix_affine_score_frechet n offset coeff A y s.
  exact (differentiable_continuous HD).
Qed.

Lemma matrix_inner_value_continuous n gamma offset coeff S (A : matrix n) y :
  0 < gamma -> S <> [] ->
  {for A, continuous (fun M => matrix_inner_values n gamma offset coeff S M y)}.
Proof.
  intros Hg HS.
  have [HD _] := matrix_inner_frechet n gamma offset coeff S A y Hg HS.
  exact (differentiable_continuous HD).
Qed.

Lemma matrix_inner_derivative_continuous n gamma offset coeff S (A U : matrix n) y :
  S <> [] ->
  {for A, continuous (fun M => matrix_inner_derivative n gamma offset coeff S M U y)}.
Proof.
  intros HS; unfold matrix_inner_derivative; apply: gibbs_average_continuous.
  - exact HS.
  - intros; apply matrix_affine_score_continuous.
  - intros; apply: cst_continuous.
Qed.

Lemma matrix_inner_covariance_continuous n gamma offset coeff S (A U V : matrix n) y :
  S <> [] ->
  {for A, continuous (fun M => matrix_inner_covariance n gamma offset coeff S M U V y)}.
Proof.
  intros HS; unfold matrix_inner_covariance; apply: gibbs_covariance_continuous.
  - exact HS.
  - intros; apply matrix_affine_score_continuous.
  - intros; apply: cst_continuous.
  - intros; apply: cst_continuous.
Qed.

Lemma matrix_inner_cumulant_continuous n gamma offset coeff S (A U V W : matrix n) y :
  S <> [] ->
  {for A, continuous (fun M => matrix_inner_cumulant n gamma offset coeff S M U V W y)}.
Proof.
  intros HS; unfold matrix_inner_cumulant; apply: gibbs_cumulant3_continuous.
  - exact HS.
  - intros; apply matrix_affine_score_continuous.
  - intros; apply: cst_continuous.
  - intros; apply: cst_continuous.
  - intros; apply: cst_continuous.
Qed.

Lemma matrix_outer_covariance_continuous n beta gamma offset coeff Y S (A U V W : matrix n) :
  0 < gamma -> Y <> [] -> S <> [] ->
  {for A, continuous (fun M => gibbs_covariance (- beta)
    (matrix_inner_values n gamma offset coeff S M) Y
    (fun y => matrix_inner_covariance n gamma offset coeff S M U V y)
    (matrix_inner_derivative n gamma offset coeff S M W))}.
Proof.
  intros Hg HY HS.
  apply: (@gibbs_covariance_continuous (matrix n) (- beta)
    (fun y M => matrix_inner_values n gamma offset coeff S M y)
    (fun y M => matrix_inner_covariance n gamma offset coeff S M U V y)
    (fun y M => matrix_inner_derivative n gamma offset coeff S M W y) Y A).
  - exact HY.
  - intros; apply matrix_inner_value_continuous; assumption.
  - intros; apply matrix_inner_covariance_continuous; assumption.
  - intros; apply matrix_inner_derivative_continuous; assumption.
Qed.

Theorem matrix_nested_third_continuous n beta gamma offset coeff Y S (A U V W : matrix n) :
  0 < gamma -> Y <> [] -> S <> [] ->
  {for A, continuous
    (fun M => matrix_nested_third_derivative n beta gamma offset coeff Y S M U V W)}.
Proof.
  intros Hg HY HS; unfold matrix_nested_third_derivative.
  apply: continuous_Rplus_fct.
  - apply: continuous_Rminus_fct.
    + apply: continuous_Rmult_fct; [apply: cst_continuous |].
      apply: (@gibbs_average_continuous (matrix n) (- beta)
        (fun y M => matrix_inner_values n gamma offset coeff S M y)
        (fun y M => matrix_inner_cumulant n gamma offset coeff S M U V W y) Y A).
      * exact HY.
      * intros; apply matrix_inner_value_continuous; assumption.
      * intros; apply matrix_inner_cumulant_continuous; assumption.
    + apply: continuous_Rmult_fct; [apply: cst_continuous |].
      apply: continuous_Rplus_fct.
      * apply: continuous_Rplus_fct; apply matrix_outer_covariance_continuous; assumption.
      * apply matrix_outer_covariance_continuous; assumption.
  - apply: continuous_Rmult_fct; [apply: cst_continuous |].
    apply: (@gibbs_cumulant3_continuous (matrix n) (- beta)
      (fun y M => matrix_inner_values n gamma offset coeff S M y)
      (fun y M => matrix_inner_derivative n gamma offset coeff S M U y)
      (fun y M => matrix_inner_derivative n gamma offset coeff S M V y)
      (fun y M => matrix_inner_derivative n gamma offset coeff S M W y) Y A).
    + exact HY.
    + intros; apply matrix_inner_value_continuous; assumption.
    + intros; apply matrix_inner_derivative_continuous; assumption.
    + intros; apply matrix_inner_derivative_continuous; assumption.
    + intros; apply matrix_inner_derivative_continuous; assumption.
Qed.

Theorem matrix_gradient_second_continuous n beta gamma offset coeff Y S (A U V : matrix n) :
  0 < gamma -> Y <> [] -> S <> [] ->
  {for A, continuous
    (fun M => matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S M U V)}.
Proof.
  intros Hg HY HS; unfold matrix_nested_gradient_second_derivative.
  apply: matrix_build_continuous; intros i j Hi Hj.
  apply matrix_nested_third_continuous; assumption.
Qed.

Theorem matrix_hessian_derivative_continuous n beta gamma offset coeff Y S (A W : matrix n) :
  0 < gamma -> Y <> [] -> S <> [] ->
  {for A, continuous
    (fun M => matrix_nested_hessian_derivative n beta gamma offset coeff Y S M W)}.
Proof.
  intros Hg HY HS; unfold matrix_nested_hessian_derivative.
  apply: hessian_build_continuous; intros i j Hi Hj.
  apply matrix_gradient_second_continuous; assumption.
Qed.

Theorem matrix_third_coefficients_continuous n beta gamma offset coeff Y S (A : matrix n) :
  0 < gamma -> Y <> [] -> S <> [] ->
  {for A, continuous (matrix_nested_third_coefficients n beta gamma offset coeff Y S)}.
Proof.
  intros Hg HY HS; unfold matrix_nested_third_coefficients.
  apply: third_build_continuous; intros i j Hi Hj.
  apply matrix_hessian_derivative_continuous; assumption.
Qed.
