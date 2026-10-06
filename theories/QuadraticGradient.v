From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions GradientDefinitions
  MatrixGradient MatrixThirdDefinitions MatrixThird HessianDefinitions MatrixHessian CoefficientMaps
  SecondChaosDefinitions QuadraticDefinitions QuadraticCalculus.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Derivatives in x of the nested gradient at
   quadratic_matrix n lambda C x = C + lambda (x x^T - I), for
   beta, gamma > 0 and nonempty Y and S.
   - quadratic_gradient_frechet: quadratic_gradient is differentiable at x,
     with differential quadratic_gradient_first x.
   - quadratic_gradient_first_frechet: z |-> quadratic_gradient_first z u is
     differentiable at x, with differential quadratic_gradient_second x u.
   - quadratic_gradient_second_basis: along chaos_basis n a and
     chaos_basis n b, the second derivative is lambda times the derivative
     of matrix_nested_gradient in the direction chaos_second n a b, plus
     lambda ^ 2 times its second derivative in the directions
     chaos_first n x a and chaos_first n x b, both at the point
     quadratic_matrix n lambda C x.
   - quadratic_hessian_biscalar: scalars on the Hessian array and on the
     direction come out of hessian_action as their product.
   Differentiability is MathComp's is_diff, for the Euclidean norm of
   vector n and the Frobenius norm of matrix n. The scalar multiplication
   (a *: H)%R of hessian_array n is entrywise. The proofs use MathComp's
   linearZ_LR on maps packed as {linear _ -> _}. *)

Theorem quadratic_gradient_frechet n beta gamma offset coeff Y S lambda C (x : vector n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff x (quadratic_gradient n beta gamma offset coeff Y S lambda C)
    (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x).
Proof.
  intros Hb Hg HY HS; unfold quadratic_gradient, quadratic_gradient_first.
  have HC := is_diff_comp (quadratic_matrix_frechet n lambda C x)
    (matrix_nested_gradient_frechet n beta gamma offset coeff Y S Hb Hg HY HS
      (quadratic_matrix n lambda C x)).
  apply: (is_diff_eq HC).
  apply: funext => u.
  symmetry.
  exact (matrix_nested_hessian_action n beta gamma offset coeff Y S
    (quadratic_matrix n lambda C x) (quadratic_first n lambda x u) Hb Hg HY HS).
Qed.

Theorem quadratic_gradient_first_frechet n beta gamma offset coeff Y S lambda C (x u : vector n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff x (fun z => quadratic_gradient_first n beta gamma offset coeff Y S lambda C z u)
    (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x u).
Proof.
  intros Hb Hg HY HS; unfold quadratic_gradient_first, quadratic_gradient_second.
  apply (@quadratic_hessian_product_frechet (vector_NormedModule n) n
    (fun z => matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C z))
    (fun v => matrix_nested_hessian_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (quadratic_first n lambda x v))
    (fun z => quadratic_first n lambda z u) (quadratic_second n lambda u) x).
  - exact (is_diff_comp (quadratic_matrix_frechet n lambda C x)
      (matrix_nested_hessian_frechet n beta gamma offset coeff Y S Hb Hg HY HS
        (quadratic_matrix n lambda C x))).
  - apply quadratic_first_frechet.
Qed.

Theorem quadratic_hessian_biscalar n (H : hessian_array n) (M : matrix n) a b :
  hessian_action n (a *: H)%R (matrix_scale n b M) =
  matrix_scale n (a * b) (hessian_action n H M).
Proof.
  unfold matrix_scale.
  (* hessian_action is linear in the direction and in the array
     (CoefficientMaps). *)
  pose L1 : {linear matrix_NormedModule n -> matrix_NormedModule n} :=
    HB.pack (hessian_action n (a *: H)%R)
      (GRing.isLinear.Build R _ _ *:%R (hessian_action n (a *: H)%R)
        (proj1 (hessian_action_linear_direction n (a *: H)%R))).
  pose L2 : {linear hessian_NormedModule n -> matrix_NormedModule n} :=
    HB.pack (fun G : hessian_array n => hessian_action n G M)
      (GRing.isLinear.Build R _ _ *:%R (fun G : hessian_array n => hessian_action n G M)
        (proj1 (hessian_action_linear_array n M))).
  have HZ1 : forall (c : R) (X : matrix n),
    hessian_action n (a *: H)%R (c *: X)%R = (c *: hessian_action n (a *: H)%R X)%R.
  { intros c X; exact (linearZ_LR L1 c X). }
  have HZ2 : forall (c : R) (G : hessian_array n),
    hessian_action n (c *: G)%R M = (c *: hessian_action n G M)%R.
  { intros c G; exact (linearZ_LR L2 c G). }
  rewrite HZ1 HZ2 scalerA.
  congr (_ *: _)%R.
  rewrite -RmultE; apply Rmult_comm.
Qed.

Theorem quadratic_gradient_second_basis n beta gamma offset coeff Y S lambda C
    (x : vector n) a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  quadratic_gradient_second n beta gamma offset coeff Y S lambda C x (chaos_basis n a) (chaos_basis n b) =
  matrix_add n
    (matrix_scale n lambda (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_second n a b)))
    (matrix_scale n (lambda ^ 2) (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_first n x a) (chaos_first n x b))).
Proof.
  intros Hb Hg HY HS; unfold quadratic_gradient_second.
  rewrite !quadratic_first_basis quadratic_second_basis.
  assert (HH : matrix_nested_hessian_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (matrix_scale n lambda (chaos_first n x b)) =
    (lambda *: matrix_nested_hessian_derivative n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C x) (chaos_first n x b))%R).
  { (* The derivative of matrix_nested_hessian is linear, since it is the
       differential of an is_diff statement (matrix_third_is_diff_linear). *)
    pose L : {linear matrix_NormedModule n -> hessian_NormedModule n} :=
      HB.pack (matrix_nested_hessian_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x))
        (GRing.isLinear.Build R _ _ *:%R
          (matrix_nested_hessian_derivative n beta gamma offset coeff Y S
            (quadratic_matrix n lambda C x))
          (proj1 (matrix_third_is_diff_linear _ _ _
            (matrix_nested_hessian_frechet n beta gamma offset coeff Y S Hb Hg HY HS
              (quadratic_matrix n lambda C x))))).
    exact (linearZ_LR L lambda (chaos_first n x b)). }
  rewrite HH quadratic_hessian_biscalar.
  rewrite (matrix_nested_hessian_derivative_action _ _ _ _ _ _ _ _ _ _ Hb Hg HY HS).
  assert (HL : hessian_action n
    (matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C x))
    (matrix_scale n lambda (chaos_second n a b)) =
    matrix_scale n lambda (hessian_action n
      (matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C x))
      (chaos_second n a b))).
  { pose L : {linear matrix_NormedModule n -> matrix_NormedModule n} :=
      HB.pack (hessian_action n
        (matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)))
        (GRing.isLinear.Build R _ _ *:%R
          (hessian_action n
            (matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C x)))
          (proj1 (hessian_action_linear_direction n _))).
    exact (linearZ_LR L lambda (chaos_second n a b)). }
  rewrite HL (matrix_nested_hessian_action _ _ _ _ _ _ _ _ _ Hb Hg HY HS).
  apply matrix_ext; intros i j Hi Hj.
  rewrite !matrix_entry_add !matrix_entry_scale; ring.
Qed.
