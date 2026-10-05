From Stdlib Require Import Reals.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions
  GradientDefinitions HessianDefinitions SecondChaosDefinitions.
Open Scope R_scope.

(* The quadratic matrix map and the nested Gibbs gradient along it.
   - quadratic_matrix n lambda C x is C + lambda (x x^T - I).
   - quadratic_first n lambda x u = lambda (u x^T + x u^T) is its derivative
     in x in the direction u, and quadratic_second n lambda u v =
     lambda (u v^T + v u^T) its second derivative.
   - quadratic_gradient is the nested Gibbs gradient at quadratic_matrix.
     quadratic_gradient_first and quadratic_gradient_second are its first
     and second derivatives in x by the chain rule, through the nested
     Hessian and its derivative; QuadraticGradient proves them. *)

Definition quadratic_matrix n (lambda : R) (C : matrix n) (x : vector n) : matrix n :=
  matrix_build n (fun i j => matrix_entry n C i j + lambda *
    (vector_entry n x i * vector_entry n x j - (if Nat.eqb i j then 1 else 0))).

Definition quadratic_first n (lambda : R) (x u : vector n) : matrix n :=
  matrix_build n (fun i j => lambda *
    (vector_entry n u i * vector_entry n x j + vector_entry n x i * vector_entry n u j)).

Definition quadratic_second n (lambda : R) (u v : vector n) : matrix n :=
  matrix_build n (fun i j => lambda *
    (vector_entry n u i * vector_entry n v j + vector_entry n v i * vector_entry n u j)).

Definition quadratic_gradient n beta gamma offset coeff Y S lambda C (x : vector n) :=
  matrix_nested_gradient n beta gamma offset coeff Y S (quadratic_matrix n lambda C x).
Definition quadratic_gradient_first n beta gamma offset coeff Y S lambda C (x u : vector n) :=
  hessian_action n
    (matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C x))
    (quadratic_first n lambda x u).
Definition quadratic_gradient_second n beta gamma offset coeff Y S lambda C (x u v : vector n) :=
  matrix_add n
    (hessian_action n
      (matrix_nested_hessian_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_first n lambda x v))
      (quadratic_first n lambda x u))
    (hessian_action n
      (matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C x))
      (quadratic_second n lambda u v)).
