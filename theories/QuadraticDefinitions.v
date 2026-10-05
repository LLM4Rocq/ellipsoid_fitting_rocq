From Stdlib Require Import Reals.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions
  GradientDefinitions HessianDefinitions SecondChaosDefinitions.
Open Scope R_scope.

(* Port of theories/QuadraticDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly.
   Its Coquelicot content came only through the types matrix n and vector n
   and the operations matrix_build, matrix_entry, vector_entry and
   matrix_add of MatrixDefinitions and OperatorDefinitions, through
   hessian_action and the nested Hessians of HessianDefinitions, and through
   matrix_nested_gradient of GradientDefinitions. Their ports keep the same
   names, arguments and values: a vector is still a nested tuple of reals
   and a matrix a nested tuple of vectors, and matrix_add is still the
   entrywise sum. So the import of Coquelicot is dropped and the text of
   every definition is unchanged. MathComp is not imported here, so the
   arithmetic, the literals 1 and 0 and the test Nat.eqb are Stdlib's, as
   before. The meaning of every definition is unchanged.

   The types vector n and matrix n keep Coquelicot's Euclidean and Frobenius
   norms, through euclidean_product of MatrixEuclideanProduct, and so the
   same topology. A statement that one of these maps has a given derivative,
   written with MathComp's is_diff x f df in place of Coquelicot's
   filterdiff f (locally x) df, therefore says the same thing as before. *)

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
