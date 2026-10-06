From Stdlib Require Import Reals.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions SoftDefinitions
  MatrixGibbsDefinitions MatrixSecondDefinitions GradientDefinitions GoeDefinitions JointDefinitions.
Open Scope R_scope.

(* The velocity of the interpolation path joint_matrix of JointDefinitions.
   joint_time_velocity n t x z is
     joint_quadratic_input n x / (2 * sqrt t) -
     goe_matrix n z / (2 * sqrt (1-t)),
   the derivative in t, for 0 < t < 1, of joint_matrix n C t x z, which is
   C + sqrt t * joint_quadratic_input n x + sqrt (1-t) * goe_matrix n z
   (joint_matrix_time_derivative of JointTimeCalculus). No MathComp module
   is imported and R_scope is opened last, so the arithmetic is Stdlib's. *)

Definition joint_time_velocity n t (x : vector n) (z : vector (goe_vector_index n)) : matrix n :=
  matrix_add n (matrix_scale n (/(2*sqrt t)) (joint_quadratic_input n x))
    (matrix_scale n (-/(2*sqrt(1-t))) (goe_matrix n z)).
