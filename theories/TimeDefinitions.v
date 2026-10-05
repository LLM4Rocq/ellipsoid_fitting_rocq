From Stdlib Require Import Reals.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions SoftDefinitions
  MatrixGibbsDefinitions MatrixSecondDefinitions GradientDefinitions GoeDefinitions JointDefinitions.
Open Scope R_scope.

(* Port of theories/TimeDefinitions.v from Coquelicot to MathComp-Analysis.

   The original used nothing from Coquelicot directly. Its only Coquelicot
   content came through matrix n, vector n, matrix_add, matrix_scale and
   trace_pair of MatrixDefinitions and OperatorDefinitions, through
   goe_vector_index and goe_matrix of GoeDefinitions, through
   joint_quadratic_input and joint_matrix of JointDefinitions, and through the
   nested Gibbs derivatives of MatrixGibbsDefinitions, MatrixSecondDefinitions
   and GradientDefinitions. Their ports keep the same names, arguments and
   values: matrix_add is the componentwise sum and matrix_scale the
   componentwise scaling of the nested tuples, as Coquelicot's plus and scal
   were. So the import of Coquelicot is dropped, the imports of EllipsoidFitting are
   the same as in the original, and every definition keeps its text.

   No MathComp module is imported here, and R_scope is opened last, so the
   coefficients are Stdlib's arithmetic, as before: -/(2*sqrt t) is
   Ropp (Rinv (2 * sqrt t)), with Stdlib's sqrt, * and 1 - t. *)

Definition joint_time_velocity n t (x : vector n) (z : vector (goe_vector_index n)) : matrix n :=
  matrix_add n (matrix_scale n (/(2*sqrt t)) (joint_quadratic_input n x))
    (matrix_scale n (-/(2*sqrt(1-t))) (goe_matrix n z)).

Definition joint_time_acceleration n t (x : vector n) (z : vector (goe_vector_index n)) : matrix n :=
  matrix_add n (matrix_scale n (-/(4*t*sqrt t)) (joint_quadratic_input n x))
    (matrix_scale n (-/(4*(1-t)*sqrt(1-t))) (goe_matrix n z)).

Definition joint_soft_value n beta gamma offset coeff Y S C t x z : R :=
  soft_minimax beta gamma (matrix_affine_scores n offset coeff (joint_matrix n C t x z)) Y S.

Definition joint_soft_second n beta gamma offset coeff Y S C t x z : R :=
  matrix_nested_second_derivative n beta gamma offset coeff Y S (joint_matrix n C t x z)
    (joint_time_velocity n t x z) (joint_time_velocity n t x z) +
  trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S (joint_matrix n C t x z))
    (joint_time_acceleration n t x z).
