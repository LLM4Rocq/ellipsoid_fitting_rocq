(* The smooth tests of the Gaussian comparisons:
   paper_main_gaussian_smooth_test d F DF D2F C r says that F, a function
   of d coordinates, has the partial derivatives DF a and the second partial
   derivatives D2F a b, that all three are jointly continuous, and that they
   satisfy the polynomial bound finite_polynomial_bound d C r. *)
From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions
  Gaussian.Coordinate.DerivativeDefinitions.
Open Scope R_scope.

Record paper_main_gaussian_smooth_test d F DF D2F C r : Prop := {
  pmgs_continuous : finite_joint_continuous d F;
  pmgs_derivative : forall a, (a < d)%coq_nat ->
    finite_coordinate_derivative d a F (DF a);
  pmgs_derivative_continuous : forall a, (a < d)%coq_nat ->
    finite_joint_continuous d (DF a);
  pmgs_second_derivative : forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_coordinate_derivative d b (DF a) (D2F a b);
  pmgs_second_continuous : forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_joint_continuous d (D2F a b);
  pmgs_bound : finite_polynomial_bound d C r F;
  pmgs_derivative_bound : forall a, (a < d)%coq_nat ->
    finite_polynomial_bound d C r (DF a);
  pmgs_second_bound : forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_polynomial_bound d C r (D2F a b)
}.
