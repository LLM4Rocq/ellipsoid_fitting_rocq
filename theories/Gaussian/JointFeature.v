(* Gaussian endpoint of the actual interleaved row input.
   Zero-padding the test coordinates avoids a separate marginal-law lemma. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Matrix.Definitions Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions
  Tensor.Definitions Matrix.VectorListDefinitions Quadratic.Definitions
  Goe.Definitions Goe.MatrixBasis Joint.Definitions Row.CoordinateDefinitions
  Row.ArrayDefinitions Gordon.ProcessCovariance Gordon.Scalar Gordon.Bilinear
  Gordon.OperatorNet Gaussian.FeatureCoordinates.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_gaussian_joint_width n := (S n+paper_main_symmetric_dimension n)%nat.
