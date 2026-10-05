(* Gaussian endpoint of the actual interleaved row input.
   Zero-padding the test coordinates avoids a separate marginal-law lemma. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum Rstruct normedtype.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  MatrixDefinitions MatrixCoordinates OperatorDefinitions TensorDefinitions
  VectorCoordinateDefinitions QuadraticDefinitions GoeDefinitions GoeSynthesis
  JointDefinitions RowCoordinateDefinitions RowArrayDefinitions
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonBilinear
  PaperMainGordonOperatorNet PaperMainGaussianFeatureCoordinates.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_gaussian_joint_width n := (S n+paper_main_symmetric_dimension n)%nat.
