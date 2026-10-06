(* Transfer to the product law of the clipped Gaussian smoothings of a
   Euclidean-Lipschitz test F, in the form used by the limit bound for
   centered exponentials: on samples x : d.-tuple, the approximants
   A_n (tval x) are measurable and converge to F (tval x); their iterated
   Gaussian means converge to the mean of F; and these means are the
   integrals for gaussian_product_law d. The envelope is integrable for
   that law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import Soft.Definitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gaussian.Iterated.Definitions
  Gaussian.Iterated.Expectation Analysis.CoordinateTopology
  Gaussian.Coordinate.PolynomialContinuity Gaussian.Coordinate.Weights
  GaussianProbabilityProductDefinitions Gaussian.Law.ProductIntegrals
  Analysis.ContinuousTupleMeasurability Gaussian.Smooth.Calculus
  Gaussian.Smooth.Law Gordon.Lipschitz Gaussian.Lipschitz.EuclideanNorm
  Gaussian.Lipschitz.Clip Gaussian.Lipschitz.Growth.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_gaussian_lipschitz_law d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
move=> HL HLip.
exact: (paper_main_gaussian_law_transport d F _ 2
  (paper_main_gaussian_lipschitz_continuous d F L HL HLip)
  (paper_main_gaussian_lipschitz_polynomial_bound d F L HL HLip)).
Qed.
