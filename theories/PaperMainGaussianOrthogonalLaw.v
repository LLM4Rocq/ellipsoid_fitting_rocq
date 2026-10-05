(* Orthogonal invariance of smooth tests under the public product law
   gaussian_product_law d. For any d-by-d loading O and continuous f, the
   map x |-> f(O x), O x = gaussian_covariance_image d d O x, is continuous
   and measurable. If f also has a finite polynomial bound, f(O x) is
   integrable for the law and its law integral is the iterated
   expectation. If the rows of O are orthonormal and f is a C2 test with
   the polynomial bounds of paper_main_gaussian_smooth_test, then
     \int f(O x) d gaussian_product_law d = \int f(x) d gaussian_product_law d.
   This is an identity for such tests only. No rotation law or spectral
   decomposition is used. *)
From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCovariancePath GaussianCovarianceDomains
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainGaussianSmoothCovariance PaperMainGaussianSmoothLaw
  PaperMainGaussianSmoothTail PaperMainGaussianGordonTail PaperMainGaussianOrthogonal.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_gaussian_orthogonal_continuous d O (f : list R -> R) :
  finite_joint_continuous d f ->
  finite_joint_continuous d (fun xs => f (gaussian_covariance_image d d O xs)).
Proof.
move=> Hf; rewrite gaussian_covariance_image_linear.
exact: linear_image_continuous_comp.
Qed.

Theorem paper_main_gaussian_orthogonal_ge_measurable d O (f : list R -> R) c :
  finite_joint_continuous d f ->
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle c (f (gaussian_covariance_image d d O (tval x)))].
Proof.
move=> Hf.
exact: (paper_main_gaussian_smooth_ge_measurable d _ c
  (paper_main_gaussian_orthogonal_continuous d O f Hf)).
Qed.

Theorem paper_main_gaussian_orthogonal_le_measurable d O (f : list R -> R) c :
  finite_joint_continuous d f ->
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle (f (gaussian_covariance_image d d O (tval x))) c].
Proof.
move=> Hf.
exact: (paper_main_gaussian_continuous_le_measurable d _ c
  (paper_main_gaussian_orthogonal_continuous d O f Hf)).
Qed.

Lemma paper_main_gaussian_orthogonal_regular d O (f : list R -> R) C r :
  finite_joint_continuous d f -> finite_polynomial_bound d C r f ->
  exists C', finite_joint_continuous d (fun xs => f (gaussian_covariance_image d d O xs)) /\
    finite_polynomial_bound d C' (r * d)%coq_nat
      (fun xs => f (gaussian_covariance_image d d O xs)).
Proof.
move=> Hf Hb.
have [M [HM HP]] := finite_matrix_bound O d d.
have [Hc Hpb] := gaussian_covariance_image_regular d d O M f C r HM HP Hf Hb.
by exists (C * (1 + M * INR d) ^ (r * d)%coq_nat).
Qed.

Theorem paper_main_gaussian_orthogonal_law_transport d O (f : list R -> R) C r :
  finite_joint_continuous d f -> finite_polynomial_bound d C r f ->
  (gaussian_product_law d).-integrable setT
    (fun x => (f (gaussian_covariance_image d d O (tval x)))%:E) /\
  (\int[gaussian_product_law d]_x (f (gaussian_covariance_image d d O (tval x)))%:E =
    (gaussian_iterated_expectation d
      (fun xs => f (gaussian_covariance_image d d O xs)))%:E)%E.
Proof.
move=> Hf Hb.
have [C' [Hc Hpb]] := paper_main_gaussian_orthogonal_regular d O f C r Hf Hb.
exact: (paper_main_gaussian_law_transport d _ C' (r * d)%coq_nat Hc Hpb).
Qed.
