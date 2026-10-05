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

Theorem paper_main_gaussian_orthogonal_measurable d O (f : list R -> R) :
  finite_joint_continuous d f ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    ((fun x => f (gaussian_covariance_image d d O (tval x))) : _ -> measurableTypeR R).
Proof.
move=> Hf.
exact: (gpp_joint_measurable d _ (paper_main_gaussian_orthogonal_continuous d O f Hf)).
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

Theorem paper_main_gaussian_orthogonal_law_expectation d O f Df D2f C r :
  paper_main_gaussian_orthonormal_rows d O ->
  paper_main_gaussian_smooth_test d f Df D2f C r ->
  (gaussian_product_law d).-integrable setT
    (fun x => (f (gaussian_covariance_image d d O (tval x)))%:E) /\
  (gaussian_product_law d).-integrable setT (fun x => (f (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (f (gaussian_covariance_image d d O (tval x)))%:E =
    \int[gaussian_product_law d]_x (f (tval x))%:E)%E.
Proof.
move=> HO Hs.
have Hs' := Hs; case: Hs' => Hc _ _ _ _ Hb _ _.
have [HI HE] := paper_main_gaussian_orthogonal_law_transport d O f C r Hc Hb.
have [HI' HE'] := paper_main_gaussian_law_transport d f C r Hc Hb.
split; first exact: HI.
split; first exact: HI'.
by rewrite HE HE' (paper_main_gaussian_orthogonal_smooth_expectation d O f Df D2f C r HO Hs).
Qed.

Corollary paper_main_gaussian_orthogonal_law_pair d O1 O2 f Df D2f C r :
  paper_main_gaussian_orthonormal_rows d O1 ->
  paper_main_gaussian_orthonormal_rows d O2 ->
  paper_main_gaussian_smooth_test d f Df D2f C r ->
  (\int[gaussian_product_law d]_x (f (gaussian_covariance_image d d O1 (tval x)))%:E =
    \int[gaussian_product_law d]_x (f (gaussian_covariance_image d d O2 (tval x)))%:E)%E.
Proof.
move=> H1 H2 Hs.
rewrite (proj2 (proj2 (paper_main_gaussian_orthogonal_law_expectation d O1 f Df D2f C r H1 Hs))).
by rewrite (proj2 (proj2 (paper_main_gaussian_orthogonal_law_expectation d O2 f Df D2f C r H2 Hs))).
Qed.
