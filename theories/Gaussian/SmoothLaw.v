(* Continuous tests under the exact Gaussian product law. A jointly
   continuous test f of d coordinates is a measurable random variable for
   gaussian_product_law d (paper_main_gaussian_smooth_random_measurable).
   With a polynomial bound it is integrable, and its expectation under that
   law is the iterated Gaussian expectation
   (paper_main_gaussian_law_transport). *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import Soft.Definitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateTopology Gaussian.CoordinatePolynomialContinuity
  Gaussian.CoordinatePolynomialDomain GaussianProbabilityProductDefinitions
  Gaussian.ProductLawIntegrals Analysis.ContinuousTupleMeasurability
  Gaussian.SmoothCalculus Gaussian.SmoothCovariance.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_smooth_random d (f : list R -> R)
    (x : d.-tuple (measurableTypeR R)) : measurableTypeR R := f (tval x).

Lemma paper_main_gaussian_smooth_random_measurable d f :
  finite_joint_continuous d f ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (paper_main_gaussian_smooth_random d f).
Proof. move=> Hf; exact: (gpp_joint_measurable d f Hf). Qed.

Lemma paper_main_gaussian_law_transport d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
move=> Hc Hb.
have [HI [HA _]] := gaussian_coordinate_polynomial_domain d F C p Hc Hb.
apply: (gpp_all_sections d F _ HI HA).
exact: (proj2 (measurable_EFinP _ _) (gpp_joint_measurable d F Hc)).
Qed.

Lemma paper_main_gaussian_shift_continuous d f c :
  finite_joint_continuous d f ->
  finite_joint_continuous d (fun xs => f xs - c).
Proof.
move=> Hf; unfold Rminus.
apply: finite_joint_continuous_add; first exact: Hf.
exact: finite_joint_continuous_constant.
Qed.
