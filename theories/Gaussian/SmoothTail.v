(* Measurability of continuous tests under the product law
   gaussian_product_law d: the centered test f (x) - E_d f
   (paper_main_gaussian_smooth_centered) is measurable, and so is the event
   {c <= f (x)} (paper_main_gaussian_smooth_ge_measurable).
   paper_main_gaussian_chernoff_exponent is the identity
     exp ((u / L^2)^2 L^2 / 2) exp (- (u / L^2) u) = exp (- u^2 / (2 L^2))
   of Chernoff's bound at the parameter t = u / L^2. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import Soft.Definitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateTopology Gaussian.CoordinatePolynomialContinuity
  Gaussian.CoordinatePolynomialDomain Analysis.FiniteSumAlgebra
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  Gaussian.SmoothCalculus Gaussian.SmoothCovariance Gaussian.SmoothLaw.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_smooth_centered d (f : list R -> R)
    (x : d.-tuple (measurableTypeR R)) : measurableTypeR R :=
  f (tval x) - gaussian_iterated_expectation d f.

Lemma paper_main_gaussian_smooth_centered_measurable d f :
  finite_joint_continuous d f ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (paper_main_gaussian_smooth_centered d f).
Proof.
move=> Hf.
exact: (gpp_joint_measurable d _
  (paper_main_gaussian_shift_continuous d f (gaussian_iterated_expectation d f) Hf)).
Qed.

Lemma paper_main_gaussian_smooth_ge_measurable d f c :
  finite_joint_continuous d f ->
  measurable [set x : d.-tuple (measurableTypeR R) | Rle c (f (tval x))].
Proof.
move=> Hf.
have HE : [set x : d.-tuple (measurableTypeR R) | Rle c (f (tval x))] =
  paper_main_gaussian_smooth_random d f @^-1` `[c, +oo[.
{ rewrite preimage_itvcy; apply/seteqP; split=> x /=.
  - by move=> H; apply/RleP.
  - by move/RleP. }
rewrite HE.
have H := paper_main_gaussian_smooth_random_measurable d f Hf measurableT
  `[c, +oo[ (measurable_itv _).
by rewrite setTI in H.
Qed.

Lemma paper_main_gaussian_chernoff_exponent L u :
  0 < L ->
  exp ((u / L ^ 2) ^ 2 * L ^ 2 / 2) * exp (- (u / L ^ 2 * u)) =
  exp (- u ^ 2 / (2 * L ^ 2)).
Proof.
intros HL; rewrite <- exp_plus; f_equal.
field; apply Rgt_not_eq; exact HL.
Qed.
