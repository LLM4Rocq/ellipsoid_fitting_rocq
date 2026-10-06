(* The Gaussian moment generating function of x^2. For t < 1/2,
   exp (t x^2) has Gaussian expectation 1 / sqrt (1 - 2 t)
   (gaussian_quadratic_exponential_expectation), and it is integrable and
   absolutely integrable against the standard Gaussian law. The proof
   reads the expectation as an integral against normal_prob 0 1
   (gaussian_quadratic_exponential_has_integral_gauss of GaussianLawBridge,
   from integral_normal_expR_sqr of the library). The integrals are
   Lebesgue integrals over the line. *)

From Stdlib Require Import Reals Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianMass GaussianExpectation.
From EllipsoidFitting Require GaussianLawBridge.
Open Scope R_scope.

Theorem gaussian_quadratic_exponential_has_integral t :
  t < 1/2 ->
  gaussian_has_integral (fun x => exp (t * (x*x)))
    (gaussian_mass / sqrt (1-2*t)).
Proof. exact (GaussianLawBridge.gaussian_quadratic_exponential_has_integral_gauss t). Qed.

Corollary gaussian_quadratic_exponential_integrable t :
  t < 1/2 -> gaussian_integral_exists (fun x => exp (t * (x*x))).
Proof.
  intro Ht.
  exact (gaussian_has_integral_exists _ _
    (gaussian_quadratic_exponential_has_integral t Ht)).
Qed.

Theorem gaussian_quadratic_exponential_absolute_integrable t :
  t < 1/2 -> gaussian_absolutely_integrable (fun x => exp (t * (x*x))).
Proof.
  intro Ht.
  unfold gaussian_absolutely_integrable.
  replace (fun x => Rabs (exp (t * (x*x)))) with (fun x => exp (t * (x*x))).
  - apply gaussian_quadratic_exponential_integrable; exact Ht.
  - apply functional_extensionality; intro x.
    rewrite Rabs_pos_eq by (apply Rlt_le, exp_pos); reflexivity.
Qed.

Theorem gaussian_quadratic_exponential_expectation t :
  t < 1/2 ->
  gaussian_expectation (fun x => exp (t * (x*x))) = 1 / sqrt (1-2*t).
Proof.
  intro Ht; unfold gaussian_expectation.
  rewrite (gaussian_integral_unique (fun x => exp (t * (x*x)))
    (gaussian_mass / sqrt (1-2*t)) (gaussian_quadratic_exponential_has_integral t Ht)).
  pose proof gaussian_mass_positive.
  assert (Hs : 0 < sqrt (1-2*t)) by (apply sqrt_lt_R0; lra).
  field; split; lra.
Qed.
