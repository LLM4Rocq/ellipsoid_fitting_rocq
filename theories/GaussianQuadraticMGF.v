(* Port of theories/GaussianQuadraticMGF.v from Coquelicot to
   MathComp-Analysis.

   Every lemma, theorem and corollary of the original keeps its name and its
   arguments, in the same order. gaussian_has_integral,
   gaussian_integral_exists, gaussian_absolutely_integrable,
   gaussian_expectation, gaussian_mass and gaussian_density come from the
   ported GaussianDefinitions, where they are stated with the Lebesgue
   integral over the line (difference 4 of analysis/README.md). The
   arithmetic in every statement is Stdlib's, as in the original.

   One statement changes form.

   1. gaussian_quadratic_exponential_density_integral concludes
      whole_line_has_integral (fun x => exp (t * (x*x)) * gaussian_density x)
        (1 / sqrt (1-2*t))
      in place of Coquelicot's
      is_RInt_gen (fun x => exp (t * (x*x)) * gaussian_density x)
        (Rbar_locally m_infty) (Rbar_locally p_infty) (1 / sqrt (1-2*t)).
      This is the translation of the vocabulary table, and the form of the
      last clause of the restated challenge ellipsoid_gaussian_mgf
      (analysis/challenges/ellipsoid_gaussian_mgf). The integrand is
      continuous and positive, so the two readings say the same thing.

   The other statements keep their text; their meaning follows the ported
   definitions. For t < 1/2 the product exp (t * (x*x)) * gaussian_kernel x
   is continuous, positive and absolutely integrable, so the Lebesgue and the
   improper Riemann readings agree.

   What changes in the proofs. The original rewrote integrands under
   Coquelicot's is_RInt_gen with is_RInt_gen_ext. The port rewrites them with
   Stdlib's functional_extensionality, whose axiom
   functional_extensionality_dep is one of the seven of analysis/README.md.
   gaussian_quadratic_exponential_has_integral applies
   gaussian_scaled_kernel_integral of the ported GaussianScaling, which is
   stated with whole_line_has_integral. gaussian_quadratic_exponential_integrable
   takes the integrability part of it, since gaussian_integral_exists is no
   longer an existential. gaussian_quadratic_exponential_density_integral
   scales the integral by / gaussian_mass with gaussian_has_integral_scale of
   the ported GaussianExpectation, in place of Coquelicot's is_RInt_gen_scal.

   The original imported Classical_Prop but did not use it. This port does
   not import it, and imports no MathComp module, so the names of the
   statements are Stdlib's. The assumptions of the module are the seven
   axioms of analysis/README.md. *)

From Stdlib Require Import Reals Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianMass GaussianExpectation GaussianScaling.
Open Scope R_scope.

Lemma gaussian_quadratic_tilt_kernel t x :
  t < 1/2 ->
  exp (t * (x*x)) * gaussian_kernel x =
    gaussian_kernel (sqrt (1-2*t) * x).
Proof.
  intro Ht.
  assert (Hsq : sqrt (1-2*t) * sqrt (1-2*t) = 1-2*t).
  { apply sqrt_def; lra. }
  unfold gaussian_kernel; rewrite <- exp_plus; f_equal.
  replace ((sqrt (1-2*t)*x)*(sqrt (1-2*t)*x)) with
    ((sqrt (1-2*t)*sqrt (1-2*t))*(x*x)) by ring.
  rewrite Hsq; field.
Qed.

Theorem gaussian_quadratic_exponential_has_integral t :
  t < 1/2 ->
  gaussian_has_integral (fun x => exp (t * (x*x)))
    (gaussian_mass / sqrt (1-2*t)).
Proof.
  intro Ht; unfold gaussian_has_integral.
  replace (fun x => exp (t * (x*x)) * gaussian_kernel x) with
    (fun x => gaussian_kernel (sqrt (1-2*t)*x)).
  - apply gaussian_scaled_kernel_integral, sqrt_lt_R0; lra.
  - apply functional_extensionality; intro x.
    symmetry; apply gaussian_quadratic_tilt_kernel; exact Ht.
Qed.

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
