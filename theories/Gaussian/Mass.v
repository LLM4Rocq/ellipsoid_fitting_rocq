(* The Gaussian kernel is integrable on the line, and its integral
   gaussian_mass is positive (gaussian_kernel_integrable,
   gaussian_kernel_mass_integral, gaussian_mass_positive).

   The constant 1 is integrable under the standard normal law, a
   probability measure, so it is integrable against the kernel
   (gaussian_integral_exists_normal of Gaussian.Kernel), and its integral
   against the kernel is (normal_peak 1)^-1 times its integral under the
   law, which is 1: gaussian_mass = (normal_peak 1)^-1
   (gaussian_mass_normal_peak). Its value sqrt (2 pi) is gpb_mass of
   Gaussian.NormalLawDensity. *)

From Stdlib Require Import Reals Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Gaussian.Kernel.
From mathcomp Require Import measurable_realfun probability normal_distribution.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_integral_exists_one : gaussian_integral_exists (fun _ : R => 1).
Proof.
by apply/gaussian_integral_exists_normal; exact: finite_measure_integrable_cst.
Qed.

Theorem gaussian_kernel_integrable : whole_line_integrable gaussian_kernel.
Proof.
apply: (eq_integrable measurableT _ _ _ gaussian_integral_exists_one) => x _ /=.
by rewrite Rmult_1_l.
Qed.

Lemma gaussian_mass_normal_peak : gaussian_mass = ((normal_peak 1)^-1)%R.
Proof.
have := whole_line_integral_normal _ gaussian_integral_exists_one.
rewrite integral_cst //= probability_setT mule1 /= mulr1 => <-.
by rewrite /gaussian_mass; apply: eq_Rintegral => x _ /=; rewrite mul1r.
Qed.

Theorem gaussian_mass_positive : 0 < gaussian_mass.
Proof.
by apply/RltP; rewrite gaussian_mass_normal_peak invr_gt0 normal_peak1_gt0.
Qed.

Theorem gaussian_kernel_mass_integral :
  whole_line_has_integral gaussian_kernel gaussian_mass.
Proof. by split; first exact: gaussian_kernel_integrable. Qed.
