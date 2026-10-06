(* Gaussian integrals on the line for functions of polynomial growth. A
   continuous f with Rabs (f x) <= C * (1 + Rabs x ^ p) is Gaussian
   integrable (gaussian_polynomial_admissible). The n-th moment is
   moment_factor n, which is (n-1)!! for even n and 0 for odd n
   (gaussian_power_moments, gaussian_standard_moments). Integrability is
   the Lebesgue integrability of x |-> f x * gaussian_kernel x over the
   line. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Kernel
  Gaussian.Mass Gaussian.Moments Gaussian.Expectation
  Gaussian.PolynomialIntegrability.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem gaussian_polynomial_admissible (f : R -> R) C p :
  (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  gaussian_integral_exists f /\ gaussian_absolutely_integrable f.
Proof. exact (gaussian_polynomial_integrals_exist f C p). Qed.

Theorem gaussian_power_moments n :
  gaussian_has_integral (fun x => x ^ n) (moment_factor n * gaussian_mass) /\
  gaussian_integral_exists (fun x => x ^ n) /\
  gaussian_absolutely_integrable (fun x => x ^ n) /\
  gaussian_expectation (fun x => x ^ n) = moment_factor n.
Proof.
  pose proof (gaussian_raw_moments gaussian_mass gaussian_kernel_mass_integral n) as HI.
  assert (Hb : forall x, Rabs (x^n) <= 1 * (1 + Rabs x ^ n)).
  { intro x; rewrite <- RPow_abs; lra. }
  destruct (gaussian_polynomial_admissible (fun x => x^n) 1 n
    (gaussian_power_continuous n) Hb) as [He Ha].
  split; [exact HI|]. split; [exact He|]. split; [exact Ha|].
  unfold gaussian_expectation.
  rewrite (gaussian_integral_unique (fun x => x^n) (moment_factor n * gaussian_mass) HI).
  pose proof gaussian_mass_positive; field; lra.
Qed.

Theorem gaussian_standard_moments :
  gaussian_expectation (fun x => x ^ 0) = 1 /\
  gaussian_expectation (fun x => x ^ 1) = 0 /\
  gaussian_expectation (fun x => x ^ 2) = 1 /\
  gaussian_expectation (fun x => x ^ 4) = 3.
Proof.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 0)))) as H0.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 1)))) as H1.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 2)))) as H2.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 4)))) as H4.
  simpl moment_factor in H0, H1, H2, H4; simpl INR in H2, H4.
  repeat split; lra.
Qed.
