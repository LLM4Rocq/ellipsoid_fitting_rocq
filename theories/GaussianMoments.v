(* The moments of the Gaussian kernel, the integrals of
   x ^ n * gaussian_kernel x over the line.
   - gaussian_moment_recurrence: if the moment of order n is L, then the
     moment of order n + 2 is (n + 1) * L. This is Stein's identity
     gaussian_stein_polynomial_split for f t = t ^ (n + 1).
   - gaussian_raw_moments: if the kernel has integral J, then the moment of
     order n is moment_factor n * J, where moment_factor n is 0 for n odd
     and 1 * 3 * ... * (n - 1) for n even. The hypothesis holds for
     J = gaussian_mass and for no other J (gaussian_kernel_mass_integral of
     GaussianMass).
   - gaussian_first_raw_moment: the moment of order 1 is 0.
   The integrals over the line are Lebesgue integrals, so each conclusion
   includes the absolute integrability of the integrand. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianDecay GaussianStein
  GaussianSteinPolynomial.
From EllipsoidFitting Require Import GaussianFubiniLebesgue.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_power_derivative n x :
  @is_derive R R^o R^o x 1 (fun t : R => t ^ S n) (INR (S n) * x ^ n).
Proof. auto_derive. cbn [Nat.pred]; ring. Qed.

Lemma gaussian_power_continuous n (x : R) :
  {for x, continuous (fun t : R => t ^ n)}.
Proof. exact (continuous_Rpow n x). Qed.

Theorem gaussian_moment_recurrence n L :
  whole_line_has_integral (fun x => x ^ n * gaussian_kernel x) L ->
  whole_line_has_integral (fun x => x ^ S (S n) * gaussian_kernel x)
    (INR (S n) * L).
Proof.
  intro HL.
  change (whole_line_has_integral (fun x => x * x ^ S n * gaussian_kernel x)
    (INR (S n) * L)).
  apply (gaussian_stein_polynomial_split (fun x => x ^ S n)
    (fun x => INR (S n) * x ^ n) 1 (S n) (INR (S n) * L)).
  - exact (gaussian_power_derivative n).
  - intro x.
    apply (continuous_mult R).
    + apply (continuous_const R).
    + apply gaussian_power_continuous.
  - intro x; rewrite <- RPow_abs; lra.
  - have E : (fun t => INR (S n) * t ^ n * gaussian_kernel t) =
        (fun t => INR (S n) * (t ^ n * gaussian_kernel t)).
    { apply/funext => t; ring. }
    rewrite E.
    destruct HL as [Hi Hl]; split.
    + exact (fubini_integrable_scale setT (fun x => x ^ n * gaussian_kernel x)
        (INR (S n)) measurableT Hi).
    + rewrite (fubini_integral_scale_l (fun x => x ^ n * gaussian_kernel x)
        (INR (S n)) Hi) Hl; reflexivity.
Qed.

Theorem gaussian_raw_moments J :
  whole_line_has_integral gaussian_kernel J ->
  forall n, whole_line_has_integral (fun x => x ^ n * gaussian_kernel x)
    (moment_factor n * J).
Proof.
  intro HJ.
  assert (Hp : forall n,
    whole_line_has_integral (fun x => x ^ n * gaussian_kernel x)
      (moment_factor n * J) /\
    whole_line_has_integral (fun x => x ^ S n * gaussian_kernel x)
      (moment_factor (S n) * J)).
  { intro n; induction n as [|n [Hn HSn]].
    - split.
      + simpl; rewrite Rmult_1_l.
        have E : (fun x : R => 1 * gaussian_kernel x) = gaussian_kernel.
        { apply/funext => x; ring. }
        rewrite E; exact HJ.
      + simpl; rewrite Rmult_0_l.
        have E : (fun x : R => x * 1 * gaussian_kernel x) =
            (fun x => x * gaussian_kernel x).
        { apply/funext => x; ring. }
        rewrite E; exact gaussian_first_moment_zero.
    - split; [exact HSn |].
      change (whole_line_has_integral (fun x => x ^ S (S n) * gaussian_kernel x)
        ((INR (S n) * moment_factor n) * J)).
      rewrite Rmult_assoc.
      exact (gaussian_moment_recurrence n (moment_factor n * J) Hn). }
  intro n; exact (proj1 (Hp n)).
Qed.
