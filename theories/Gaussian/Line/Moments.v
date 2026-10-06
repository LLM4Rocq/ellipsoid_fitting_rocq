(* The moments of the Gaussian kernel, the integrals of
   x ^ n * gaussian_kernel x over the line. gaussian_raw_moments: if the
   kernel has integral J, then the moment of order n is moment_factor n * J,
   where moment_factor n is 0 for n odd and 1 * 3 * ... * (n - 1) for n
   even. The hypothesis holds for J = gaussian_mass and for no other J
   (gaussian_kernel_mass_integral of Gaussian.Line.Mass).

   The moments of the standard normal law are normal_moment_even and
   normal_moment_odd of the library (GaussianAnalysis.gauss_moments), and
   whole_line_integral_normal of Gaussian.Line.Kernel carries them over to the
   kernel. The integrals over the line are Lebesgue integrals, so each
   conclusion includes the absolute integrability of the integrand. *)

From Stdlib Require Import Reals Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Line.Kernel
  Gaussian.Line.Mass.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From GaussianAnalysis Require Import normal_integral gauss_moments.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_power_derivative n x :
  @is_derive R R^o R^o x 1 (fun t : R => t ^ S n) (INR (S n) * x ^ n).
Proof. auto_derive. cbn [Nat.pred]; ring. Qed.

Lemma gaussian_power_continuous n (x : R) :
  {for x, continuous (fun t : R => t ^ n)}.
Proof. exact (continuous_Rpow n x). Qed.

Lemma moment_factorSS m : moment_factor m.+2 = INR m.+1 * moment_factor m.
Proof. by []. Qed.

Lemma moment_factor_double k :
  moment_factor k.*2 = (\prod_(i < k) i.*2.+1%:R)%R.
Proof.
elim: k => [|k IH]; first by rewrite big_ord0.
by rewrite doubleS moment_factorSS INRE IH big_ord_recr /= mulrC.
Qed.

Lemma moment_factor_odd k : moment_factor k.*2.+1 = 0.
Proof. by elim: k => [|k IH] //; rewrite doubleS moment_factorSS IH Rmult_0_r. Qed.

Theorem gaussian_raw_moments J :
  whole_line_has_integral gaussian_kernel J ->
  forall n, whole_line_has_integral (fun x => x ^ n * gaussian_kernel x)
    (moment_factor n * J).
Proof.
move=> [_ <-] n; rewrite -/gaussian_mass gaussian_mass_normal_peak.
have Nf : (@normal_prob R 0 1).-integrable [set: measurableTypeR R]
    (EFin \o (fun x : R => x ^ n)).
  apply: (integrable_normal_poly (C := 1) (k := n)) => [|x].
    under eq_fun do rewrite RpowE.
    by apply: measurable_funX; exact: measurable_id.
  by rewrite /= RpowE normrX mul1r lerDr ler01.
have Hf : gaussian_integral_exists (fun x : R => x ^ n).
  exact/gaussian_integral_exists_normal.
split; first exact: Hf.
rewrite (whole_line_integral_normal _ Hf).
under eq_integral do rewrite /= RpowE.
have := odd_double_half n; case: (odd n) => /= E.
  rewrite add1n in E; rewrite -E moment_factor_odd normal_moment_odd /=.
  by rewrite mulr0 Rmult_0_l.
rewrite add0n in E; rewrite -E moment_factor_double normal_moment_even /=.
by rewrite RmultE mulrC.
Qed.
