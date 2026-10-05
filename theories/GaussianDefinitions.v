(* The standard Gaussian weight and its integrals. Port of
   theories/GaussianDefinitions.v from Coquelicot to MathComp-Analysis.

   gaussian_kernel, gaussian_stein_integrand, gaussian_expectation,
   gaussian_density and moment_factor have the same text as in theories/.
   The integrals now come from AnalysisIntegralDefinitions, which states them
   with the Lebesgue integral.
   - gaussian_primitive x is still the oriented integral of the kernel from 0
     to x, negative for x < 0. The kernel is continuous, so its value is the
     same as with Coquelicot's RInt.
   - gaussian_mass is the integral of the kernel over the line. The kernel is
     absolutely integrable, so its value is the same as with RInt_gen.
   - gaussian_integral, gaussian_has_integral and gaussian_integral_exists use
     the Lebesgue integral of x |-> f x * gaussian_kernel x over the line in
     place of Coquelicot's improper Riemann integral (difference 4 of
     analysis/README.md). gaussian_integral_exists f now says that this
     product is Borel measurable and absolutely integrable. It no longer
     holds for a product whose improper integral converges without absolute
     convergence, and it now holds for some products that are not Riemann
     integrable on a segment. Since the kernel is positive and measurable,
     the product is measurable exactly when f is.
   - gaussian_absolutely_integrable keeps its text. With the Lebesgue
     integral it follows from gaussian_integral_exists, and the converse needs
     f to be measurable.
   - gaussian_integral f is 0 when f is measurable and the product is not
     integrable; see AnalysisIntegralDefinitions for the other values off the
     domain.
   - Some lemmas of theories/ become false with this meaning and need an
     added hypothesis when they are ported. Each concludes that a signed
     integrand involving the highest derivative of f has a whole-line
     integral, and bounds neither that derivative nor the integrand. Besides
     differentiability and continuity, it assumes only limits of a primitive
     at -oo and +oo, or bounds on f and its lower derivatives. The lemmas
     are gaussian_stein_improper_decay and gaussian_stein_improper
     (GaussianKernel), gaussian_stein_second_decay (GaussianStein),
     gaussian_stein_polynomial and gaussian_stein_second_polynomial
     (GaussianSteinPolynomial), and their copies in GaussianCoordinateProofs.
     For example f x = sin (exp (x * x)) is bounded and has a continuous
     derivative df, but
     df x * gaussian_kernel x is not absolutely integrable, so
     gaussian_stein_integrand f df has no Lebesgue integral over the line.
     The ported lemmas must also assume that the integrand is integrable on
     the line. The challenge statements bound every derivative that they
     integrate by a polynomial, which gives that hypothesis. For a
     nonnegative continuous integrand the conclusion still holds, by
     monotone convergence. *)

From Stdlib Require Import Reals.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
Open Scope R_scope.

Definition gaussian_kernel (x : R) : R := exp (- (x * x) / 2).

Definition gaussian_stein_integrand (f df : R -> R) (x : R) : R :=
  df x * gaussian_kernel x - x * f x * gaussian_kernel x.

Definition gaussian_primitive (x : R) : R :=
  oriented_integral gaussian_kernel 0 x.

Definition gaussian_mass : R := whole_line_integral gaussian_kernel.

Definition gaussian_integral (f : R -> R) : R :=
  whole_line_integral (fun x => f x * gaussian_kernel x).

Definition gaussian_has_integral (f : R -> R) (l : R) : Prop :=
  whole_line_has_integral (fun x => f x * gaussian_kernel x) l.

Definition gaussian_integral_exists (f : R -> R) : Prop :=
  whole_line_integrable (fun x => f x * gaussian_kernel x).

Definition gaussian_absolutely_integrable (f : R -> R) : Prop :=
  gaussian_integral_exists (fun x => Rabs (f x)).

Definition gaussian_expectation (f : R -> R) : R :=
  gaussian_integral f / gaussian_mass.

Definition gaussian_density (x : R) : R := gaussian_kernel x / gaussian_mass.

Fixpoint moment_factor (n : nat) : R :=
  match n with
  | O => 1
  | S O => 0
  | S (S m) => INR (S m) * moment_factor m
  end.
