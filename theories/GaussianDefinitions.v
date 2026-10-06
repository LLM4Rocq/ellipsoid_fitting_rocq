(* The standard Gaussian weight and its integrals. The integrals are those
   of AnalysisIntegralDefinitions, that is Lebesgue integrals.
   - gaussian_kernel x = exp (- x^2 / 2), and gaussian_primitive x is its
     oriented integral from 0 to x, negative for x < 0.
   - gaussian_mass is the integral of the kernel over the line,
     sqrt (2 pi) (gpb_mass of GaussianProbabilityDensity).
   - gaussian_integral, gaussian_has_integral and gaussian_integral_exists
     use the Lebesgue integral of x |-> f x * gaussian_kernel x over the
     line. gaussian_integral_exists f says that this product is Borel
     measurable and absolutely integrable. It does not hold for a product
     whose improper Riemann integral converges without absolute convergence,
     and it holds for some products that are not Riemann integrable on a
     segment. Since the kernel is positive and measurable, the product is
     measurable exactly when f is.
   - gaussian_absolutely_integrable f says the same of Rabs f. It follows
     from gaussian_integral_exists f, and the converse needs f to be
     measurable.
   - gaussian_integral f is 0 when f is measurable and the product is not
     integrable; see AnalysisIntegralDefinitions for the other values off the
     domain.
   - gaussian_expectation f is gaussian_integral f / gaussian_mass, and
     gaussian_density is the kernel divided by the mass. moment_factor n is
     the n-th moment of the standard normal law: 0 for n odd and
     1 * 3 * ... * (n - 1) for n even.
   Since integrability is absolute, an identity that integrates the highest
   derivative of f, such as Stein's identity E [f'] = E [x f], needs the
   integrability of that integrand as a hypothesis when it bounds neither
   the derivative nor the integrand. For example f x = sin (exp (x * x)) is
   bounded and has a continuous derivative df, but df x * gaussian_kernel x
   is not absolutely integrable, so gaussian_stein_integrand f df has no
   Lebesgue integral over the line. A polynomial bound on every derivative
   that is integrated gives that hypothesis. For a nonnegative continuous
   integrand the conclusion still holds, by monotone convergence. *)

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
