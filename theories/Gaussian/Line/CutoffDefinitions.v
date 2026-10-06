(* Gaussian integrals cut off at [-A, A].
   - gaussian_cutoff_integral f A is the oriented integral of
     x |-> f x * gaussian_kernel x from -A to A: the Lebesgue integral over
     [-A, A] when -A <= A, and minus the integral over [A, -A] otherwise.
   - gaussian_cutoff_expectation f A divides it by gaussian_mass.
   - gaussian_cutoff_error_majorant g C A is C / gaussian_mass times
     gaussian_integral g minus gaussian_cutoff_integral g A; when the
     integral of g exists and A >= 0, this difference is the integral of
     g against the kernel outside [-A, A]. *)
From Stdlib Require Import Reals.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
Open Scope R_scope.

Definition gaussian_cutoff_integral (f : R -> R) (A : R) : R :=
  oriented_integral (fun x => f x * gaussian_kernel x) (-A) A.

Definition gaussian_cutoff_expectation (f : R -> R) (A : R) : R :=
  gaussian_cutoff_integral f A / gaussian_mass.

Definition gaussian_cutoff_error_majorant (g : R -> R) (C A : R) : R :=
  (C / gaussian_mass) * (gaussian_integral g - gaussian_cutoff_integral g A).
