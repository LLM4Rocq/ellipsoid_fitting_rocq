(* Port of theories/GaussianCutoffDefinitions.v from Coquelicot to
   MathComp-Analysis. The three definitions keep their names, arguments and
   text, with one change: Coquelicot's oriented Riemann integral
     RInt (fun x => f x * gaussian_kernel x) (-A) A
   becomes
     oriented_integral (fun x => f x * gaussian_kernel x) (-A) A
   of AnalysisIntegralDefinitions, the Lebesgue integral over [-A, A] when
   -A <= A and minus the integral over [A, -A] otherwise (difference 3 of
   analysis/README.md). For a continuous integrand and -A <= A the value is
   Coquelicot's. The Coquelicot import is dropped. *)
From Stdlib Require Import Reals.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
Open Scope R_scope.

Definition gaussian_cutoff_integral (f : R -> R) (A : R) : R :=
  oriented_integral (fun x => f x * gaussian_kernel x) (-A) A.

Definition gaussian_cutoff_expectation (f : R -> R) (A : R) : R :=
  gaussian_cutoff_integral f A / gaussian_mass.

Definition gaussian_cutoff_error_majorant (g : R -> R) (C A : R) : R :=
  (C / gaussian_mass) * (gaussian_integral g - gaussian_cutoff_integral g A).
