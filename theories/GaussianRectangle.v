(* Gaussian expectations of a jointly continuous function F of two
   variables, cut off to a rectangle [-A, A] x [-B, B].
   - gaussian_cutoff_density and gaussian_rectangle_density write the cut
     off expectations as oriented integrals against gaussian_density.
   - gaussian_finite_rectangle_fubini: on a rectangle, the two iterated cut
     off expectations of F are equal.
   - gaussian_rectangle_approximation_given_section_continuity: if
     |F x y| <= g x * h y, with g and h continuous, nonnegative and
     integrable against the kernel, and if x |-> E[F x] is continuous and
     bounded by E[h] * g x, then the iterated expectation of F differs from
     its cut off version by at most E[h] times the tail of g outside
     [-A, A] plus E[g] times the tail of h outside [-B, B]
     (gaussian_cutoff_error_majorant).
   - gaussian_vanishing_error_limit: if |J - D A| <= e A for A >= 0 and e A
     tends to 0, then D A tends to J as A tends to +oo.
   The integrals on segments are oriented integrals of continuous functions,
   and the integrals over the line are Lebesgue integrals. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianCutoffDefinitions GaussianKernel
  GaussianMass GaussianExpectation ImproperBounds ImproperDomination ImproperCutoff
  GaussianCutoff RectangleFubini.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_cutoff_expectation_sub (f g : R -> R) A :
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  gaussian_cutoff_expectation (fun x => f x - g x) A =
  gaussian_cutoff_expectation f A - gaussian_cutoff_expectation g A.
Proof.
  intros HC HG. unfold gaussian_cutoff_expectation, gaussian_cutoff_integral.
  replace (oriented_integral (fun x => (f x - g x) * gaussian_kernel x) (-A) A) with
    (oriented_integral (fun x => f x * gaussian_kernel x - g x * gaussian_kernel x) (-A) A).
  2:{ apply rectangle_oriented_ext; intros x Hx; ring. }
  pose proof (rectangle_oriented_minus
    (fun x => f x * gaussian_kernel x) (fun x => g x * gaussian_kernel x) (-A) A
    (continuous_finite_integrable _ (gaussian_weighted_continuous f HC) (-A) A)
    (continuous_finite_integrable _ (gaussian_weighted_continuous g HG) (-A) A)) as HS.
  rewrite HS.
  unfold Rdiv; ring.
Qed.
