(* Integrability against the Gaussian kernel of continuous functions of
   polynomial growth. If f is continuous and
   Rabs (f x) <= C * (1 + Rabs x ^ p) for all x, then
   f x * gaussian_kernel x and Rabs (f x) * gaussian_kernel x are
   integrable on the line (gaussian_polynomial_integrals_exist): these are
   gaussian_integral_exists f and gaussian_absolutely_integrable f of
   GaussianDefinitions. The integrals are Lebesgue integrals, so the second
   conclusion also follows from the first.

   Both come from the library: a measurable function of polynomial growth
   is integrable under the standard normal law (integrable_normal_poly of
   GaussianAnalysis.normal_integral), and integrability under the law is
   integrability against the kernel (gaussian_integral_exists_normal of
   Gaussian.Kernel). *)

From Stdlib Require Import Reals Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Kernel.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From GaussianAnalysis Require Import normal_integral.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem gaussian_polynomial_integrals_exist (f : R -> R) C p :
  (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  whole_line_integrable (fun x => f x * gaussian_kernel x) /\
  whole_line_integrable (fun x => Rabs (f x) * gaussian_kernel x).
Proof.
move=> HC Hb.
have Hb' x : (`|f x| <= C * (1 + `|x| ^+ p))%R.
  by apply/RleP; rewrite -!RabsE -RpowE.
split; apply/gaussian_integral_exists_normal;
  apply: (integrable_normal_poly (C := C) (k := p)).
- exact: continuous_measurable_fun.
- exact: Hb'.
- apply: continuous_measurable_fun => x.
  exact: (continuous_comp (HC x) (continuous_Rabs (f x))).
- by move=> x; rewrite /= RabsE normr_id.
Qed.
