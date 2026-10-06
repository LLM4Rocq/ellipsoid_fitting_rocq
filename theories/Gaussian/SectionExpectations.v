(* A bound on a Gaussian expectation from a majorant:
   |E[f]| <= c * E[h] when f and h are continuous, |f| <= c * h, and h is
   integrable against the Gaussian kernel
   (gaussian_expectation_majorant_bound). The expectations are Lebesgue
   integrals over the line, read as integrals against the standard normal
   law (Gaussian.NormalLawIntegrals): f is integrable by comparison with
   c * h, and the integral of |f| is at most that of c * h. *)

From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions
  GaussianProbabilityDefinitions Gaussian.NormalLawIntegrals.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_expectation_majorant_bound (f h : R -> R) (c : R) :
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous h}) ->
  (forall x, Rabs (f x) <= c * h x) ->
  gaussian_integral_exists h ->
  Rabs (gaussian_expectation f) <= c * gaussian_expectation h.
Proof.
move=> cf ch fh hI.
have hL : gaussian_law_integrable h by apply/gpb_integrable_iff.
have mf : measurable_fun [set: measurableTypeR R] (EFin \o f).
  by apply/measurable_EFinP; apply: continuous_measurable_fun => x; exact: cf.
have fch x : (`|f x| <= c * h x)%R by apply/RleP; rewrite -RabsE; exact: fh.
have fL : gaussian_law_integrable f.
  apply: (le_integrable measurableT mf _ (integrableZl measurableT c hL)) => x _.
  rewrite /= lee_fin.
  exact: (Order.POrderTheory.le_trans (fch x) (ler_norm _)).
have fI : gaussian_integral_exists f by apply/gpb_integrable_iff.
have Ef := gpb_law_integral f fI; have Eh := gpb_law_integral h hI.
have fin_f : (\int[gaussian_law]_x (f x)%:E)%E \is a fin_num by rewrite Ef.
have fin_h : (\int[gaussian_law]_x (h x)%:E)%E \is a fin_num by rewrite Eh.
have -> : gaussian_expectation f = fine (\int[gaussian_law]_x (f x)%:E)%E.
  by rewrite Ef.
have -> : gaussian_expectation h = fine (\int[gaussian_law]_x (h x)%:E)%E.
  by rewrite Eh.
apply/RleP; rewrite RabsE RmultE -fine_abse // -[c]/(fine c%:E) -fineM //.
apply: fine_le; first by rewrite abse_fin_num.
  by apply: fin_numM.
apply: (Order.POrderTheory.le_trans
  (le_abse_integral _ measurableT (measurable_int _ fL))).
rewrite -integralZl //; apply: le_integral.
- exact: measurableT.
- exact: integrable_abse.
- exact: (integrableZl measurableT c hL).
- by move=> x _; rewrite /= lee_fin; exact: fch.
Qed.
