(* The probability side of the Gaussian expectation: the standard normal law
   of MathComp-Analysis, and integrability and expectation under it. This
   module contains definitions only. It was written on 30 September 2026 for
   the challenge gaussian_probability_bridge of the MathComp-Analysis port.

   The law itself is not defined here. It is MathComp's normal_prob 0 1
   (probability_theory/normal_distribution.v): the measure
   A |-> \int[lebesgue_measure]_(x in A) (normal_pdf 0 1 x)%:E on the Borel
   sets of R, where normal_pdf 0 1 x = expR (- x^2 / 2) / sqrt (2 pi), which
   MathComp-Analysis proves to be a probability measure (its instances
   isMeasure and isProbability, unconditional in the mean and the scale).
   That object is the paper's law N(0, 1) of one coordinate of a sample
   x ~ N(0, I_d), and the challenge relates it to the library's
   gaussian_density, gaussian_integral_exists and gaussian_expectation of
   GaussianDefinitions, which never mention a probability measure.

   The last two definitions below are the probability-side counterparts of
   gaussian_integral_exists and gaussian_expectation, and nothing else:
   - gaussian_law_integrable f says that f is Borel measurable and that
     |f| has a finite integral against the law (MathComp's mu.-integrable,
     which includes measurability).
   - gaussian_law_expectation f is the real value of the integral of f
     against the law: fine (\int[normal_prob 0 1]_x (f x)%:E), where fine
     sends +oo and -oo to 0. It is the expectation E[f(X)] for X ~ N(0, 1)
     when f is integrable, and a value with no intended meaning otherwise,
     as for the integrals of AnalysisIntegralDefinitions.
   Neither renames a definition of the library: gaussian_expectation f is
   the Lebesgue integral of f times the kernel divided by the mass, and the
   challenge is what says that the two agree.

   The variable x of the integral ranges over the carrier of lebesgue_measure,
   the Borel copy of Stdlib's R on which the port states every integral
   (AnalysisIntegralDefinitions). R_scope is opened after the MathComp
   imports, so 0 and 1 in normal_prob 0 1 are Stdlib's. *)
From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
Open Scope R_scope.

(* The standard normal density and law of MathComp-Analysis at Stdlib's R,
   named once. Both are transparent aliases: gaussian_law unfolds to
   normal_prob 0 1, and MathComp finds the measure and probability structure
   of normal_prob 0 1 through the alias, so \int[gaussian_law]_x and
   gaussian_law.-integrable are well formed (checked when the statement
   compiles). The real type is written explicitly because the numerals 0
   and 1 alone do not determine it. *)
Definition gaussian_law_density : R -> R := @normal_pdf R 0 1.

Definition gaussian_law : set (measurableTypeR R) -> \bar R := @normal_prob R 0 1.

Definition gaussian_law_integrable (f : R -> R) : Prop :=
  gaussian_law.-integrable setT (EFin \o f).

Definition gaussian_law_expectation (f : R -> R) : R :=
  fine (\int[gaussian_law]_x (f x)%:E)%E.
