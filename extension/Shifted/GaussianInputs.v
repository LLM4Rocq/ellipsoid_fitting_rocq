(* Gaussian specializations of the mixture inputs for shifted ellipsoid
   fitting. The normal law has fourth moment 3 and admissible subgaussian
   constant 2: its exponential moment at that constant is exactly sqrt 2.
   The one-component family therefore satisfies the hypotheses of the
   finite-mixture interpolation and condition-number theorems. Its sample
   probability agrees with the original frozen Gaussian sample law.

   These are supporting lemmas, not a statement of the shifted theorem.
   Source: doc/shifted-gaussian.tex, Gaussian input requirements; the
   moments and exponential moment are the existing library results
   normal_moment_even and integral_normal_expR_sqr. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences exp.
From GaussianAnalysis.gaussian Require Import gauss_moments.
From GaussianAnalysis.comparison Require Import chi_square.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Mixture Require Import Component OneComponent.
From EllipsoidUniversality.Model Require Import Rows.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma gaussian_subgaussian_expectation :
  ('E_gaussian_law_probability[universality_subgaussian_test 2%:R])%E =
  (Num.sqrt (2 : RR))%:E.
Proof.
rewrite unlock /universality_subgaussian_test /gaussian_law_probability.
under eq_integral do rewrite mulrC.
have ht : 2 * (2 ^+ 2)^-1 * 1 ^+ 2 < (1 : RR).
  have -> : 2 * (2 ^+ 2)^-1 * 1 ^+ 2 = (2 : RR)^-1 by field.
  by rewrite invf_lt1 ?ltr0n // ltr1n.
rewrite integral_normal_expR_sqr ?oner_eq0 //.
have -> : 1 - 2 * (2 ^+ 2)^-1 * 1 ^+ 2 = (2 : RR)^-1 by field.
by rewrite sqrtrV ?ler0n // invrK.
Qed.

Lemma gaussian_coordinate_law :
  universality_coordinate_law 3%:R 2%:R gaussian_law_probability.
Proof.
split; first by rewrite ltr0n.
split.
  rewrite unlock /universality_power /gaussian_law_probability.
  under eq_integral do rewrite expr1.
  exact: normal_mean.
split.
  rewrite unlock /universality_power /gaussian_law_probability.
  by rewrite (normal_moment_even 1) big_ord1.
split.
  rewrite unlock /universality_power /gaussian_law_probability.
  by rewrite (normal_moment_even 2) big_ord_recr big_ord1 /= mul1r.
rewrite gaussian_subgaussian_expectation lee_fin.
have hsq : Num.sqrt (2 ^+ 2) = (2 : RR) by rewrite sqrtr_sqr ger0_norm.
rewrite -[leRHS]hsq.
by apply: ler_wsqrtr; nra.
Qed.

Lemma gaussian_component_law :
  mixture_component_law 2%:R gaussian_law_probability.
Proof. exact: coordinate_law_component gaussian_coordinate_law. Qed.

Lemma gaussian_mixture_family :
  mixture_family 2%:R (fun=> 1%N) (fun _ _ => 1)
    (fun _ _ _ => gaussian_law_probability).
Proof.
have [hf _] := one_component_family 3%:R 2%:R
  (fun _ _ => gaussian_law_probability)
  (fun _ _ _ => gaussian_coordinate_law).
exact: hf.
Qed.

Lemma gaussian_mixture_fourth_moment :
  mixture_fourth_moment 3%:R (fun=> 1%N) (fun _ _ => 1)
    (fun _ _ _ => gaussian_law_probability).
Proof.
have [_ h4] := one_component_family 3%:R 2%:R
  (fun _ _ => gaussian_law_probability)
  (fun _ _ _ => gaussian_coordinate_law).
exact: h4.
Qed.

Lemma gaussian_mixture_probability n d (E : set (paper_main_sample n d)) :
  mixture_probability 1 (fun=> 1) (fun _ _ => gaussian_law_probability)
    n d E = gaussian_product_law (n * d) E.
Proof.
by rewrite one_component_probability /universality_probability
  -gaussian_sample_lawE.
Qed.
