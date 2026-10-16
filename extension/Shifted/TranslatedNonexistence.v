(* Centered-fitting consequences of the uniform translation-error margin.
   The shift is arbitrary and deterministic. These consequences are used
   by the separately-even sign-mixture law; the universal quadric event
   itself is not invariant under independent row signs. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import symmetric_shift independent_row_signs.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting.Measurability Require Import Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From EllipsoidUniversality.Gaussian Require Import Threshold.
From EllipsoidUniversality.Shifted Require Import MainMoment MixtureRows ResidualLaws
  Translations TranslationError GaussianExistence SymmetricQuadric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma positive_translation_error_no_psd_fit n d (x : paper_main_sample n d)
    (eta : R) (m : 'cV[RR]_d) :
  (0 < n)%N -> (0 < d)%N -> 0 < eta ->
  eta <= translation_fitting_error n d x ->
  ~ paper_main_fit_event n d (sample_translate m x).
Proof.
move=> n0 d0 eta0 he hf.
have h1 := @translation_fitting_error_le n d x m n0 d0.
have h2 := fit_fitting_error n d (sample_translate m x) d0 hf.
have := le_trans he (le_trans h1 h2).
by rewrite leNgt eta0.
Qed.

Lemma translated_psd_probability_from_covers
    (n : nat -> nat) (alpha eta : R)
    (P : forall d, probability 'M[RR]_(n d,d) RR)
    (pi : forall d, set (paper_main_sample (n d) d) -> \bar R)
    (m : forall d, 'cV[RR]_d) :
  0 < alpha -> 0 < eta -> universality_density_tends_to n alpha ->
  (forall d A, measurable A -> P d ((@matrix_sample (n d) d) @^-1` A) = pi d A) ->
  (forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists E : set (paper_main_sample (n d) d),
      [/\ measurable E, (pi d E <= eps%:E)%E &
        forall x, ~ E x -> eta <= translation_fitting_error (n d) d x]) ->
  paper_main_tends_to (fun d=>pi d
    (sample_translate (m d) @^-1` paper_main_fit_event (n d) d)) 0.
Proof.
move=> a0 eta0 hn law covers eps eps0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [De hDe] := covers (eps/2) e20.
have [Dn hDn] := gaussian_density_positive a0 hn.
exists (maxn 1 (maxn De Dn))=>d.
rewrite !geq_max=>/andP[d0 /andP[de dn]].
have n0 := hDn d dn.
have [E [mE PE bound]] := hDe d de.
pose A := sample_translate (m d) @^-1` paper_main_fit_event (n d) d.
have mA : measurable A.
  rewrite -[X in measurable X]setTI.
  exact: measurable_sample_translate (pm_fit_event_measurable _ _).
have AE : A `<=` E.
  move=>x fx; apply: contrapT=>nx.
  exact: (@positive_translation_error_no_psd_fit (n d) d x eta (m d)
    n0 d0 eta0 (bound x nx) fx).
have mpA : measurable ((@matrix_sample (n d) d) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_matrix_sample.
have mpE : measurable ((@matrix_sample (n d) d) @^-1` E).
  by rewrite -[X in measurable X]setTI; exact: measurable_matrix_sample.
have pp : (@matrix_sample (n d) d) @^-1` A `<=`
    (@matrix_sample (n d) d) @^-1` E by move=>H; exact: AE.
rewrite -(law d A mA) sube0 gee0_abs ?measure_ge0 //.
apply: le_lt_trans (le_measure (P d) (mem_set mpA) (mem_set mpE) pp) _.
have PE' : (P d ((@matrix_sample (n d) d) @^-1` E) <= (eps/2)%:E)%E.
  exact (eq_ind_r (fun v : \bar R => (v <= (eps/2)%:E)%E) PE (law d E mE)).
apply: le_lt_trans PE' _; rewrite lte_fin; clear -eps0; lra.
Qed.

Theorem finite_translated_psd_nonexistence (kappa alpha K : R)
    (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K N w mu) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) :
  1 < kappa -> universality_alpha_star kappa < alpha -> 0 < K ->
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  mixture_fourth_moment kappa N w mu -> universality_density_tends_to n alpha ->
  paper_main_tends_to (fun d=>mixture_probability (N d) (w d) (mu d) (n d) d
    (sample_translate (m d) @^-1` paper_main_fit_event (n d) d)) 0.
Proof.
move=> k1 aa K0 sym fourth hn.
have a0 := lt_trans (universality_alpha_star_gt0 kappa k1) aa.
apply: (@translated_psd_probability_from_covers n alpha
  (symmetric_quadric_margin kappa alpha)
  (fun d=>independent_row_matrix_law (fun=>finite_row_law hfam d) (n d))
  (fun d=>mixture_probability (N d) (w d) (mu d) (n d) d) m a0
  (symmetric_quadric_margin_gt0 k1 aa) hn).
- move=>d A mA; exact: finite_matrix_sample_law mA.
- move=>eps eps0.
  have [D hD] := finite_symmetric_quadric k1 aa K0 sym fourth hn eps0.
  exists D=>d dD; have [E [mE PE hE]] := hD d dD.
  exists E; split=>// x nx; exact: (hE x nx).1.
Qed.

Theorem countable_translated_psd_nonexistence (kappa alpha K : R)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : countable_mixture_family K w mu) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) :
  1 < kappa -> universality_alpha_star kappa < alpha -> 0 < K ->
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  countable_fourth_moment kappa w mu -> universality_density_tends_to n alpha ->
  paper_main_tends_to (fun d=>countable_mixture_probability (w d) (mu d) (n d) d
    (sample_translate (m d) @^-1` paper_main_fit_event (n d) d)) 0.
Proof.
move=> k1 aa K0 sym fourth hn.
have a0 := lt_trans (universality_alpha_star_gt0 kappa k1) aa.
apply: (@translated_psd_probability_from_covers n alpha
  (symmetric_quadric_margin kappa alpha)
  (fun d=>independent_row_matrix_law (fun=>countable_row_law hfam d) (n d))
  (fun d=>countable_mixture_probability (w d) (mu d) (n d) d) m a0
  (symmetric_quadric_margin_gt0 k1 aa) hn).
- move=>d A mA; exact: countable_matrix_sample_law mA.
- move=>eps eps0.
  have [D hD] := countable_symmetric_quadric k1 aa K0 sym fourth hn eps0.
  exists D=>d dD; have [E [mE PE hE]] := hD d dD.
  exists E; split=>// x nx; exact: (hE x nx).1.
Qed.
