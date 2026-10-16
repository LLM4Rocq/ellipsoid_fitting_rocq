(* Two-sided optimal-condition bounds for arbitrary Gaussian translations.
   Both constants precede the sample-size and shift sequences. The lower
   input holds simultaneously over all translations; the upper fit and
   the combined good event concern the specified deterministic shift.
   Source: doc/shifted-gaussian.tex, arbitrary Gaussian shifts. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions ConditionDefinitions.
From EllipsoidUniversality.Model Require Import Measurability.
Require Import EllipsoidUniversality.Condition.Theorem.
From EllipsoidUniversality.Shifted Require Import Translations GaussianExistence GaussianCondition ConditionLower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Theorem gaussian_arbitrary_shift_condition_bounds (alpha : R) :
  0 < alpha -> alpha < 4%:R^-1 ->
  exists c C : R, [/\ 0 < c, c <= C &
  forall (n : nat -> nat) (m : forall d, 'cV[R]_d),
    universality_density_tends_to n alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists E : set (paper_main_sample (n d) d),
      [/\ measurable E, (gaussian_product_law (n d*d) E <= eps%:E)%E &
        forall x, ~ E x ->
        universality_conditioned_fit_event (n d) d
          (C*(1+frobenius (m d)/Num.sqrt d%:R)) (sample_translate (m d) x) /\
        ((c*(1+frobenius (m d)/Num.sqrt d%:R))%:E <=
          data_condition_number (n d) d (sample_translate (m d) x) <=
          (C*(1+frobenius (m d)/Num.sqrt d%:R))%:E)%E]].
Proof.
move=> a0 a4.
have [c [c0 hc]] := gaussian_translated_condition_lower a0.
have [K [K0 hK]] := gaussian_arbitrary_shift_exists a0 a4.
pose C := maxr c K.
have cC : c <= C by rewrite /C le_max lexx.
have KC : K <= C by rewrite /C le_max lexx orbT.
exists c,C; split=> // n m hn eps eps0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [Dl hDl] := hc n hn (eps/2) e20.
have [Du hDu] := hK n m hn (eps/2) e20.
exists (maxn Dl Du)=>d; rewrite geq_max=>/andP[dl du].
have [E [mE PE lower]] := hDl d dl.
pose F : set (paper_main_sample (n d) d) := [set x |
  universality_conditioned_fit_event (n d) d
    (K*(1+frobenius (m d)/Num.sqrt d%:R)) (sample_translate (m d) x)].
have mF : measurable F := measurable_gaussian_shift_fit _ _.
have PF : (gaussian_product_law (n d*d) (~` F) <= (eps/2)%:E)%E.
  exact: gaussian_complement_probability mF (hDu d du).
exists (E `|` ~` F); split.
- exact: measurableU mE (measurableC mF).
- apply: le_trans (measureU2 (gaussian_product_law (n d*d)) mE (measurableC mF)) _.
  apply: le_trans (leeD PE PF) _.
  rewrite -EFinD lee_fin; clear -eps0; lra.
- move=> x nx.
  have nE : ~ E x by move=> h; apply: nx; left.
  have fx : F x by apply: contrapT=>h; apply: nx; right.
  have rate0 : 0 <= 1+frobenius (m d)/Num.sqrt d%:R.
    by rewrite addr_ge0 // divr_ge0 ?frobenius_ge0 ?sqrtr_ge0.
  have fit : universality_conditioned_fit_event (n d) d
      (C*(1+frobenius (m d)/Num.sqrt d%:R)) (sample_translate (m d) x).
    apply: conditioned_fit_mono _ _ _ _ _ _ fx.
    by apply: ler_wpM2r.
  split=> //; apply/andP; split; first exact: lower x nE (m d).
  apply: ge_ereal_inf.
  exists (C*(1+frobenius (m d)/Num.sqrt d%:R))%:E=>//.
  by exists (C*(1+frobenius (m d)/Num.sqrt d%:R)).
Qed.
