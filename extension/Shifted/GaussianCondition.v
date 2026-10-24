(* Gaussian small-shift condition thresholds and the optimal condition
   number. The scalar curve is the previously proved fourth-moment-three
   curve. The optimum is controlled as an infimum; no minimizing matrix,
   attainment assertion, or measurable selection is used. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability rat.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions ConditionDefinitions.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Condition Require Import Curve.
Require Import EllipsoidUniversality.Condition.Theorem.
From EllipsoidUniversality.Shifted Require Import Translations GaussianExistence GaussianSmallShift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

(* This names the identical small-shift hypothesis of the existence and
   nonexistence inputs. It concerns a deterministic sequence of columns. *)
Definition gaussian_small_shift (m : forall d, 'cV[R]_d) : Prop :=
  forall e : R, 0 < e -> exists D : nat, forall d, (D <= d)%N ->
    frobenius (m d) <= e * Num.sqrt d%:R.

Lemma measurable_gaussian_shift_fit n d (m : 'cV[R]_d) (C : R) :
  measurable (sample_translate m @^-1` universality_conditioned_fit_event n d C).
Proof.
rewrite -[X in measurable X]setTI.
exact: measurable_sample_translate (measurable_conditioned_fit_event _ _ _).
Qed.

Lemma measurable_gaussian_shift_condition_number n d (m : 'cV[R]_d) :
  measurable_fun [set: paper_main_sample n d]
    (fun x => data_condition_number n d (sample_translate m x)).
Proof.
apply: measurableT_comp; first exact: measurable_data_condition_number.
exact: measurable_sample_translate.
Qed.

Theorem gaussian_shift_condition_threshold (C alpha : R)
    (N : nat -> nat) (m : forall d, 'cV[R]_d) :
  1 < C -> 0 < alpha -> universality_density_tends_to N alpha ->
  gaussian_small_shift m ->
  (alpha < condition_alpha C ->
    paper_main_tends_to (fun d => gaussian_product_law (N d * d)
      (sample_translate (m d) @^-1` universality_conditioned_fit_event (N d) d C)) 1%R) /\
  (condition_alpha C < alpha ->
    paper_main_tends_to (fun d => gaussian_product_law (N d * d)
      (sample_translate (m d) @^-1` universality_conditioned_fit_event (N d) d C)) 0%R).
Proof.
move=> C1 a0 hN hm; split=> aC.
- exact: gaussian_small_shift_exists a0 C1 aC hN hm.
- exact: gaussian_small_shift_condition_unsat C1 a0 aC hN hm.
Qed.

Theorem gaussian_shift_optimal_condition (alpha : R)
    (N : nat -> nat) (m : forall d, 'cV[R]_d) :
  0 < alpha -> alpha < 4%:R^-1 ->
  universality_density_tends_to N alpha -> gaussian_small_shift m ->
  forall eps delta : R, 0 < eps -> 0 < delta ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (N d) d), [/\ measurable E,
    (gaussian_product_law (N d * d) E <= delta%:E)%E &
    forall x, ~ E x ->
      (`|data_condition_number (N d) d (sample_translate (m d) x) -
        (condition_star alpha)%:E| <= eps%:E)%E].
Proof.
move=> a0 a4 hN hm eps delta e0 dl0.
have [st1 stE below above] := condition_starP alpha a0 a4.
move: st1 stE below above; set Cs := condition_star alpha.
move=> st1 stE below above.
have e2 : 0 < eps / 2%:R by rewrite divr_gt0.
pose Cp := Cs + eps / 2%:R.
pose Cm := Num.max (Cs - eps / 2%:R) ((1 + Cs) / 2%:R).
have CsCp : Cs < Cp by rewrite ltrDl.
have Cp1 : 1 < Cp := lt_trans st1 CsCp.
have hmC : (1 + Cs) / 2%:R <= Cm by rewrite le_max lexx orbT.
have dm : Cs - eps / 2%:R <= Cm by rewrite le_max lexx.
have Cm1 : 1 < Cm by apply: lt_le_trans hmC; lra.
have CmCs : Cm < Cs.
  rewrite gt_max; apply/andP; split; last by lra.
  by rewrite ltrBlDr ltrDl.
have CpE : Cp = Cs + eps / 2%:R by [].
clearbody Cp Cm.
have aCp : alpha < condition_alpha Cp := above Cp CsCp.
have aCm : condition_alpha Cm < alpha := below Cm Cm1 CmCs.
have [tp _] := gaussian_shift_condition_threshold Cp1 a0 hN hm.
have [_ tm] := gaussian_shift_condition_threshold Cm1 a0 hN hm.
have dl2 : 0 < delta / 2%:R by rewrite divr_gt0.
have [D1 h1] := tp aCp _ dl2.
have [D2 h2] := tm aCm _ dl2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
pose Fp : set (paper_main_sample (N d) d) :=
  sample_translate (m d) @^-1` universality_conditioned_fit_event (N d) d Cp.
pose Fm : set (paper_main_sample (N d) d) :=
  sample_translate (m d) @^-1` universality_conditioned_fit_event (N d) d Cm.
have mFp : measurable Fp := measurable_gaussian_shift_fit _ _.
have mFm : measurable Fm := measurable_gaussian_shift_fit _ _.
exists (~` Fp `|` Fm); split.
- exact: measurableU (measurableC mFp) mFm.
- have hp := gaussian_complement_probability mFp (h1 d d1).
  have hq : (gaussian_product_law (N d * d) Fm <= (delta / 2%:R)%:E)%E.
    have h := h2 d d2.
    rewrite sube0 gee0_abs ?measure_ge0 // in h.
    exact: ltW h.
  apply: le_trans (measureU2 (gaussian_product_law (N d * d))
    (measurableC mFp) mFm) _.
  apply: le_trans (leeD hp hq) _.
  rewrite -EFinD lee_fin; clear; lra.
- move=> x hx.
  have xFp : Fp x by apply: contrapT => nFp; apply: hx; left.
  have xFm : ~ Fm x by move=> xm; apply: hx; right.
  have hi : (data_condition_number (N d) d (sample_translate (m d) x) <= Cp%:E)%E.
    by apply: ge_ereal_inf; exists Cp%:E => //; exists Cp.
  have lo : (Cm%:E <= data_condition_number (N d) d (sample_translate (m d) x))%E.
    apply: le_ereal_inf_tmp => _ [c fc <-]; rewrite lee_fin.
    rewrite leNgt; apply/negP => cCm; apply: xFm.
    exact: conditioned_fit_mono _ _ _ _ _ (ltW cCm) fc.
  move: lo hi; case: (data_condition_number _ _ _) => [y||] //=.
  rewrite !lee_fin => lo hi.
  clearbody Cs; clear -lo hi dm CpE e0.
  by rewrite ler_norml; apply/andP; split; lra.
Qed.

Lemma measurable_gaussian_shift_optimal_tail n d (m : 'cV[R]_d) (c eps : R) :
  measurable [set x : paper_main_sample n d |
    (eps%:E < `|data_condition_number n d (sample_translate m x) - c%:E|)%E].
Proof.
have mf : measurable_fun [set: paper_main_sample n d]
    (fun x => `|data_condition_number n d (sample_translate m x) - c%:E|)%E.
  apply: measurableT_comp; first exact: abse_measurable.
  apply: emeasurable_funB; first exact: measurable_gaussian_shift_condition_number.
  exact: measurable_cst.
rewrite -[X in measurable X]setTI.
exact: (@emeasurable_fun_o_infty _ _ RR setT _ measurableT mf eps%:E).
Qed.

Corollary gaussian_shift_optimal_tail (alpha : R)
    (N : nat -> nat) (m : forall d, 'cV[R]_d) :
  0 < alpha -> alpha < 4%:R^-1 ->
  universality_density_tends_to N alpha -> gaussian_small_shift m ->
  forall eps : R, 0 < eps ->
  paper_main_tends_to (fun d => gaussian_product_law (N d * d)
    [set x : paper_main_sample (N d) d |
      (eps%:E < `|data_condition_number (N d) d (sample_translate (m d) x) -
        (condition_star alpha)%:E|)%E]) 0%R.
Proof.
move=> a0 a4 hN hm eps e0 delta dl0.
have dl2 : 0 < delta / 2 by rewrite divr_gt0.
have [D hD] := gaussian_shift_optimal_condition a0 a4 hN hm e0 dl2.
exists D => d dD.
have [E [mE PE hE]] := hD d dD.
pose A : set (paper_main_sample (N d) d) := [set x |
  (eps%:E < `|data_condition_number (N d) d (sample_translate (m d) x) -
    (condition_star alpha)%:E|)%E].
have mA : measurable A := measurable_gaussian_shift_optimal_tail _ _ _.
have AE : A `<=` E.
  move=> x hx; apply: contrapT => nx.
  have h := hE x nx.
  by move: hx; rewrite /A /= ltNge h.
rewrite sube0 gee0_abs ?measure_ge0 //.
apply: le_lt_trans (le_measure (gaussian_product_law (N d * d)) _ _ AE) _.
- by rewrite inE.
- by rewrite inE.
apply: le_lt_trans PE _.
rewrite lte_fin; clear -dl0.
change (is_true (delta / (2 : RR) < delta)); lra.
Qed.
