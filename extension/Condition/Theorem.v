(* The condition-number theorem at fourth moment three for finite mixtures,
   at Stdlib's R: item Q9 of phase 8 (notes/three-extensions-plan.md,
   sections 4.4 and 5.2; the note notes/phase6-three-extensions.md, (20)
   and (21)).

   - condition_statement_holds: (20). Below alpha_C, the satisfiable half
     condition_sat_witness (Condition/Sat, item Q7) at some C_- in (1, C)
     with alpha < alpha_(C_-) (condition_alpha_left of Condition/Curve),
     with the Gaussian witness gaussian_witness (Condition/GaussianWitness,
     Q3) at C_-. Above alpha_C, the unsatisfiable half condition_unsat_gap
     (Condition/Unsat, Q8) at some C_+ > C with alpha_(C_+) < alpha
     (condition_alpha_right), with the Gaussian gap gaussian_gap
     (Condition/GaussianGap, Q4) at C_+. Both Gaussian inputs take the
     limit cond_support_goe_cvg (Condition/GaussianCone, Q2).
   - conditioned_fit_mono: the event universality_conditioned_fit_event
     n d c increases with c.
   - measurable_data_condition_number: the optimal condition number
     data_condition_number n d is a measurable function of the sample, with
     values in the extended reals: {data_condition_number < r} is the union
     over the rationals q < r of the fit events at q.
   - condition_number_of_threshold: (21) from (20). For 0 < alpha < 1/4,
     C_star = condition_star alpha is the C > 1 with alpha_C = alpha, below
     it alpha_C < alpha and above it alpha_C > alpha (condition_starP of
     Condition/Curve). With C_+ = C_star + eps / 2 and
     C_- = max (C_star - eps / 2) ((1 + C_star) / 2), (20) gives a fit of
     condition number at most C_+ with probability tending to 1, and a fit
     of condition number at most C_- with probability tending to 0. Outside
     the union of the two exceptional events the optimal condition number
     lies in [C_-, C_+], hence within eps / 2 of C_star. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability rat.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionStatement.
From EllipsoidUniversality.Features Require Import Mixture.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Condition Require Import Curve GaussianCone.
From EllipsoidUniversality.Condition Require Import GaussianWitness GaussianGap.
From EllipsoidUniversality.Condition Require Import Sat Unsat.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. (20): the two halves at C_- < C and at C_+ > C. *)
Theorem condition_statement_holds : condition_statement.
Proof.
move=> K C alpha K0 C1 a0; split.
  by move=> n d; exact: measurable_conditioned_fit_event.
move=> N w mu hfam h4 n hn; split => aC.
- have [Cm /andP[Cm1 CmC] aCm] := condition_alpha_left _ _ C1 aC.
  exact: (condition_sat_witness K C Cm alpha K0 Cm1 CmC a0 aCm
    (gaussian_witness Cm alpha Cm1 a0 aCm (cond_support_goe_cvg Cm Cm1))
    N w mu hfam h4 n hn).
- have [Cp CCp aCp] := condition_alpha_right _ _ C1 aC.
  have Cp1 := lt_trans C1 CCp.
  exact: (condition_unsat_gap K C Cp alpha K0 C1 CCp a0
    (gaussian_gap Cp alpha Cp1 a0 aCp (cond_support_goe_cvg Cp Cp1))
    N w mu hfam h4 n hn).
Qed.

(* 2. The fit events increase with the condition number. *)
Lemma conditioned_fit_mono (n d : nat) (c c' : R) (x : paper_main_sample n d) :
  c <= c' -> universality_conditioned_fit_event n d c x ->
  universality_conditioned_fit_event n d c' x.
Proof.
move=> cc [S [lm [lm0 [hlo [hhi fit]]]]].
exists S, lm; split => //; split => //; split => //.
have [Ss Sq] := (uni_loewner_leP d _ S).1 hhi.
apply/(uni_loewner_leP d _ S); split => // v.
apply: le_trans (Sq v) _; apply: ler_wpM2r; first exact: pm_sqnorm_ge0.
by rewrite ler_pM2r.
Qed.

(* The optimal condition number of a sample is a measurable function of the
   sample: {data_condition_number < r} is the union over the rationals
   q < r of the fit events at q, by conditioned_fit_mono. *)
Lemma measurable_data_condition_number (n d : nat) :
  measurable_fun [set: paper_main_sample n d] (data_condition_number n d).
Proof.
apply: (@measurability _ _ _ _ _ _ (ErealGenInftyO.G (R:=R))).
  exact: ErealGenInftyO.measurableE.
move=> _ [_ [r ->] <-]; rewrite setTI.
set A := (data_condition_number n d @^-1` _).
have -> : A = \bigcup_(q : rat) [set x | ratr q < r /\
      universality_conditioned_fit_event n d (ratr q) x].
  apply/seteqP; split => x; rewrite /A /=.
  - rewrite interval.in_itv /= => /ereal_inf_lt [_ [c fc <-]].
    rewrite lte_fin => cr.
    have [q] := rat_in_itvoo cr; rewrite interval.in_itv /= => /andP[cq qr].
    exists q => //; split => //.
    exact: conditioned_fit_mono _ _ _ _ _ (ltW cq) fc.
  - move=> [q _ [qr fq]]; rewrite interval.in_itv /=.
    have h : (data_condition_number n d x <= (ratr q)%:E)%E.
      by apply: ge_ereal_inf; exists (ratr q)%:E => //; exists (ratr q).
    by apply: (le_lt_trans h); rewrite lte_fin.
apply: bigcupT_measurable_rat => q.
have [qr|qr] := ltP (ratr q) r.
- have -> : [set x | true /\
      universality_conditioned_fit_event n d (ratr q) x] =
      universality_conditioned_fit_event n d (ratr q).
    by apply/seteqP; split => x /=; [case | split].
  exact: measurable_conditioned_fit_event.
- have -> : [set x | false /\
      universality_conditioned_fit_event n d (ratr q) x] = set0.
    by apply/seteqP; split => x //= [].
  exact: measurable0.
Qed.

(* 3. (21) from (20). *)
Theorem condition_number_of_threshold :
  condition_statement -> condition_number_statement.
Proof.
move=> h20 K alpha K0 a0 a4 N w mu hfam h4 n hn eps delta e0 dl0.
have [st1 stE below above] := condition_starP alpha a0 a4.
move: st1 stE below above; set Cs := condition_star alpha.
move=> st1 stE below above.
have e2 : 0 < eps / 2%:R by rewrite divr_gt0 // ltr0n.
pose Cp := Cs + eps / 2%:R.
pose Cm := Num.max (Cs - eps / 2%:R) ((1 + Cs) / 2%:R).
have CsCp : Cs < Cp by rewrite ltrDl.
have Cp1 : 1 < Cp := lt_trans st1 CsCp.
have hm : (1 + Cs) / 2%:R <= Cm by rewrite le_max lexx orbT.
have dm : Cs - eps / 2%:R <= Cm by rewrite le_max lexx.
have Cm1 : 1 < Cm by apply: lt_le_trans hm; lra.
have CmCs : Cm < Cs.
  rewrite gt_max; apply/andP; split; last by lra.
  by rewrite ltrBlDr ltrDl.
have CpE : Cp = Cs + eps / 2%:R by [].
clearbody Cp Cm.
have aCp : alpha < condition_alpha Cp := above Cp CsCp.
have aCm : condition_alpha Cm < alpha := below Cm Cm1 CmCs.
have [_ hP] := h20 K Cp alpha K0 Cp1 a0.
have [_ hM] := h20 K Cm alpha K0 Cm1 a0.
have [tp _] := hP N w mu hfam h4 n hn.
have [_ tm] := hM N w mu hfam h4 n hn.
have d2 : 0 < delta / 2%:R by rewrite divr_gt0 // ltr0n.
have [D1 h1] := tp aCp _ d2.
have [D2 h2] := tm aCm _ d2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2'].
pose Fp := universality_conditioned_fit_event (n d) d Cp.
pose Fm := universality_conditioned_fit_event (n d) d Cm.
have mFp : measurable Fp := measurable_conditioned_fit_event _ _ _.
have mFm : measurable Fm := measurable_conditioned_fit_event _ _ _.
exists (~` Fp `|` Fm); split.
- exact: measurableU (measurableC mFp) mFm.
- pose P : probability (paper_main_sample (n d) d) RR := mixture
    (fun s : (n d).-tuple 'I_(N d) =>
       mixture_labelled_law (N d) (mu d) (n d) d s)
    (mixture_weights_prod (n d) (mix_weights K N w mu hfam d)).
  have PE (A : set (paper_main_sample (n d) d)) :
      mixture_probability (N d) (w d) (mu d) (n d) d A = P A by [].
  move: (h1 d d1) (h2 d d2'); rewrite !PE -/Fp -/Fm => hp hq.
  have hU : (P (~` Fp `|` Fm) <= P (~` Fp) + P Fm)%E :=
    measureU2 P (measurableC mFp) mFm.
  have hC : P (~` Fp) = (1 - P Fp)%E := probability_setC P mFp.
  apply: le_trans hU _; rewrite hC.
  have fp : P Fp \is a fin_num := fin_num_measure P _ mFp.
  have fm : P Fm \is a fin_num := fin_num_measure P _ mFm.
  move: hp hq; rewrite -(fineK fp) -(fineK fm).
  move: (fine (P Fp)) (fine (P Fm)) => p q.
  rewrite /= !lte_fin lee_fin !ltr_norml => /andP[hp1 hp2] /andP[hq1 hq2].
  (* the limits 1 and 0 of the statement are Stdlib's numerals *)
  have E1 : IZR (Zpos xH) = 1%:R by [].
  have E0 : IZR Z0 = 0%:R by [].
  rewrite E1 E0 in hp1 hp2 hq1 hq2.
  by clear -hp1 hp2 hq1 hq2; lra.
- move=> x hx.
  have xFp : Fp x by apply: contrapT => nFp; apply: hx; left.
  have xFm : ~ Fm x by move=> xm; apply: hx; right.
  have hi : (data_condition_number (n d) d x <= Cp%:E)%E.
    by apply: ge_ereal_inf; exists Cp%:E => //; exists Cp.
  have lo : (Cm%:E <= data_condition_number (n d) d x)%E.
    apply: le_ereal_inf_tmp => _ [c fc <-]; rewrite lee_fin.
    rewrite leNgt; apply/negP => cCm; apply: xFm.
    exact: conditioned_fit_mono _ _ _ _ _ (ltW cCm) fc.
  move: lo hi; case: (data_condition_number _ _ x) => [y||] //=.
  rewrite !lee_fin => lo hi.
  clearbody Cs; clear -lo hi dm CpE e0.
  by rewrite ler_norml; apply/andP; split; lra.
Qed.
