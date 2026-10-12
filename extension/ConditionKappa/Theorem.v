(* The threshold and the optimal condition number at fourth moment kappa,
   for finite mixtures of product laws, at Stdlib's R: item A1 of phase 11
   (notes/phase11-plan.md, sections 3.4, 5 and 6; lane B, reassigned from
   lane C). The model is
   Condition/Theorem.v, which treats kappa = 3.

   Results to prove here.
   - (20) at kappa: for K > 0, kappa > 1, C > 1 and alpha > 0, the
     conditioned fit event is measurable, and its probability tends to 1
     if alpha < alpha(C, kappa) (item D1, Sat) and to 0 if
     alpha(C, kappa) < alpha (item D2, Unsat).
   - (21) at kappa, from (20), as condition_number_of_threshold does at
     kappa = 3: for 0 < alpha < alpha*(kappa) and C_star = C_star(alpha,
     kappa), (20) at C_star + eps / 2 and at a point between 1 and C_star
     puts the optimal condition number (data_condition_number, measurable
     by measurable_data_condition_number of Condition/Theorem.v) within eps
     of C_star outside a measurable set of small probability.

   Interface used: I3, from item S3 (Curve, lane C): the analogue of
   condition_starP of Condition/Curve.v for C_star(alpha, kappa) on
   0 < alpha < alpha*(kappa): 1 < C_star, alpha(C_star, kappa) = alpha,
   alpha(C, kappa) < alpha for 1 < C < C_star, and
   alpha < alpha(C, kappa) for C_star < C.

   Proved, as implications until items S3 (Curve) and M5 (GaussianLimit)
   are on main.
   - condition_kappa_statement_holds: condition_kappa_statement, from the
     three forms of interface I3 that items D1 and D2 take (the analogues
     of condition_alpha_left and condition_alpha_right, and
     alpha(C, kappa) < 1/2) and interface I1, each for every kappa > 1.
     The measurability is measurable_conditioned_fit_event of
     Model/Measurability; the two limits are condition_kappa_sat (Sat)
     and condition_kappa_unsat (Unsat).
   - condition_kappa_statement_of_I3: the same with interface I1
     discharged by kcond_support_cvg of GaussianLimit (item M5), so that
     only the three forms of I3 remain as hypotheses.
   - condition_kappa_number_of_threshold: condition_kappa_statement ->
     condition_kappa_number_statement, given condition_kappa_inverse
     kappa (the frozen conjunct (e) of the curve statement) for every
     kappa > 1. Above C_star, alpha < alpha(C, kappa) by (e). Below it,
     alpha(C, kappa) < alpha because C_star is the greatest lower bound of
     the C > 1 with alpha <= alpha(C, kappa). The rest is the proof of
     condition_number_of_threshold of Condition/Theorem.v. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import gauss.
From GaussianAnalysis.probability Require Import mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality Require Import ConditionKappaCurveStatement.
From EllipsoidUniversality Require Import ConditionKappaStatement.
From EllipsoidUniversality.Features Require Import Mixture.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Gaussian Require Import InProbability.
Require Import EllipsoidUniversality.Condition.Theorem.
From EllipsoidUniversality.ConditionKappa Require Import Cone GaussianLimit.
From EllipsoidUniversality.ConditionKappa Require Import Sat Unsat.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. (20) at kappa, from the two halves, under interfaces I3 and I1. *)
Theorem condition_kappa_statement_holds :
  (forall kappa : R, 1 < kappa ->
     forall C' alpha' : R, 1 < C' -> alpha' < condition_kappa_alpha C' kappa ->
     exists2 Cm : R, 1 < Cm < C' & alpha' < condition_kappa_alpha Cm kappa) ->
  (forall kappa : R, 1 < kappa ->
     forall C' : R, 1 < C' -> condition_kappa_alpha C' kappa < 2^-1) ->
  (forall kappa : R, 1 < kappa ->
     forall C' alpha' : R, 1 < C' -> condition_kappa_alpha C' kappa < alpha' ->
     exists2 Cp : R, C' < Cp & condition_kappa_alpha Cp kappa < alpha') ->
  (forall kappa : R, 1 < kappa ->
     forall C' : R, 1 < C' -> cvg_prob (fun d => @gauss RR (d * d))
       (fun d a => kcond_support kappa C' (vec_mx a : 'M[RR]_d) / d%:R)
       (Num.sqrt (condition_kappa_alpha C' kappa))) ->
  condition_kappa_statement.
Proof.
move=> hleft hhalf hright hI1 kappa K C alpha k1 K0 C1 a0.
split; first by move=> n d; exact: measurable_conditioned_fit_event.
move=> N w mu hfam h4 n hn; split => aC.
  exact: (condition_kappa_sat K kappa C alpha K0 k1 C1 a0 aC (hleft kappa k1)
    (hhalf kappa k1) (hI1 kappa k1) N w mu hfam h4 n hn).
exact: (condition_kappa_unsat K kappa C alpha K0 k1 C1 a0 aC
  (hright kappa k1) (hI1 kappa k1) N w mu hfam h4 n hn).
Qed.

(* Interface I1 is item M5, kcond_support_cvg. *)
Theorem condition_kappa_statement_of_I3 :
  (forall kappa : R, 1 < kappa ->
     forall C' alpha' : R, 1 < C' -> alpha' < condition_kappa_alpha C' kappa ->
     exists2 Cm : R, 1 < Cm < C' & alpha' < condition_kappa_alpha Cm kappa) ->
  (forall kappa : R, 1 < kappa ->
     forall C' : R, 1 < C' -> condition_kappa_alpha C' kappa < 2^-1) ->
  (forall kappa : R, 1 < kappa ->
     forall C' alpha' : R, 1 < C' -> condition_kappa_alpha C' kappa < alpha' ->
     exists2 Cp : R, C' < Cp & condition_kappa_alpha Cp kappa < alpha') ->
  condition_kappa_statement.
Proof.
move=> hleft hhalf hright.
apply: (condition_kappa_statement_holds hleft hhalf hright).
by move=> kappa k1 C' C1'; exact: kcond_support_cvg.
Qed.

(* 2. (21) at kappa, from (20) and the inverse of the curve. *)

(* Below C_star, alpha(C, kappa) < alpha: C_star is the greatest lower
   bound of the C > 1 with alpha <= alpha(C, kappa). *)
Lemma condition_kappa_below (alpha kappa C : R) : 1 < C ->
  C < condition_kappa_star alpha kappa -> condition_kappa_alpha C kappa < alpha.
Proof.
move=> C1 CCs; rewrite ltNge; apply/negP => aC.
pose S := [set C : R | 1 < C /\ alpha <= condition_kappa_alpha C kappa].
have SC : S C by split.
have lb : has_lbound S by exists 1 => c [c1 _]; exact: ltW.
have := ge_inf lb SC; rewrite -/(condition_kappa_star alpha kappa).
by move: CCs; set c := condition_kappa_star alpha kappa; clearbody c => h1 h2;
  lra.
Qed.

Theorem condition_kappa_number_of_threshold :
  condition_kappa_statement ->
  (forall kappa : R, 1 < kappa -> condition_kappa_inverse kappa) ->
  condition_kappa_number_statement.
Proof.
move=> h20 hinv kappa K alpha k1 K0 a0 aS N w mu hfam h4 n hn eps delta e0 dl0.
have [st1 _ hiff] := hinv kappa k1 alpha a0 aS.
have above C : condition_kappa_star alpha kappa < C ->
    alpha < condition_kappa_alpha C kappa.
  by move=> sC; apply/(hiff C (lt_trans st1 sC)).
have below C : 1 < C -> C < condition_kappa_star alpha kappa ->
    condition_kappa_alpha C kappa < alpha.
  exact: condition_kappa_below.
move: st1 above below; set Cs := condition_kappa_star alpha kappa.
move=> st1 above below.
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
have aCp : alpha < condition_kappa_alpha Cp kappa := above Cp CsCp.
have aCm : condition_kappa_alpha Cm kappa < alpha := below Cm Cm1 CmCs.
have [_ hP] := h20 kappa K Cp alpha k1 K0 Cp1 a0.
have [_ hM] := h20 kappa K Cm alpha k1 K0 Cm1 a0.
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
