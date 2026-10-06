From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal interval interval_inference topology.
From mathcomp Require Import normedtype sequences exp numfun measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral charge.
From mathcomp Require Import probability.

(**md**************************************************************************)
(* # Integrals against the normal law                                         *)
(*                                                                            *)
(* MathComp-Analysis defines normal_prob m s as the measure with density      *)
(* normal_pdf m s against Lebesgue measure. This file turns that definition   *)
(* into a formula for integrals (integral_normal_prob) and proves that the    *)
(* powers, hence the functions of polynomial growth, are integrable against   *)
(* the standard normal law, with mean 0.                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section normal_density.
Context {R : realType} (m s : R).
Local Notation mu := (@lebesgue_measure R).
Local Notation P := (normal_prob m s).

Let measurable_pdf : measurable_fun [set: measurableTypeR R]
  (fun x => (normal_pdf m s x)%:E).
Proof. by apply/measurable_EFinP; exact: measurable_normal_pdf. Qed.

Let RN_pdf : ae_eq mu [set: R] (Radon_Nikodym_SigmaFinite.f P mu)
  (fun x => (normal_pdf m s x)%:E).
Proof.
apply: integral_ae_eq => //.
- exact: Radon_Nikodym_SigmaFinite.f_integrable (normal_prob_dominates m s).
- move=> E _ mE.
  by rewrite -(Radon_Nikodym_SigmaFinite.f_integral
    (normal_prob_dominates m s) mE).
Qed.

Lemma ge0_integral_normal_prob (f : R -> \bar R) :
  (forall x, (0 <= f x)%E) -> measurable_fun [set: R] f ->
  (\int[P]_x f x = \int[mu]_x (f x * (normal_pdf m s x)%:E))%E.
Proof.
move=> f0 mf.
rewrite -(Radon_Nikodym_SigmaFinite.change_of_variables
  (normal_prob_dominates m s) f0 measurableT mf).
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //.
  exact: measurable_int
    (Radon_Nikodym_SigmaFinite.f_integrable (normal_prob_dominates m s)).
- exact: emeasurable_funM.
- exact: ae_eqe_mul2l RN_pdf.
Qed.

Lemma integrable_normal_prob (f : R -> \bar R) : measurable_fun [set: R] f ->
  P.-integrable [set: R] f <->
  mu.-integrable [set: R] (fun x => f x * (normal_pdf m s x)%:E)%E.
Proof.
move=> mf.
have mpdf : measurable_fun [set: R] (fun x => (normal_pdf m s x)%:E).
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
have E : (\int[P]_x `|f x| = \int[mu]_x `|f x * (normal_pdf m s x)%:E|)%E.
  rewrite ge0_integral_normal_prob//; first by apply: measurableT_comp.
  apply: eq_integral => x _.
  by rewrite abseM (@gee0_abs _ (normal_pdf m s x)%:E)// lee_fin normal_pdf_ge0.
split=> /integrableP[_ fi]; apply/integrableP; split.
- exact: emeasurable_funM.
- by rewrite -E.
- exact: mf.
- by rewrite E.
Qed.

Lemma integral_normal_prob (f : R -> \bar R) : P.-integrable [set: R] f ->
  (\int[P]_x f x = \int[mu]_x (f x * (normal_pdf m s x)%:E))%E.
Proof.
move=> fi; have mf := measurable_int _ fi.
have p0 x : (0 <= (normal_pdf m s x)%:E)%E by rewrite lee_fin normal_pdf_ge0.
rewrite [LHS]integralE [RHS]integralE.
congr (_ - _)%E; rewrite ge0_integral_normal_prob//.
- exact: measurable_funepos.
- apply: eq_integral => x _; rewrite !funeposE.
  by rewrite muleC maxe_pMr// mule0 muleC.
- exact: measurable_funeneg.
- apply: eq_integral => x _; rewrite !funenegE.
  by rewrite muleC maxe_pMr// mule0 muleN muleC.
Qed.

End normal_density.

Section standard_normal_moments.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Notation N := (@normal_prob R 0 1).

Lemma exprn_le_expR (x : R) k :
  `|x| ^+ k <= (k`! * 4 ^ k)%:R * expR (x ^+ 2 / 4).
Proof.
set y := x ^+ 2 / 4.
have y0 : 0 <= y by rewrite /y divr_ge0 ?sqr_ge0.
have c1 : 1 <= (k`! * 4 ^ k)%:R :> R.
  by rewrite ler1n muln_gt0 fact_gt0 expn_gt0.
have ey1 : 1 <= expR y by rewrite (le_trans _ (expR_ge1Dx y))// lerDl.
have [x1|x1] := leP `|x| 1.
  rewrite (le_trans (exprn_ile1 _ (normr_ge0 x) x1))//.
  by rewrite (le_trans c1)// ler_peMr// ler0n.
case: k c1 => [|n] c1; first by rewrite expr0 (le_trans c1)// ler_peMr// ler0n.
have yn : y ^+ n.+1 <= n.+1`!%:R * expR y.
  have fpos : 0 < (n.+1)`!%:R :> R by rewrite ltr0n fact_gt0.
  rewrite -ler_pdivrMl// mulrC (le_trans _ (expR_ge1Dxn n y0))// lerDr.
  exact: ler01.
have x2 : `|x| ^+ 2 = 4 * y.
  by rewrite real_normK ?num_real// /y mulrC divfK ?pnatr_eq0.
rewrite (le_trans (_ : _ <= `|x| ^+ (2 * n.+1)))//.
  by rewrite ler_eXn2l// leq_pmull.
rewrite exprM x2 exprMn natrM natrX.
by rewrite [X in _ <= X]mulrAC [X in _ <= X]mulrC ler_pM2l ?exprn_gt0.
Qed.

Lemma integrable_normal_exprn k :
  N.-integrable [set: R] (fun x => (`|x| ^+ k)%:E).
Proof.
have mk : measurable_fun [set: R] (fun x : R => (`|x| ^+ k)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: normr_measurable.
apply/(integrable_normal_prob _ _ mk).
pose c := (k`! * 4 ^ k)%:R * normal_peak (1 : R) / normal_peak (Num.sqrt 2 : R).
have gi := integrableZl measurableT c (integrable_normal_pdf 0 (Num.sqrt 2)).
refine (le_integrable measurableT _ _ gi).
  apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
move=> x _; rewrite -!EFinM !abse_EFin lee_fin.
have s2 : Num.sqrt 2 != 0 :> R by rewrite sqrtr_eq0 -ltNge ltr0n.
rewrite normal_pdfE ?oner_neq0// normal_pdfE//=.
have p1 : 0 < normal_peak (1 : R) by rewrite normal_peak_gt0 ?oner_neq0.
have p2 : 0 < normal_peak (Num.sqrt 2 : R) by rewrite normal_peak_gt0.
have c0 : 0 <= c.
  apply: mulr_ge0; last by rewrite invr_ge0; exact: ltW.
  by apply: mulr_ge0 => //; exact: ltW.
have h1 : 0 <= `|x| ^+ k * (normal_peak 1 * normal_fun 0 1 x).
  apply: mulr_ge0; first exact: exprn_ge0.
  by apply: mulr_ge0; [exact: ltW|exact: normal_fun_ge0].
have h2 : 0 <= c * (normal_peak (Num.sqrt 2) * normal_fun 0 (Num.sqrt 2) x).
  by apply: mulr_ge0 => //; apply: mulr_ge0; [exact: ltW|exact: normal_fun_ge0].
rewrite (ger0_norm h1) (ger0_norm h2) /c /normal_fun !subr0 expr1n.
rewrite sqr_sqrtr ?ler0n// mulrA divfK ?gt_eqF// mulrCA.
rewrite [X in _ <= X]mulrAC [X in _ <= X]mulrC ler_pM2l//.
rewrite (le_trans (ler_wpM2r (expR_ge0 _) (exprn_le_expR x k)))// -mulrA.
rewrite ler_pM2l ?ltr0n ?muln_gt0 ?fact_gt0 ?expn_gt0// -expRD ler_expR.
lra.
Qed.

Lemma integrable_normal_poly (f : R -> R) (C : R) k :
  measurable_fun [set: R] f -> (forall x, `|f x| <= C * (1 + `|x| ^+ k)) ->
  N.-integrable [set: R] (EFin \o f).
Proof.
move=> mf fC.
have gi : N.-integrable [set: R] (fun x => (C * (1 + `|x| ^+ k))%:E).
  under eq_fun do rewrite EFinM.
  apply: integrableZl => //; under eq_fun do rewrite EFinD.
  apply: integrableD => //; last exact: integrable_normal_exprn.
  exact: finite_measure_integrable_cst.
refine (le_integrable measurableT _ _ gi); first exact/measurable_EFinP.
by move=> x _; rewrite /comp !abse_EFin lee_fin (le_trans (fC x))// ler_norm.
Qed.

End standard_normal_moments.
