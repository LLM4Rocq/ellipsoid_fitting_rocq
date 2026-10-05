From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import exp measure lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import normal_integral.

(**md**************************************************************************)
(* # Exponential moments and tails of the normal law                          *)
(*                                                                            *)
(* For s != 0, normal_prob m s is the normal law of mean m and variance s^2   *)
(* of MathComp-Analysis. This file computes its moment generating function,   *)
(* E[expR (t X)] = expR (t m + t^2 s^2 / 2) for X of law normal_prob m s      *)
(* (integral_normal_expR), and deduces Chernoff bounds for its tails: P(X >=  *)
(* m + u) and P(X <= m - u) are at most expR (- u^2 / (2 s^2)) for u >= 0     *)
(* (normal_prob_upper_tail, normal_prob_lower_tail), and P(|X - m| >= u) is   *)
(* at most twice that (normal_prob_abs_tail).                                 *)
(*                                                                            *)
(* measure_ge_expR is Chernoff's bound in integral form: P(u <= f) <= E[expR  *)
(* (t (f - u))] for every measure P, measurable f and t >= 0.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section chernoff.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : {measure set T -> \bar R}).

Lemma measure_ge_expR (f : T -> R) (u t : R) : measurable_fun [set: T] f ->
  (0 <= t)%R ->
  P [set x | u <= f x]%R <= \int[P]_x (expR (t * (f x - u)))%:E.
Proof.
move=> mf t0; have mA : measurable [set x | u <= f x]%R.
  have -> : [set x | u <= f x]%R = f @^-1` `[u, +oo[ by rewrite preimage_itvcy.
  by rewrite -[X in measurable X]setTI; apply: mf => //; exact: measurable_itv.
rewrite -(setIT [set x | u <= f x]%R) -integral_indic//.
apply: ge0_le_integral => //.
- by apply/measurable_EFinP; exact: measurable_indic.
- apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_funB.
move=> x _; rewrite lee_fin indicE; have [/= ux|_] := boolP (x \in _).
  by rewrite -expR0 ler_expR mulr_ge0// subr_ge0; move: ux; rewrite inE.
exact: expR_ge0.
Qed.

End chernoff.

Section normal_mgf.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Implicit Types m s t x a r u : R.

Lemma normal_pdf_expR m s t x : s != 0 ->
  expR (t * x) * normal_pdf m s x =
  expR (t * m + t ^+ 2 * s ^+ 2 / 2) * normal_pdf (m + t * s ^+ 2) s x.
Proof.
move=> s0; rewrite !normal_pdfE//.
rewrite mulrCA [RHS]mulrCA; congr (_ * _).
by rewrite /normal_fun -!expRD; congr expR; field.
Qed.

Lemma integral_normal_expR m s t : s != 0 ->
  (\int[normal_prob m s]_x (expR (t * x))%:E =
   (expR (t * m + t ^+ 2 * s ^+ 2 / 2))%:E)%E.
Proof.
move=> s0; rewrite ge0_integral_normal_prob//.
  by apply/measurable_EFinP; apply: measurableT_comp => //; apply: measurable_funM.
under eq_integral do rewrite -EFinM normal_pdf_expR// EFinM.
rewrite ge0_integralZl//.
- by apply/measurable_EFinP; exact: measurable_normal_pdf.
- by move=> x _; rewrite lee_fin normal_pdf_ge0.
- by rewrite integral_normal_pdf mule1.
Qed.

Lemma integrable_normal_expR m s t : s != 0 ->
  (normal_prob m s).-integrable setT (fun x => (expR (t * x))%:E).
Proof.
move=> s0; apply/integrableP; split.
  by apply/measurable_EFinP; apply: measurableT_comp => //; apply: measurable_funM.
under eq_integral do rewrite gee0_abs ?lee_fin ?expR_ge0//.
by rewrite integral_normal_expR// ltry.
Qed.

Lemma normal_prob_ge m s a r : s != 0 -> 0 <= r ->
  (normal_prob m s [set x | a <= x]%R <=
   (expR (r * (m - a) + r ^+ 2 * s ^+ 2 / 2))%:E)%E.
Proof.
move=> s0 r0.
have mA : measurable [set x : R | a <= x].
  by rewrite -set_itvcy//; exact: measurable_itv.
rewrite -(setIT [set x : R | a <= x]) -integral_indic//.
apply: (@le_trans _ _ (\int[normal_prob m s]_x (expR (r * (x - a)))%:E))%E.
  apply: ge0_le_integral => //.
  - by apply/measurable_EFinP; exact: measurable_indic.
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    by apply: measurable_funM => //; exact: measurable_funB.
  - move=> x _; rewrite lee_fin indicE; have [/= ax|_] := boolP (x \in _).
      by rewrite -expR0 ler_expR mulr_ge0// subr_ge0; move: ax; rewrite inE.
    exact: expR_ge0.
under eq_integral do rewrite mulrBr expRD mulrC EFinM.
rewrite ge0_integralZl//.
  by apply/measurable_EFinP; apply: measurableT_comp => //; apply: measurable_funM.
rewrite integral_normal_expR// -EFinM -expRD lee_fin ler_expR.
by rewrite mulrBr; lra.
Qed.

Lemma normal_prob_le m s a r : s != 0 -> 0 <= r ->
  (normal_prob m s [set x | x <= a]%R <=
   (expR (r * (a - m) + r ^+ 2 * s ^+ 2 / 2))%:E)%E.
Proof.
move=> s0 r0.
have mA : measurable [set x : R | x <= a].
  by rewrite -set_itvNyc//; exact: measurable_itv.
rewrite -(setIT [set x : R | x <= a]) -integral_indic//.
apply: (@le_trans _ _ (\int[normal_prob m s]_x (expR ((- r) * (x - a)))%:E))%E.
  apply: ge0_le_integral => //.
  - by apply/measurable_EFinP; exact: measurable_indic.
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    by apply: measurable_funM => //; exact: measurable_funB.
  - move=> x _; rewrite lee_fin indicE; have [/= ax|_] := boolP (x \in _).
      rewrite -expR0 ler_expR mulNr oppr_ge0 mulr_ge0_le0// subr_le0.
      by move: ax; rewrite inE.
    exact: expR_ge0.
under eq_integral do rewrite mulrBr expRD mulrC EFinM.
rewrite ge0_integralZl//.
  by apply/measurable_EFinP; apply: measurableT_comp => //; apply: measurable_funM.
rewrite integral_normal_expR// -EFinM -expRD lee_fin ler_expR.
by rewrite mulrBr sqrrN; lra.
Qed.

Lemma normal_prob_upper_tail m s u : s != 0 -> 0 <= u ->
  (normal_prob m s [set x | m + u <= x]%R <=
   (expR (- u ^+ 2 / (2 * s ^+ 2)))%:E)%E.
Proof.
move=> s0 u0; have s2 : 0 < s ^+ 2 by rewrite exprn_even_gt0.
have r0 : 0 <= u / s ^+ 2 by rewrite divr_ge0// ltW.
apply: le_trans (normal_prob_ge m (m + u) s0 r0) _.
by rewrite lee_fin ler_expR le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Lemma normal_prob_lower_tail m s u : s != 0 -> 0 <= u ->
  (normal_prob m s [set x | x <= m - u]%R <=
   (expR (- u ^+ 2 / (2 * s ^+ 2)))%:E)%E.
Proof.
move=> s0 u0; have s2 : 0 < s ^+ 2 by rewrite exprn_even_gt0.
have r0 : 0 <= u / s ^+ 2 by rewrite divr_ge0// ltW.
apply: le_trans (normal_prob_le m (m - u) s0 r0) _.
by rewrite lee_fin ler_expR le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Lemma normal_prob_abs_tail m s u : s != 0 -> 0 <= u ->
  (normal_prob m s [set x | u <= `|x - m|]%R <=
   (2 * expR (- u ^+ 2 / (2 * s ^+ 2)))%:E)%E.
Proof.
move=> s0 u0.
have -> : [set x | u <= `|x - m|]%R =
    [set x | m + u <= x]%R `|` [set x | x <= m - u]%R.
  apply/seteqP; split => x /=.
    rewrite ler_normr => /orP[ux|ux]; [left|right]; lra.
  by move=> [ux|ux]; rewrite ler_normr; apply/orP; [left|right]; lra.
apply: (le_trans (measureU2 _ _ _)).
- by rewrite -set_itvcy//; exact: measurable_itv.
- by rewrite -set_itvNyc//; exact: measurable_itv.
rewrite mulr_natl mulr2n EFinD.
by apply: leeD; [exact: normal_prob_upper_tail|exact: normal_prob_lower_tail].
Qed.

End normal_mgf.
