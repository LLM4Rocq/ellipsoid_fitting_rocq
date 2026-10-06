From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss gauss_ibp.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import normal_mgf gauss_shift partial_diff.

(**md**************************************************************************)
(* # Gaussian smoothing of Lipschitz functions                                *)
(*                                                                            *)
(* For G : 'rV[R]_n -> R and eps > 0, gauss_smooth eps G x is E[G (x + eps    *)
(* y)] for y of law gauss n. If G is bounded by K and L-Lipschitz for the     *)
(* Euclidean norm, then gauss_smooth eps G is bounded by K                    *)
(* (gauss_smooth_bounded) and L-Lipschitz (gauss_smooth_lipschitz). Its       *)
(* partial derivatives are gauss_smooth_partial eps G j x = E[G (x + eps y)   *)
(* y_j] / eps (gauss_smooth_derive), computed with the Cameron-Martin formula *)
(* of gauss_shift.v and differentiation under the integral sign. They are     *)
(* continuous (continuous_gauss_smooth_partial), so gauss_smooth eps G is     *)
(* differentiable (gauss_smooth_differentiable), and its gradient has         *)
(* Euclidean norm at most L (gauss_smooth_grad). Finally |gauss_smooth eps G  *)
(* x - G x| <= L eps E[|y|] (gauss_smooth_close).                             *)
(*                                                                            *)
(* The file also proves that a function that is Lipschitz for the Euclidean   *)
(* norm is continuous (lipschitz_frobenius_continuous), that the gradient of  *)
(* a function of class C^1 that is L-Lipschitz has Euclidean norm at most L   *)
(* (lipschitz_frobenius_grad), and an is_derive form of differentiation under *)
(* the integral sign (is_derive_Rintegral).                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*        gauss_smooth eps G x == E[G (x + eps y)], y of law gauss n          *)
(* gauss_smooth_partial eps G j x == E[G (x + eps y) y_j] / eps               *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section frobenius_mx_norm.
Context {R : realType}.

Lemma frobenius_le_mx_norm m n (A : 'M[R]_(m, n)) :
  frobenius A <= (m * n)%:R * `|A|.
Proof.
have A0 := normr_ge0 A; have k0 : (0 : R) <= (m * n)%:R by rewrite ler0n.
have h1 : mxdot A A <= (m * n)%:R * `|A| ^+ 2.
  apply: (@le_trans _ _ (\sum_(i < m) \sum_(j < n) `|A| ^+ 2)).
    apply: ler_sum => i _; apply: ler_sum => j _.
    rewrite -expr2 -real_normK ?num_real// lerXn2r ?nnegrE//.
    exact: mx_norm_entry_le.
  under eq_bigr do rewrite sumr_const card_ord.
  by rewrite sumr_const card_ord -mulrnA mulr_natl mulnC.
have h2 : (m * n)%:R * `|A| ^+ 2 <= ((m * n)%:R * `|A|) ^+ 2.
  rewrite exprMn ler_wpM2r ?exprn_ge0// expr2 -natrM ler_nat.
  by case: (m * n)%N => // k; rewrite leq_pmulr.
rewrite /frobenius -[X in _ <= X]ger0_norm ?mulr_ge0// -sqrtr_sqr.
by rewrite ler_sqrt// (le_trans h1 h2).
Qed.

End frobenius_mx_norm.

Section lipschitz_frobenius.
Context {R : realType} {n : nat}.
Implicit Types F : 'rV[R]_n -> R.

Lemma lipschitz_frobenius_continuous F (L : R) :
  (forall x y, `|F x - F y| <= L * frobenius (x - y)) -> continuous F.
Proof.
move=> FL x.
pose L' := `|L| + 1; have L'0 : 0 < L' by rewrite /L' ltr_wpDl.
pose c := L' * ((1 * n)%:R + 1); have c0 : 0 < c by rewrite mulr_gt0// ltr_wpDl.
have FL' y : `|F x - F y| <= c * `|x - y|.
  rewrite (le_trans (FL x y))// -mulrA.
  apply: (@le_trans _ _ (L' * frobenius (x - y))).
    by rewrite ler_wpM2r ?frobenius_ge0// /L' (le_trans (ler_norm _))// lerDl.
  rewrite (ler_wpM2l (ltW L'0))//.
  apply: le_trans; first exact: frobenius_le_mx_norm.
  by rewrite ler_wpM2r// lerDl.
move=> A /nbhs_ballP [d d0 dA]; apply/nbhs_ballP.
exists (d / c); first by rewrite /= divr_gt0.
move=> y; rewrite /= -ball_normE /= => xy; apply: dA; rewrite -ball_normE /=.
by rewrite (le_lt_trans (FL' y))// mulrC -ltr_pdivlMr.
Qed.

(* A function of class C^1 that is L-Lipschitz for the Euclidean norm has
   a gradient of Euclidean norm at most L. *)
Lemma lipschitz_frobenius_grad F (DF : 'I_n -> 'rV[R]_n -> R) (L : R) :
    (forall j x, is_derive x (delta_mx 0 j) F (DF j x)) ->
    (forall j, continuous (DF j)) ->
    (forall x y, `|F x - F y| <= L * frobenius (x - y)) ->
  forall x, mxdot (\row_j DF j x) (\row_j DF j x) <= L ^+ 2.
Proof.
move=> dF cDF FL x; set g := \row_j DF j x.
have Fd := partial_differentiable dF cDF x.
have Dg : 'D_g (F : 'rV[R]_n -> R^o) x = mxdot g g.
  rewrite deriveE// (partial_diffE dF cDF) /partial_lin /mxdot big_ord1.
  by apply: eq_bigr => j _; rewrite mxE.
have D_le : 'D_g (F : 'rV[R]_n -> R^o) x <= L * frobenius g.
  apply: limr_le; first exact: diff_derivable.
  near=> h.
  have h0 : h != 0 by near: h; exact: nbhs_dnbhs_neq.
  rewrite /= (le_trans (ler_norm _))// normrZ normfV.
  have hp : 0 < `|h| by rewrite normr_gt0.
  by rewrite ler_pdivrMl// (le_trans (FL _ _))// addrK frobeniusZ mulrCA.
rewrite Dg in D_le; have f0 := frobenius_ge0 g.
rewrite -frobenius_sqr in D_le *.
have [g0|gp] := eqVneq (frobenius g) 0; first by rewrite g0 expr0n /= sqr_ge0.
have fpos : 0 < frobenius g by rewrite lt_neqAle eq_sym gp f0.
have fL : frobenius g <= L by rewrite -(ler_pM2r fpos) -expr2.
by rewrite lerXn2r// ?nnegrE// (le_trans f0 fL).
Unshelve. all: by end_near.
Qed.

End lipschitz_frobenius.

Section is_derive_Rintegral.
Context {R : realType} d {Y : measurableType d} (mu : {measure set Y -> \bar R}).

(* Differentiation under the integral sign, in the form of is_derive. *)
Lemma is_derive_Rintegral (f df : R -> Y -> R) (D : Y -> R) (u v a : R) :
    a \in `]u, v[ ->
    (forall x, x \in `]u, v[ -> mu.-integrable [set: Y] (EFin \o f x)) ->
    (forall x y, x \in `]u, v[ -> is_derive x 1 (f ^~ y) (df x y)) ->
    (forall y, 0 <= D y) -> mu.-integrable [set: Y] (EFin \o D) ->
    (forall x y, x \in `]u, v[ -> `|df x y| <= D y) ->
  is_derive a 1 (fun x => \int[mu]_y f x y) (\int[mu]_y df a y).
Proof.
move=> aI fi fd D0 Di Db.
have pE x y : x \in `]u, v[ -> partial1of2 f x y = df x y.
  by move=> xI; have h := fd x y xI; rewrite partial1of2E derive_val.
have derf x y : x \in `]u, v[ -> [set: Y] y -> derivable (f ^~ y) x 1.
  by move=> xI _; case: (fd x y xI).
have Gub x y : x \in `]u, v[ -> [set: Y] y -> `|partial1of2 f x y| <= D y.
  by move=> xI _; rewrite pE//; exact: Db.
have dF := @derivable_under_integral R _ Y mu f setT measurableT a u v aI fi derf
  D D0 Di Gub.
have E := @differentiation_under_integral R _ Y mu f setT measurableT a u v aI fi
  derf D D0 Di Gub.
apply: DeriveDef => //; rewrite -derive1E E; apply: eq_Rintegral => y _.
exact: pE.
Qed.

End is_derive_Rintegral.

Section gauss_integrable.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma integrable_gauss_bounded n (f : 'rV[R]_n -> R) (C : R) :
  measurable_fun [set: 'rV[R]_n] f -> (forall y, `|f y| <= C) ->
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o f).
Proof.
move=> mf fC; have C0 : 0 <= C := le_trans (normr_ge0 _) (fC 0).
apply: (integrable_gauss_poly mf (C := C) (k := 0)) => y.
by rewrite expr0 (le_trans (fC y))// ler_peMr// lerDr.
Qed.

Lemma integrable_normal_expR_abs (c : R) :
  N.-integrable [set: R] (fun u => (expR (c * `|u|))%:E).
Proof.
have mE : measurable_fun [set: R] (fun u : R => (expR (c * `|u|))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurableT_comp.
apply: (@le_integrable _ _ _ N setT measurableT _
  (fun u => (expR (c * u) + expR (- c * u))%:E) mE).
  move=> u _; rewrite !gee0_abs ?lee_fin ?addr_ge0 ?expR_ge0//.
  by case: (ler0P u) => u0; rewrite ?ler0_norm ?gtr0_norm// ?mulrN ?mulNr ?lerDr ?lerDl ?expR_ge0.
under eq_fun do rewrite EFinD.
apply: integrableD => //; first exact: integrable_normal_expR (oner_neq0 R).
exact: integrable_normal_expR (oner_neq0 R).
Qed.

Lemma integrable_gauss_expR_abs_coord n (j : 'I_n) (c : R) :
  (gauss n).-integrable [set: 'rV[R]_n] (fun y => (expR (c * `|y 0 j|))%:E).
Proof.
have mE : measurable_fun [set: R] (fun u : R => (expR (c * `|u|))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurableT_comp.
by apply/(integrable_gauss_coord j mE); exact: integrable_normal_expR_abs.
Qed.

End gauss_integrable.

Section gauss_smooth.
Context {R : realType} {n : nat}.

(* The Gaussian smoothing of G at scale eps, x |-> E[G (x + eps y)] for y
   of law gauss n, and its candidate partial derivatives. *)
Definition gauss_smooth (eps : R) (G : 'rV[R]_n -> R) (x : 'rV[R]_n) : R :=
  \int[gauss n]_y G (x + eps *: y).

Definition gauss_smooth_partial (eps : R) (G : 'rV[R]_n -> R) (j : 'I_n)
    (x : 'rV[R]_n) : R :=
  eps^-1 * \int[gauss n]_y (G (x + eps *: y) * y 0 j).

Variables (G : 'rV[R]_n -> R) (K L eps : R).
Hypothesis GK : forall x, `|G x| <= K.
Hypothesis GL : forall x y, `|G x - G y| <= L * frobenius (x - y).
Hypothesis eps0 : 0 < eps.

Let K0 : 0 <= K := le_trans (normr_ge0 _) (GK 0).
Let cG : continuous G := lipschitz_frobenius_continuous GL.
Let mG : measurable_fun [set: 'rV[R]_n] G := continuous_measurable_mx cG.

Let maff (x : 'rV[R]_n) (c : R) :
  measurable_fun [set: 'rV[R]_n] (fun y : 'rV[R]_n => x + c *: y).
Proof.
apply: measurable_addmx; first exact: measurable_cst.
by apply: measurable_scalemx => //; exact: measurable_cst.
Qed.

Let mGa x c : measurable_fun [set: 'rV[R]_n] (fun y => G (x + c *: y)) :=
  measurableT_comp mG (maff x c).

Let iGa x c : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun y => G (x + c *: y))) :=
  integrable_gauss_bounded (mGa x c) (fun y => GK _).

Let iGa_coord x c j :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun y => G (x + c *: y) * y 0 j)).
Proof.
have m : measurable_fun [set: 'rV[R]_n] (fun y => G (x + c *: y) * y 0 j).
  by apply: measurable_funM => //; exact: measurable_mxentry.
apply: (integrable_gauss_poly m (C := K) (k := 1)) => y.
rewrite normrM expr1 mulrDr mulr1 (le_trans (ler_wpM2r (normr_ge0 _) (GK _)))//.
apply: (@le_trans _ _ (K * `|y|)); first by rewrite ler_wpM2l// mx_norm_entry_le.
by rewrite lerDr.
Qed.

Lemma gauss_smooth_bounded x : `|gauss_smooth eps G x| <= K.
Proof.
have mA : measurable_fun [set: 'rV[R]_n] (fun y => `|G (x + eps *: y)|).
  exact: measurableT_comp.
rewrite /gauss_smooth (le_trans (le_normr_Rintegral _ _))//.
apply: (@le_trans _ _ (\int[gauss n]_y K)).
  apply: le_Rintegral => //.
    by apply: (integrable_gauss_bounded (C := K) mA) => y; rewrite normr_id.
  by apply: (integrable_gauss_bounded (C := K)) => // y; rewrite ger0_norm.
by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
Qed.

Lemma gauss_smooth_lipschitz x x' :
  `|gauss_smooth eps G x - gauss_smooth eps G x'| <= L * frobenius (x - x').
Proof.
rewrite /gauss_smooth -RintegralB//.
have mD : measurable_fun [set: 'rV[R]_n]
    (fun y => G (x + eps *: y) - G (x' + eps *: y)).
  exact: measurable_funB.
have bD y : `|G (x + eps *: y) - G (x' + eps *: y)| <= L * frobenius (x - x').
  by rewrite (le_trans (GL _ _))// opprD addrACA subrr addr0.
have L0 : 0 <= L * frobenius (x - x') := le_trans (normr_ge0 _) (bD 0).
rewrite (le_trans (le_normr_Rintegral _ _))//.
  exact: (integrable_gauss_bounded mD bD).
apply: (@le_trans _ _ (\int[gauss n]_y (L * frobenius (x - x')))).
  apply: le_Rintegral => //.
    apply: (integrable_gauss_bounded (C := L * frobenius (x - x'))).
      exact: measurableT_comp.
    by move=> y; rewrite normr_id.
  by apply: (integrable_gauss_bounded (C := L * frobenius (x - x'))) => // y; rewrite ger0_norm.
by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
Qed.

Let e0 : eps != 0 := lt0r_neq0 eps0.

(* The exponent of the Cameron-Martin density for the shift a along a
   coordinate u of y, after the scaling by eps. *)
Let q (u a : R) := a * (u / eps) - a ^+ 2 / (2 * eps ^+ 2).

Let is_derive_q (u a : R) : is_derive a 1 (q u) (u / eps - a / eps ^+ 2).
Proof.
have hsq : is_derive a 1 (@GRing.exp R ^~ 2) (2%:R *: a ^+ 1 *: 1).
  by apply: DeriveDef; [exact: exprn_derivable|exact: exp_derive].
have h3 := is_deriveB (is_deriveZ (u / eps) (is_derive_id a 1))
  (is_deriveZ ((2 * eps ^+ 2)^-1) hsq).
have -> : q u = (u / eps) \*: id - (2 * eps ^+ 2)^-1 \*: (@GRing.exp R ^~ 2).
  by apply/funext => s; rewrite /q !fctE /= /GRing.scale /=; ring.
by apply: (is_derive_eq h3); rewrite /GRing.scale /= !mulr1 expr1; field.
Qed.

(* By the Cameron-Martin formula, shifting x along the j-th coordinate by a
   multiplies the law of y by expR (q (y 0 j) a). *)
Let gauss_smooth_shift x j (a : R) :
  gauss_smooth eps G (a *: delta_mx 0 j + x) =
  \int[gauss n]_y (G (x + eps *: y) * expR (q (y 0 j) a)).
Proof.
rewrite /gauss_smooth /Rintegral; congr fine.
have mf : measurable_fun [set: 'rV[R]_n] (fun y => (G (x + eps *: y))%:E).
  exact/measurable_EFinP.
have E := integral_gauss_shift ((a / eps) *: delta_mx 0 j) mf.
transitivity (\int[gauss n]_y (G (x + eps *: (y + (a / eps) *: delta_mx 0 j)))%:E)%E.
  apply: eq_integral => y _; congr (G _)%:E.
  rewrite scalerDr scalerA [eps * _]mulrC divfK//.
  by rewrite [_ + x]addrC -addrA [_ + a *: _]addrC.
rewrite E; apply: eq_integral => y _; rewrite EFinM; congr (_ * (expR _)%:E)%E.
rewrite mxdotZl mxdotZl mxdotZr mxdotC !mxdot_delta mxE !eqxx /= /q.
by field.
Qed.

Lemma gauss_smooth_derive x j :
  is_derive x (delta_mx 0 j) (gauss_smooth eps G) (gauss_smooth_partial eps G j x).
Proof.
pose f (a : R) (y : 'rV[R]_n) := G (x + eps *: y) * expR (q (y 0 j) a).
pose df (a : R) (y : 'rV[R]_n) :=
  G (x + eps *: y) * ((y 0 j / eps - a / eps ^+ 2) * expR (q (y 0 j) a)).
have fd (a : R) (y : 'rV[R]_n) : is_derive a 1 (f ^~ y) (df a y).
  have h := is_deriveZ (G (x + eps *: y))
    (is_derive1_comp (is_derive_expR (q (y 0 j) a)) (is_derive_q (y 0 j) a)).
  by apply: (is_derive_eq h); rewrite /df /GRing.scale /= [expR _ * _]mulrC.
(* A bound for f and its derivative in a, uniform for a in ]-1, 1[. *)
pose c := 1 + eps^-1 + eps^-2.
have c0 : 0 <= c by rewrite /c !addr_ge0// ?invr_ge0 ?exprn_ge0// ltW.
have c1 : 1 <= c.
  by rewrite /c -addrA lerDl addr_ge0// ?invr_ge0 ?exprn_ge0// ltW.
pose D' (y : 'rV[R]_n) := K * c * expR ((1 + eps^-1) * `|y 0 j|).
have D'0 y : 0 <= D' y by rewrite /D' !mulr_ge0// expR_ge0.
have ab (a : R) : a \in `]-1, 1[ -> `|a| <= 1.
  by rewrite in_itv /= => /andP[a1 a2]; rewrite ler_norml !ltW.
have qb (u a : R) : a \in `]-1, 1[ -> expR (q u a) <= expR (eps^-1 * `|u|).
  move=> /ab aa; rewrite ler_expR /q.
  have h1 : a * (u / eps) <= eps^-1 * `|u|.
    rewrite (le_trans (ler_norm _))// !normrM normfV (gtr0_norm eps0).
    by rewrite [eps^-1 * _]mulrC ler_piMl// divr_ge0// ltW.
  apply: le_trans h1; rewrite gerBl.
  by apply: divr_ge0; [exact: sqr_ge0|rewrite mulr_ge0// sqr_ge0].
have e1 (u : R) : 1 <= expR `|u|.
  by rewrite (le_trans _ (expR_ge1Dx _))// lerDl.
have eE (u : R) : expR ((1 + eps^-1) * `|u|) = expR `|u| * expR (eps^-1 * `|u|).
  by rewrite mulrDl mul1r expRD.
have fb a y : a \in `]-1, 1[ -> `|f a y| <= D' y.
  move=> aI; rewrite /f /D' normrM (ger0_norm (expR_ge0 _)) eE.
  apply: (le_trans (ler_pM (normr_ge0 _) (expR_ge0 _) (GK _) (qb _ _ aI))).
  rewrite -mulrA ler_wpM2l// mulrA ler_peMl ?expR_ge0//.
  by rewrite -[1]mulr1 ler_pM.
have hu (u a : R) : a \in `]-1, 1[ -> `|u / eps - a / eps ^+ 2| <= c * expR `|u|.
  move=> aI; rewrite (le_trans (ler_normB _ _))// !normrM !normfV (gtr0_norm eps0).
  rewrite normrX (gtr0_norm eps0).
  apply: (@le_trans _ _ ((eps^-1 + eps^-2) * expR `|u|)).
    rewrite mulrDl; apply: lerD.
      rewrite mulrC ler_wpM2l ?invr_ge0 ?(ltW eps0)//.
      by rewrite (le_trans _ (expR_ge1Dx _))// lerDr.
    rewrite mulrC ler_pM// ?invr_ge0 ?exprn_ge0 ?(le_trans (ab _ aI))//.
    exact: ltW.
  by rewrite ler_wpM2r ?expR_ge0// /c -addrA lerDr.
have dfb a y : a \in `]-1, 1[ -> `|df a y| <= D' y.
  move=> aI; rewrite /df /D' !normrM (ger0_norm (expR_ge0 _)) eE.
  apply: (@le_trans _ _ (K * ((c * expR `|y 0 j|) * expR (eps^-1 * `|y 0 j|)))).
    apply: ler_pM; rewrite ?mulr_ge0 ?expR_ge0//.
    by apply: ler_pM; rewrite ?mulr_ge0 ?expR_ge0//; [exact: hu|exact: qb].
  by rewrite !mulrA.
have D'i : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o D').
  have := integrableZl measurableT (K * c)
    (integrable_gauss_expR_abs_coord j (1 + eps^-1)).
  by apply: eq_integrable => // y _; rewrite /D' /= EFinM.
have mf a : measurable_fun [set: 'rV[R]_n] (f a).
  apply: measurable_funM; first exact: mGa.
  apply: measurableT_comp => //; rewrite /q.
  apply: measurable_funB => //; apply: measurable_funM => //.
  by apply: measurable_funM => //; exact: measurable_mxentry.
have fi a : a \in `]-1, 1[ -> (gauss n).-integrable [set: 'rV[R]_n] (EFin \o f a).
  move=> aI; apply: (le_integrable measurableT _ _ D'i).
    exact/measurable_EFinP.
  by move=> y _; rewrite /comp lee_fin (ger0_norm (D'0 y)) fb.
have I0 : (0 : R) \in `]-1, 1[ by rewrite in_itv /= ltrN10 ltr01.
have H := is_derive_Rintegral I0 fi (fun a y _ => fd a y) D'0 D'i dfb.
apply: (is_derive_transfer (G := fun a => \int[gauss n]_y f a y) (b := 0) (w := 1)).
  by move=> h; rewrite gauss_smooth_shift scaler1 addr0.
have iGj := iGa_coord x eps j.
apply: (is_derive_eq H); rewrite /gauss_smooth_partial -RintegralZl//.
apply: eq_Rintegral => y _; rewrite /df /q.
rewrite !mul0r expr0n /= !mul0r !subr0 expR0 mulr1.
by rewrite mulrA mulrC.
Qed.

Lemma continuous_gauss_smooth_partial j : continuous (gauss_smooth_partial eps G j).
Proof.
pose M : R := \int[gauss n]_y `|y 0 j|.
have mA : measurable_fun [set: 'rV[R]_n] (fun y : 'rV[R]_n => `|y 0 j|).
  by apply: measurableT_comp => //; exact: measurable_mxentry.
have iA : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun y : 'rV[R]_n => `|y 0 j|)).
  apply: (integrable_gauss_poly mA (C := 1) (k := 1)) => y.
  by rewrite normr_id mul1r expr1 (le_trans (mx_norm_entry_le y 0 j))// lerDr.
apply: (@lipschitz_frobenius_continuous _ _ _ (eps^-1 * L * M)) => x x'.
rewrite /gauss_smooth_partial -mulrBr normrM gtr0_norm ?invr_gt0// -mulrA.
rewrite -mulrA ler_wpM2l ?invr_ge0 ?(ltW eps0)//.
have i1 := iGa_coord x eps j; have i2 := iGa_coord x' eps j.
rewrite -RintegralB//.
have bD y : `|G (x + eps *: y) * y 0 j - G (x' + eps *: y) * y 0 j| <=
    L * frobenius (x - x') * `|y 0 j|.
  rewrite -mulrBl normrM ler_wpM2r// (le_trans (GL _ _))//.
  by rewrite opprD addrACA subrr addr0.
have mD : measurable_fun [set: 'rV[R]_n]
    (fun y => G (x + eps *: y) * y 0 j - G (x' + eps *: y) * y 0 j).
  by apply: measurable_funB; apply: measurable_funM => //; exact: measurable_mxentry.
have iD : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun y => G (x + eps *: y) * y 0 j - G (x' + eps *: y) * y 0 j)).
  have := integrableB measurableT i1 i2.
  by apply: eq_integrable => // y _; rewrite /= EFinB.
rewrite (le_trans (le_normr_Rintegral _ _))//.
apply: (@le_trans _ _ (\int[gauss n]_y (L * frobenius (x - x') * `|y 0 j|))).
  apply: le_Rintegral => //.
  - apply: (le_integrable measurableT _ _ iD).
      exact/measurable_EFinP/measurableT_comp.
    by move=> y _; rewrite /comp lee_fin normr_id.
  - have := integrableZl measurableT (L * frobenius (x - x')) iA.
    by apply: eq_integrable => // y _; rewrite /= EFinM.
by rewrite RintegralZl// mulrAC.
Qed.

Theorem gauss_smooth_differentiable x :
  differentiable (gauss_smooth eps G : 'rV[R]_n -> R^o) x.
Proof.
exact: (partial_differentiable (fun j x => gauss_smooth_derive x j)
  continuous_gauss_smooth_partial).
Qed.

Theorem gauss_smooth_grad x :
  mxdot (\row_j gauss_smooth_partial eps G j x) (\row_j gauss_smooth_partial eps G j x)
    <= L ^+ 2.
Proof.
exact: (lipschitz_frobenius_grad (fun j x => gauss_smooth_derive x j)
  continuous_gauss_smooth_partial gauss_smooth_lipschitz).
Qed.

Lemma integrable_gauss_frobenius :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun y : 'rV[R]_n => frobenius y)).
Proof.
have cF : continuous (fun y : 'rV[R]_n => frobenius y).
  apply: (@lipschitz_frobenius_continuous _ _ _ 1) => y y'.
  by rewrite mul1r ler_frobeniusB.
apply: (integrable_gauss_poly (continuous_measurable_mx cF) (C := (1 * n)%:R) (k := 1)).
move=> y; rewrite ger0_norm ?frobenius_ge0// expr1.
by rewrite (le_trans (frobenius_le_mx_norm y))// ler_wpM2l// lerDr.
Qed.

Lemma gauss_smooth_close x :
  `|gauss_smooth eps G x - G x| <= L * eps * \int[gauss n]_y frobenius y.
Proof.
have -> : G x = \int[gauss n]_y G x.
  by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
have iG := iGa x eps.
have iC : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun _ : 'rV[R]_n => G x)).
  by apply: (integrable_gauss_bounded (C := `|G x|)) => //.
rewrite /gauss_smooth -RintegralB//.
have mD : measurable_fun [set: 'rV[R]_n] (fun y => G (x + eps *: y) - G x).
  exact: measurable_funB.
have iD : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun y => G (x + eps *: y) - G x)).
  have := integrableB measurableT iG iC.
  by apply: eq_integrable => // y _; rewrite /= EFinB.
rewrite (le_trans (le_normr_Rintegral _ _))//.
have iF := integrable_gauss_frobenius.
apply: (@le_trans _ _ (\int[gauss n]_y (L * eps * frobenius y))).
  apply: le_Rintegral => //.
  - apply: (le_integrable measurableT _ _ iD).
      exact/measurable_EFinP/measurableT_comp.
    by move=> y _; rewrite /comp lee_fin normr_id.
  - have := integrableZl measurableT (L * eps) iF.
    by apply: eq_integrable => // y _; rewrite /= EFinM.
  - move=> y _; rewrite (le_trans (GL _ _))// addrAC subrr add0r.
    by rewrite frobeniusZ gtr0_norm// mulrA.
by rewrite RintegralZl.
Qed.

End gauss_smooth.
