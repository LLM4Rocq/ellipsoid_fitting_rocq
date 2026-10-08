From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp trigo.
From mathcomp Require Import derive realfun.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability ftc charge.
From GaussianAnalysis.comparison Require Import normal_linear.

(**md**************************************************************************)
(* # The semicircle law                                                       *)
(*                                                                            *)
(* The semicircle law of radius r > 0 has the density                         *)
(* 2 / (pi r^2) sqrt (r^2 - x^2) on [-r, r] with respect to Lebesgue measure. *)
(* Its variance is r^2 / 4. Wigner's semicircle law for a GOE matrix scaled   *)
(* by 1 / sqrt d has radius 2, and the law nu of Koehler and Sohn (arXiv      *)
(* 2608.27372, lines 345-349), of density sqrt (2 - x^2) / pi, has radius     *)
(* sqrt 2. As MathComp-Analysis does for normal_pdf m 0, the density at       *)
(* r = 0 is the indicator of [0, 1], so that semicircle_prob r is a           *)
(* probability for every r.                                                   *)
(*                                                                            *)
(* Main results:                                                              *)
(* - Rintegral_sqrt_disk: \int_{-a}^{a} sqrt (a^2 - x^2) dx = pi a^2 / 2 for  *)
(*   a > 0, by the substitution x = a sin t (Rintegral_cos2:                  *)
(*   \int_{-pi/2}^{pi/2} cos^2 = pi / 2).                                     *)
(* - integral_semicircle_pdf: the density has integral one; hence             *)
(*   semicircle_prob r is a probability on measurableTypeR R, and             *)
(*   semicircle_prob_dominates: it is absolutely continuous with respect to   *)
(*   Lebesgue measure.                                                        *)
(* - ge0_integral_semicircle_prob, integrable_semicircle_prob,                *)
(*   integral_semicircle_prob: integrating against semicircle_prob r is       *)
(*   integrating against Lebesgue measure with the density, for nonnegative   *)
(*   or integrable functions; semicircle_integrable_eq,                       *)
(*   semicircle_integral_eq: the same for a function g that agrees with f     *)
(*   where the density is positive.                                           *)
(* - semicircle_prob_sym: for r != 0 the law is invariant under x |-> -x.     *)
(* - For r != 0: integrable_semicircle_continuous,                            *)
(*   integrable_semicircle_pdfM (every continuous function f is integrable,   *)
(*   and so is f times the density), Rintegral_semicircle (its integral is    *)
(*   the integral of f times the density over [-|r|, |r|]),                   *)
(*   semicircle_prob_gt0 (every half-line ]b, +oo[ with b < |r| has positive  *)
(*   measure), semicircle_restrict (if f times the density is integrable,     *)
(*   some measurable g that is f or 0 at each point has g times the density   *)
(*   equal to f times the density: f restricted to ]-|r|, |r|[).              *)
(* - semicircle_momentS: E X^(k+2) = (k + 1) r^2 / (k + 4) E X^k, by          *)
(*   integration by parts against (r^2 - x^2)^(3/2); semicircle_moment0,      *)
(*   semicircle_moment1, semicircle_moment2, semicircle_moment_odd: E 1 = 1,  *)
(*   E X = 0, E X^2 = r^2 / 4, and the odd moments vanish. At r = 2 the even  *)
(*   moments are the Catalan numbers.                                         *)
(* - semicircle_pdf_scale, ge0_integral_semicircle_scale: for r, a > 0, the   *)
(*   semicircle law of radius a r is the image of the one of radius r under   *)
(*   x |-> a x (by the affine change of variables of                          *)
(*   comparison/normal_linear.v).                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*    semicircle_pdf r x == 2 / (pi r^2) sqrt (r^2 - x^2), zero outside       *)
(*                          [-r, r] since Num.sqrt is zero on negative        *)
(*                          numbers; the indicator of [0, 1] if r = 0         *)
(*     semicircle_prob r == the measure with density semicircle_pdf r with    *)
(*                          respect to Lebesgue measure                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section disk_integral.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

(* The fundamental theorem of calculus, for an antiderivative on R. *)
Lemma Rintegral_FTC_R (f F : R -> R) (a b : R) : a < b -> continuous f ->
  (forall x : R, is_derive x 1 F (f x)) ->
  \int[mu]_(x in `[a, b]) f x = F b - F a.
Proof.
move=> ab cf dF.
have cF : continuous F.
  move=> x; apply: differentiable_continuous; apply/derivable1_diffP.
  exact: (@ex_derive _ _ _ _ _ _ _ (dF x)).
have E : (\int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E)%E.
  apply: continuous_FTC2 => //.
  - by apply: continuous_subspaceT => x; exact: cf.
  - split.
    + by move=> y _; exact: (@ex_derive _ _ _ _ _ _ _ (dF y)).
    + by apply: cvg_at_right_filter; exact: cF.
    + by apply: cvg_at_left_filter; exact: cF.
  - move=> y _; rewrite derive1E.
    exact: (@derive_val _ _ _ _ _ _ _ (dF y)).
by rewrite /Rintegral E -EFinB.
Qed.

(* \int_{-pi/2}^{pi/2} cos^2 = pi / 2. *)
Lemma Rintegral_cos2 :
  \int[mu]_(t in `[- (pi / 2), pi / 2]) cos t ^+ 2 = pi / 2 :> R.
Proof.
have pi0 : 0 < pi / 2 :> R by rewrite divr_gt0// pi_gt0.
pose H (t : R) := t / 2 + sin t * cos t / 2.
have dH (t : R) : is_derive t 1 H (cos t ^+ 2).
  have d1 : is_derive t 1 (fun s : R => 2^-1 * s) 2^-1.
    apply: (is_derive_eq (is_deriveZ 2^-1 (is_derive_id t 1))).
    by rewrite /GRing.scale /= mulr1.
  have := is_deriveD d1
    (is_deriveZ 2^-1 (is_deriveM (is_derive_sin t) (is_derive_cos t))).
  have -> : (fun s : R => 2^-1 * s) + 2^-1 *: (sin * cos) = H.
    by apply/funext => s; rewrite /H !fctE /GRing.scale /= ![2^-1 * _]mulrC.
  move=> h; apply: (is_derive_eq h); rewrite /GRing.scale /=.
  have := sin2cos2 t; move: (sin t) (cos t) => a b e.
  have -> : a * - a = - (a ^+ 2) by rewrite mulrN expr2.
  by rewrite e; field.
rewrite (Rintegral_FTC_R _ _ dH).
- by rewrite gtrN.
- by move=> x; apply: (@continuousM _ _ cos cos); exact: continuous_cos.
rewrite /H sinN cosN sin_pihalf cos_pihalf !mulr0 !mul0r !addr0.
by field.
Qed.

(* The area of the half disk: \int_{-a}^{a} sqrt (a^2 - x^2) dx = pi a^2 / 2,
   by the substitution x = a sin t. *)
Lemma Rintegral_sqrt_disk (a : R) : 0 < a ->
  \int[mu]_(x in `[- a, a]) Num.sqrt (a ^+ 2 - x ^+ 2) = pi / 2 * a ^+ 2.
Proof.
move=> a0; have pi0 : 0 < pi / 2 :> R by rewrite divr_gt0// pi_gt0.
pose F (t : R) := a * sin t.
pose G (x : R) := Num.sqrt (a ^+ 2 - x ^+ 2).
have dF (t : R) : is_derive t 1 F (a * cos t).
  apply: (is_derive_eq (is_deriveZ a (is_derive_sin t))).
  by rewrite /GRing.scale.
have F'E : F^`() = (fun t => a * cos t).
  by apply/funext => t; rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dF t)).
have cF : continuous F.
  by move=> t; apply: differentiable_continuous; apply/derivable1_diffP;
    exact: (@ex_derive _ _ _ _ _ _ _ (dF t)).
have cF' : continuous (fun t : R => a * cos t).
  by move=> t; apply: continuousM; [exact: cvg_cst|exact: continuous_cos].
have cG : continuous G.
  move=> x; apply: continuous_comp; last exact: sqrt_continuous.
  by apply: continuousB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
have := @integration_by_substitution_increasing R F G (- (pi / 2)) (pi / 2).
rewrite F'E.
have -> : F (- (pi / 2)) = - a by rewrite /F sinN sin_pihalf mulrN1.
have -> : F (pi / 2) = a by rewrite /F sin_pihalf mulr1.
move=> /(_ _ _ _ _ _ _ _) h.
have ab : - (pi / 2) <= pi / 2 :> R by have := pi0; lra.
have incr : {in `[- (pi / 2), pi / 2] &, {homo F : x y / x < y}}.
  by move=> x y xI yI xy; rewrite /F ltr_pM2l// ltr_sin.
have cvgl : cvg (a * cos x @[x --> (- (pi / 2))^'+]).
  apply/cvg_ex; exists (a * cos (- (pi / 2))).
  by apply: cvg_at_right_filter; exact: cF'.
have cvgr : cvg (a * cos x @[x --> (pi / 2)^'-]).
  apply/cvg_ex; exists (a * cos (pi / 2)).
  by apply: cvg_at_left_filter; exact: cF'.
have dLR : derivable_oo_LRcontinuous F (- (pi / 2)) (pi / 2).
  split.
  - by move=> x _; exact: (@ex_derive _ _ _ _ _ _ _ (dF x)).
  - by apply: cvg_at_right_filter; exact: cF.
  - by apply: cvg_at_left_filter; exact: cF.
have := h ab incr (fun x _ => cF' x) cvgl cvgr dLR (continuous_subspaceT cG).
move=> E; rewrite /Rintegral.
rewrite [X in fine X](_ : _ = (\int[mu]_(x in `[(- a)%R, a]) (G x)%:E)%E)//.
rewrite E.
have -> : (\int[mu]_(x in `[(- (pi / 2))%R, (pi / 2)%R])
    (((G \o F) * (fun t : R => a * cos t)) x)%:E =
    \int[mu]_(x in `[(- (pi / 2))%R, (pi / 2)%R]) ((a ^+ 2 * cos x ^+ 2)%:E))%E.
  apply: eq_integral => t; rewrite inE /= in_itv /= => /andP[t1 t2].
  congr EFin; rewrite /G /F /= !fctE.
  have c0 : 0 <= cos t by rewrite cos_ge0_pihalf// t1 t2.
  have -> : a ^+ 2 - (a * sin t) ^+ 2 = (a * cos t) ^+ 2.
    by rewrite !exprMn cos2sin2; ring.
  rewrite sqrtr_sqr ger0_norm; first by rewrite mulr_ge0// ltW.
  by rewrite -exprMn expr2.
rewrite -[LHS]/(\int[mu]_(x in `[- (pi / 2), pi / 2]) (a ^+ 2 * cos x ^+ 2)).
rewrite RintegralZl//; first last.
  by rewrite Rintegral_cos2 mulrC.
apply: continuous_compact_integrable; first exact: segment_compact.
apply: continuous_subspaceT => x.
by apply: (@continuousM _ _ cos cos); exact: continuous_cos.
Qed.

End disk_integral.

Section semicircle_density.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

Definition semicircle_pdf (r x : R) : R :=
  if r == 0 then \1_`[0, 1] x
  else 2 / (pi * r ^+ 2) * Num.sqrt (r ^+ 2 - x ^+ 2).

Lemma semicircle_pdfE r x : r != 0 ->
  semicircle_pdf r x = 2 / (pi * r ^+ 2) * Num.sqrt (r ^+ 2 - x ^+ 2).
Proof. by rewrite /semicircle_pdf => /negbTE ->. Qed.

Lemma semicircle_pdf_ge0 r x : 0 <= semicircle_pdf r x.
Proof.
rewrite /semicircle_pdf; case: ifP => _.
  by rewrite indicE; case: (_ \in _).
by rewrite mulr_ge0 ?sqrtr_ge0// divr_ge0// mulr_ge0// ?pi_ge0// sqr_ge0.
Qed.

Lemma semicircle_pdfN r x : r != 0 ->
  semicircle_pdf r (- x) = semicircle_pdf r x.
Proof. by move=> r0; rewrite !semicircle_pdfE// sqrrN. Qed.

Lemma semicircle_pdf_out r x : r != 0 -> r ^+ 2 <= x ^+ 2 ->
  semicircle_pdf r x = 0.
Proof.
by move=> r0 rx; rewrite semicircle_pdfE// ler0_sqrtr ?mulr0// subr_le0.
Qed.

Lemma continuous_semicircle_pdf r : r != 0 -> continuous (semicircle_pdf r).
Proof.
move=> r0; have -> : semicircle_pdf r =
    (fun x => 2 / (pi * r ^+ 2) * Num.sqrt (r ^+ 2 - x ^+ 2)).
  by apply/funext => x; rewrite semicircle_pdfE.
move=> x; apply: cvgM; first exact: cvg_cst.
apply: continuous_comp; last exact: sqrt_continuous.
by apply: continuousB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
Qed.

Lemma measurable_semicircle_pdf r : measurable_fun [set: R] (semicircle_pdf r).
Proof.
have [->|r0] := eqVneq r 0.
  have -> : semicircle_pdf 0 = \1_`[0, 1].
    by apply/funext => x; rewrite /semicircle_pdf eqxx.
  exact: measurable_indic.
by apply: continuous_measurable_fun; exact: continuous_semicircle_pdf.
Qed.

Lemma integral_semicircle_pdf_support r : r != 0 ->
  (\int[mu]_x (semicircle_pdf r x)%:E =
   \int[mu]_(x in `[(- `|r|)%R, `|r|%R]) (semicircle_pdf r x)%:E)%E.
Proof.
move=> r0; rewrite [RHS]integral_mkcond; apply: eq_integral => x _.
rewrite patchE; case: ifPn => // xI; rewrite semicircle_pdf_out//.
have : ~ (`|x| <= `|r|).
  move=> h; move/negP: xI; apply; rewrite inE /= in_itv /= -ler_norml.
  exact: h.
move=> /negP; rewrite -ltNge => /ltW h.
rewrite -[r ^+ 2]real_normK ?num_real// -[x ^+ 2]real_normK ?num_real//.
by rewrite ler_pXn2r// ?nnegrE// normr_ge0.
Qed.

Lemma integral_semicircle_pdf r : (\int[mu]_x (semicircle_pdf r x)%:E = 1)%E.
Proof.
have [->|r0] := eqVneq r 0.
  under eq_integral do rewrite /semicircle_pdf eqxx.
  by rewrite integral_indic//= setIT lebesgue_measure_itv/= lte01 oppr0 adde0.
rewrite integral_semicircle_pdf_support//; set a := `|r|.
have a0 : 0 < a by rewrite normr_gt0.
have ra : r ^+ 2 = a ^+ 2 by rewrite /a real_normK// num_real.
have ci : mu.-integrable `[- a, a] (EFin \o (semicircle_pdf r)).
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_subspaceT; exact: continuous_semicircle_pdf.
have fin : (\int[mu]_(x in `[(- a)%R, a]) (semicircle_pdf r x)%:E)%E
    \is a fin_num by exact: integrable_fin_num ci.
rewrite -(fineK fin) -[fine _]/(\int[mu]_(x in `[- a, a]) semicircle_pdf r x).
have -> : \int[mu]_(x in `[- a, a]) semicircle_pdf r x =
    \int[mu]_(x in `[- a, a]) (2 / (pi * a ^+ 2) * Num.sqrt (a ^+ 2 - x ^+ 2)).
  by apply: eq_Rintegral => x _; rewrite semicircle_pdfE// ra.
rewrite RintegralZl//.
  apply: continuous_compact_integrable; first exact: segment_compact.
  apply: continuous_subspaceT => x; apply: continuous_comp; last first.
    exact: sqrt_continuous.
  by apply: continuousB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
rewrite Rintegral_sqrt_disk//; congr EFin.
have pi0 : pi != 0 :> R by rewrite gt_eqF// pi_gt0.
have a2 : a ^+ 2 != 0 by rewrite expf_neq0// gt_eqF.
by move: (pi : R) (a ^+ 2) pi0 a2 => p q p0 q0; field.
Qed.

Lemma integrable_semicircle_pdf r :
  mu.-integrable [set: R] (fun x => (semicircle_pdf r x)%:E).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_semicircle_pdf.
under eq_integral do rewrite gee0_abs ?lee_fin ?semicircle_pdf_ge0//.
by rewrite integral_semicircle_pdf ltry.
Qed.

End semicircle_density.

Definition semicircle_prob {R : realType} (r : R) :
    set (measurableTypeR R) -> \bar R :=
  fun V => (\int[lebesgue_measure]_(x in V) (semicircle_pdf r x)%:E)%E.

(* HB declares canonical projections that the structures of the measure
   already provide; the warning says so. The setting lasts until the end of
   this file and is not exported. *)
Set Warnings "-redundant-canonical-projection".

Section semicircle_probability.
Context {R : realType} (r : R).
Local Notation mu := (@lebesgue_measure R).
Local Notation P := (semicircle_prob r).

Let P0 : P set0 = 0%E.
Proof. by rewrite /P integral_set0. Qed.

Let P_ge0 A : (0 <= P A)%E.
Proof.
by apply: integral_ge0 => x _; rewrite lee_fin semicircle_pdf_ge0.
Qed.

Let P_sigma_additive : semi_sigma_additive P.
Proof.
move=> /= A mA tA mUA.
rewrite /semicircle_prob/= integral_bigcup//=.
  apply: (integrableS measurableT mUA (subsetT _)).
  exact: integrable_semicircle_pdf.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin semicircle_pdf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ P P0 P_ge0 P_sigma_additive.

Let P_setT : P [set: _] = 1%E.
Proof. by rewrite /P integral_semicircle_pdf. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R P P_setT.

Lemma semicircle_prob_dominates : P `<< mu.
Proof.
apply/null_content_dominatesP => A mA muA0; rewrite /semicircle_prob.
have mf : measurable_fun A (fun x => (semicircle_pdf r x)%:E).
  apply/measurable_EFinP; apply: measurable_funTS.
  exact: measurable_semicircle_pdf.
have := @integral_abs_eq0 _ _ _ mu A _ mA mf muA0.
by under eq_integral do rewrite gee0_abs ?lee_fin ?semicircle_pdf_ge0//.
Qed.

End semicircle_probability.

Section semicircle_integral.
Context {R : realType} (r : R).
Local Notation mu := (@lebesgue_measure R).
Local Notation P := (semicircle_prob r).

Let RN_pdf : ae_eq mu [set: R] (Radon_Nikodym_SigmaFinite.f P mu)
  (fun x => (semicircle_pdf r x)%:E).
Proof.
apply: integral_ae_eq => //.
- exact: Radon_Nikodym_SigmaFinite.f_integrable (semicircle_prob_dominates r).
- by apply/measurable_EFinP; exact: measurable_semicircle_pdf.
- move=> E _ mE.
  by rewrite -(Radon_Nikodym_SigmaFinite.f_integral
    (semicircle_prob_dominates r) mE).
Qed.

Lemma ge0_integral_semicircle_prob (f : R -> \bar R) :
  (forall x, (0 <= f x)%E) -> measurable_fun [set: R] f ->
  (\int[P]_x f x = \int[mu]_x (f x * (semicircle_pdf r x)%:E))%E.
Proof.
move=> f0 mf.
rewrite -(Radon_Nikodym_SigmaFinite.change_of_variables
  (semicircle_prob_dominates r) f0 measurableT mf).
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //.
  exact: measurable_int
    (Radon_Nikodym_SigmaFinite.f_integrable (semicircle_prob_dominates r)).
- apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: measurable_semicircle_pdf.
- exact: ae_eqe_mul2l RN_pdf.
Qed.

Lemma integrable_semicircle_prob (f : R -> \bar R) :
  measurable_fun [set: R] f ->
  P.-integrable [set: R] f <->
  mu.-integrable [set: R] (fun x => f x * (semicircle_pdf r x)%:E)%E.
Proof.
move=> mf.
have mpdf : measurable_fun [set: R] (fun x => (semicircle_pdf r x)%:E).
  by apply/measurable_EFinP; exact: measurable_semicircle_pdf.
have E : (\int[P]_x `|f x| = \int[mu]_x `|f x * (semicircle_pdf r x)%:E|)%E.
  rewrite ge0_integral_semicircle_prob//; first by apply: measurableT_comp.
  apply: eq_integral => x _.
  by rewrite abseM (@gee0_abs _ (semicircle_pdf r x)%:E)// lee_fin
    semicircle_pdf_ge0.
split=> /integrableP[_ fi]; apply/integrableP; split.
- exact: emeasurable_funM.
- by rewrite -E.
- exact: mf.
- by rewrite E.
Qed.

Lemma integral_semicircle_prob (f : R -> \bar R) :
  P.-integrable [set: R] f ->
  (\int[P]_x f x = \int[mu]_x (f x * (semicircle_pdf r x)%:E))%E.
Proof.
move=> fi; have mf := measurable_int _ fi.
have p0 x : (0 <= (semicircle_pdf r x)%:E)%E.
  by rewrite lee_fin semicircle_pdf_ge0.
rewrite [LHS]integralE [RHS]integralE.
congr (_ - _)%E; rewrite ge0_integral_semicircle_prob//.
- exact: measurable_funepos.
- apply: eq_integral => x _; rewrite !funeposE.
  by rewrite muleC maxe_pMr// mule0 muleC.
- exact: measurable_funeneg.
- apply: eq_integral => x _; rewrite !funenegE.
  by rewrite muleC maxe_pMr// mule0 muleN muleC.
Qed.

Lemma semicircle_integrable_eq (f g : R -> R) : measurable_fun [set: R] g ->
  (forall x, g x * semicircle_pdf r x = f x * semicircle_pdf r x) ->
  mu.-integrable [set: R] (fun x => (f x * semicircle_pdf r x)%:E) ->
  P.-integrable [set: R] (EFin \o g).
Proof.
move=> mg gf fi; apply/integrable_semicircle_prob; first exact/measurable_EFinP.
by move: fi; apply: eq_integrable => // x _; rewrite /= -EFinM gf.
Qed.

Lemma semicircle_integral_eq (f g : R -> R) : P.-integrable [set: R] (EFin \o g) ->
  (forall x, g x * semicircle_pdf r x = f x * semicircle_pdf r x) ->
  \int[P]_x g x = \int[mu]_x (f x * semicircle_pdf r x).
Proof.
move=> gi gf; rewrite /Rintegral integral_semicircle_prob//; congr fine.
by apply: eq_integral => x _; rewrite /= -EFinM gf.
Qed.

Lemma semicircle_prob_sym (A : set (measurableTypeR R)) : r != 0 ->
  measurable A -> P ((fun x => - x) @^-1` A) = P A.
Proof.
move=> r0 mA; rewrite /semicircle_prob.
transitivity (\int[mu]_(x in (-%R : _ -> measurableTypeR R) @^-1` A)
    ((fun y => (semicircle_pdf r y)%:E) \o (-%R)) x)%E.
  by apply: eq_integral => x _ /=; rewrite semicircle_pdfN.
rewrite -ge0_integral_pushforward//.
- by apply/measurable_EFinP; apply: measurable_funTS;
    exact: measurable_semicircle_pdf.
- by move=> y _; rewrite lee_fin semicircle_pdf_ge0.
apply: eq_measure_integral => B mB _.
exact: lebesgue_measureN.
Qed.

End semicircle_integral.

Section semicircle_support.
Context {R : realType} (r : R).
Hypothesis r0 : r != 0.
Local Notation mu := (@lebesgue_measure R).
Local Notation P := (semicircle_prob r).
Local Notation a := `|r|.

Let a0 : 0 < a. Proof. by rewrite normr_gt0. Qed.

Let ra : r ^+ 2 = a ^+ 2. Proof. by rewrite real_normK// num_real. Qed.

Let pdf_out (x : R) : x \notin `[- a, a] -> semicircle_pdf r x = 0.
Proof.
move=> xI; rewrite semicircle_pdf_out//.
have : ~ (`|x| <= a).
  by move=> h; move/negP: xI; apply; rewrite in_itv /= -ler_norml.
move=> /negP; rewrite -ltNge => /ltW h.
rewrite -[r ^+ 2]real_normK ?num_real// -[x ^+ 2]real_normK ?num_real//.
by rewrite ler_pXn2r// ?nnegrE// normr_ge0.
Qed.

Let csqrt : continuous (fun x : R => Num.sqrt (a ^+ 2 - x ^+ 2)).
Proof.
move=> x; apply: continuous_comp; last exact: sqrt_continuous.
by apply: continuousB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
Qed.

Lemma integrable_semicircle_continuous (f : R -> R) : continuous f ->
  P.-integrable [set: R] (EFin \o f).
Proof.
move=> cf; apply/integrable_semicircle_prob.
  by apply/measurable_EFinP; exact: continuous_measurable_fun.
have -> : (fun x => (EFin \o f) x * (semicircle_pdf r x)%:E)%E =
    ((fun x => (f x * semicircle_pdf r x)%:E) \_ `[- a, a]).
  apply/funext => x; rewrite patchE; case: ifPn => [_|xI].
    by rewrite /= EFinM.
  by rewrite pdf_out ?mulr0 ?mule0//; apply: contra xI; rewrite inE.
apply: (proj1 (@integrable_mkcond _ _ _ mu `[- a, a]
  (fun x => (f x * semicircle_pdf r x)%:E) _)); first exact: measurable_itv.
apply: continuous_compact_integrable; first exact: segment_compact.
apply: continuous_subspaceT => x; apply: cvgM; first exact: cf.
exact: continuous_semicircle_pdf.
Qed.

Lemma integrable_semicircle_pdfM (f : R -> R) : continuous f ->
  mu.-integrable [set: R] (fun x => (f x * semicircle_pdf r x)%:E).
Proof.
move=> cf; have fi := integrable_semicircle_continuous cf.
have mf : measurable_fun [set: R] (EFin \o f).
  by apply/measurable_EFinP; exact: continuous_measurable_fun.
have := (integrable_semicircle_prob r mf).1 fi.
by apply: eq_integrable => // x _; rewrite /= EFinM.
Qed.

Lemma Rintegral_semicircle (f : R -> R) : P.-integrable [set: R] (EFin \o f) ->
  \int[P]_x f x = \int[mu]_(x in `[- a, a]) (f x * semicircle_pdf r x).
Proof.
move=> fi; rewrite /Rintegral integral_semicircle_prob//; congr fine.
rewrite [RHS]integral_mkcond; apply: eq_integral => x _; rewrite patchE.
case: ifPn => [_|xI]; first by rewrite /= EFinM.
by rewrite pdf_out ?mulr0 ?mule0//; apply: contra xI; rewrite inE.
Qed.

Let I k := \int[mu]_(x in `[- a, a]) (x ^+ k * Num.sqrt (a ^+ 2 - x ^+ 2)).

Let cI k : continuous (fun x : R => x ^+ k * Num.sqrt (a ^+ 2 - x ^+ 2)).
Proof. by move=> x; apply: cvgM; [exact: exprn_continuous|exact: csqrt]. Qed.

Let iI k : mu.-integrable `[- a, a]
  (EFin \o (fun x : R => x ^+ k * Num.sqrt (a ^+ 2 - x ^+ 2))).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
by apply: continuous_subspaceT; exact: cI.
Qed.

Let I_rec k : I k.+2 = k.+1%:R * a ^+ 2 / k.+4%:R * I k.
Proof.
pose u (x : R) := a ^+ 2 - x ^+ 2.
pose G (x : R) := - 3^-1 * (u x * Num.sqrt (u x)).
pose g (x : R) := x * Num.sqrt (u x).
pose F (x : R) := x ^+ k.+1.
pose f (x : R) := k.+1%:R * x ^+ k.
have dF (x : R) : is_derive x 1 F (f x).
  have := @is_deriveX _ _ (@id R) k.+1 x 1 1 (is_derive_id x 1).
  have -> : (@id R) ^+ k.+1 = F by apply/funext => y; rewrite /F exprfctE.
  move=> h; apply: (is_derive_eq h).
  by rewrite /f /GRing.scale /= mulr1.
have du (y : R) : is_derive y 1 u (- (2 * y)).
  have := is_deriveB (is_derive_cst (a ^+ 2) y 1)
    (@is_deriveX _ _ (@id R) 2 y 1 1 (is_derive_id y 1)).
  have -> : (cst (a ^+ 2) - (@id R) ^+ 2) = u.
    by apply/funext => z; rewrite /u /=.
  move=> h; apply: (is_derive_eq h).
  by rewrite /GRing.scale /= sub0r mulr1 expr1.
have u0 (x : R) : - a < x < a -> 0 < u x.
  move=> /andP[x1 x2]; rewrite /u subr_gt0 -[a ^+ 2]real_normK ?num_real//.
  rewrite -[x ^+ 2]real_normK ?num_real// ltr_pXn2r// ?nnegrE// ?normr_ge0//.
  by rewrite normr_id ltr_norml x1 x2.
have dG (x : R) : - a < x < a -> is_derive x 1 G (g x).
  move=> /u0 ux.
  have ds := @is_derive1_comp R Num.sqrt u x _ _ (is_derive1_sqrt ux) (du x).
  have := is_deriveZ (- 3^-1) (is_deriveM (du x) ds).
  have -> : (- 3^-1) \*: (u * (Num.sqrt \o u)) = G.
    by apply/funext => z; rewrite /G /= /GRing.scale /=.
  move=> h; apply: (is_derive_eq h); rewrite /g /GRing.scale /=.
  have s0 : 0 < Num.sqrt (u x) by rewrite sqrtr_gt0.
  have us : u x = Num.sqrt (u x) ^+ 2 by rewrite sqr_sqrtr// ltW.
  rewrite [in X in X * (_ * _)]us.
  move: (Num.sqrt (u x)) s0 => q q0.
  have qn0 : q != 0 by rewrite gt_eqF.
  by field.
have aa : - a < a by rewrite gtrN.
have cf : continuous f.
  by move=> x; apply: cvgM; [exact: cvg_cst|exact: exprn_continuous].
have cg : continuous g.
  by move=> x; apply: cvgM; [exact: cvg_id|exact: csqrt].
have cG : continuous G.
  move=> x; apply: cvgM; first exact: cvg_cst.
  apply: cvgM; last exact: csqrt.
  by apply: cvgB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
have cF : continuous F by move=> x; exact: exprn_continuous.
have dLRF : derivable_oo_LRcontinuous F (- a) a.
  split.
  - by move=> x _; exact: (@ex_derive _ _ _ _ _ _ _ (dF x)).
  - by apply: cvg_at_right_filter; exact: cF.
  - by apply: cvg_at_left_filter; exact: cF.
have dLRG : derivable_oo_LRcontinuous G (- a) a.
  split.
  - move=> x; rewrite in_itv /= => xI.
    exact: (@ex_derive _ _ _ _ _ _ _ (dG x xI)).
  - by apply: cvg_at_right_filter; exact: cG.
  - by apply: cvg_at_left_filter; exact: cG.
have F'f : {in `]- a, a[, F^`() =1 f}.
  by move=> x _; rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dF x)).
have G'g : {in `]- a, a[, G^`() =1 g}.
  move=> x; rewrite in_itv /= => xI.
  by rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dG x xI)).
have := @Rintegration_by_parts R F G f g (- a) a aa (continuous_subspaceT cf)
  dLRF F'f (continuous_subspaceT cg) dLRG G'g.
have Ga : G a = 0 by rewrite /G /u subrr sqrtr0 !mul0r mulr0.
have GNa : G (- a) = 0 by rewrite /G /u sqrrN subrr sqrtr0 !mul0r mulr0.
rewrite Ga GNa !mulr0 subrr sub0r.
have -> : \int[mu]_(x in `[- a, a]) (F x * g x) = I k.+2.
  by apply: eq_Rintegral => x _; rewrite /F /g /u mulrA -exprSr.
have ci (h0 : R -> R) : continuous h0 -> mu.-integrable `[- a, a] (EFin \o h0).
  move=> ch; apply: continuous_compact_integrable; first exact: segment_compact.
  exact: continuous_subspaceT.
have hk : mu.-integrable `[- a, a]
    (EFin \o (fun x : R => a ^+ 2 * (x ^+ k * Num.sqrt (a ^+ 2 - x ^+ 2)))).
  by apply: ci => x; apply: cvgM; [exact: cvg_cst|exact: cI].
have hB : mu.-integrable `[- a, a] (EFin \o (fun x : R =>
    a ^+ 2 * (x ^+ k * Num.sqrt (a ^+ 2 - x ^+ 2))
    - x ^+ k.+2 * Num.sqrt (a ^+ 2 - x ^+ 2))).
  apply: ci => x; apply: cvgB; last exact: cI.
  by apply: cvgM; [exact: cvg_cst|exact: cI].
have -> : \int[mu]_(x in `[- a, a]) (f x * G x) =
    - (k.+1%:R / 3) * (a ^+ 2 * I k - I k.+2).
  have E1 : a ^+ 2 * I k - I k.+2 = \int[mu]_(x in `[- a, a])
      (a ^+ 2 * (x ^+ k * Num.sqrt (a ^+ 2 - x ^+ 2))
       - x ^+ k.+2 * Num.sqrt (a ^+ 2 - x ^+ 2)).
    rewrite RintegralB//; congr (_ - _).
    by rewrite RintegralZl.
  rewrite E1 -RintegralZl//.
  apply: eq_Rintegral => x _; rewrite /f /G /u.
  by rewrite !exprSr; field.
have -> : (k.+4%:R : R) = k.+1%:R + 3 by rewrite -[3]/(3%:R) -natrD addnC.
move: (I k) (I k.+2) (k.+1%:R : R) (ler0n R k.+1) => A B K K0 e.
have K3 : K + 3 != 0 by rewrite gt_eqF// ltr_wpDl.
have e' : B * (K + 3) = K * a ^+ 2 * A by move: e; move: (a ^+ 2) => q; nra.
by rewrite -[B](mulfK K3) e' mulrAC.
Qed.

Let moment_I k : \int[P]_x ((x : R) ^+ k) = 2 / (pi * a ^+ 2) * I k.
Proof.
rewrite Rintegral_semicircle.
  by apply: integrable_semicircle_continuous; exact: exprn_continuous.
rewrite /I -RintegralZl//.
by apply: eq_Rintegral => x _; rewrite semicircle_pdfE// ra mulrCA.
Qed.

Lemma semicircle_momentS k : \int[P]_x ((x : R) ^+ k.+2) =
  k.+1%:R * r ^+ 2 / k.+4%:R * \int[P]_x ((x : R) ^+ k).
Proof. by rewrite !moment_I I_rec ra mulrCA. Qed.

Lemma semicircle_moment0 : \int[P]_x ((x : R) ^+ 0) = 1.
Proof.
under eq_Rintegral do rewrite expr0.
by rewrite Rintegral_cst// -[X in fine X]/(P setT) probability_setT /= mulr1.
Qed.

Lemma semicircle_moment2 : \int[P]_x ((x : R) ^+ 2) = r ^+ 2 / 4.
Proof. by rewrite (semicircle_momentS 0) semicircle_moment0 mulr1 mul1r. Qed.

Let I_odd k : I k.*2.+1 = 0.
Proof.
have := @integration_by_substitution_oppr R
  (fun x => x ^+ k.*2.+1 * Num.sqrt (a ^+ 2 - x ^+ 2)) (- a) a.
rewrite opprK.
have aa : - a <= a by have := a0; lra.
have cw : {within `[- a, a], continuous (fun x : R =>
    x ^+ k.*2.+1 * Num.sqrt (a ^+ 2 - x ^+ 2))}.
  by apply: continuous_subspaceT; exact: cI.
move=> /(_ aa cw) e.
have e2 : (\int[mu]_(x in `[(- a)%R, a])
    (((fun x0 : R => x0 ^+ k.*2.+1 * Num.sqrt (a ^+ 2 - x0 ^+ 2)) \o -%R) x)%:E
    = \int[mu]_(x in `[(- a)%R, a])
    (- (x ^+ k.*2.+1 * Num.sqrt (a ^+ 2 - x ^+ 2)))%:E)%E.
  apply: eq_integral => x _; congr EFin.
  rewrite /= sqrrN exprNn.
  have -> : (-1 : R) ^+ k.*2.+1 = -1.
    by rewrite exprS -mul2n exprM sqrrN expr1n expr1n mulr1.
  by rewrite mulN1r mulNr.
rewrite e2 in e; move: e => /(congr1 fine) /=.
rewrite -[X in X = _ -> _]/(I k.*2.+1).
rewrite -[X in _ = X -> _]/(\int[mu]_(x in `[- a, a])
  (- (x ^+ k.*2.+1 * Num.sqrt (a ^+ 2 - x ^+ 2)))).
under eq_Rintegral do rewrite -mulN1r.
rewrite RintegralZl// -/(I k.*2.+1).
by move: (I k.*2.+1) => J; lra.
Qed.

Lemma semicircle_moment_odd k : \int[P]_x ((x : R) ^+ k.*2.+1) = 0.
Proof. by rewrite moment_I I_odd mulr0. Qed.

Lemma semicircle_moment1 : \int[P]_x (x : R) = 0.
Proof.
by have := semicircle_moment_odd 0; under eq_Rintegral do rewrite expr1.
Qed.

Lemma semicircle_prob_gt0 (b : R) : b < a -> (0 < P `]b, +oo[%classic)%E.
Proof.
move=> ba; pose c := Num.max b (- a).
have ca : c < a by rewrite gt_max ba gtrN.
have cNa : - a <= c by rewrite le_max lexx orbT.
have bc : b <= c by rewrite le_max lexx.
pose u := (c + a) / 2; pose v := (u + a) / 2.
have cu : c < u by rewrite /u ltr_pdivlMr// mulrDr mulr1 ltrD2l.
have uv : u < v.
  by rewrite /v ltr_pdivlMr// mulrDr mulr1 ltrD2l /u ltr_pdivrMr// mulrDr mulr1
    ltrD2r.
have va : v < a.
  by rewrite /v ltr_pdivrMr// mulrDr mulr1 ltrD2r /u ltr_pdivrMr// mulrDr mulr1
    ltrD2r.
pose M := Num.max `|u| `|v|.
have Ma : M < a.
  rewrite gt_max !ltr_norml; apply/andP; split; apply/andP; split.
  - by apply: le_lt_trans cNa cu.
  - by apply: lt_trans uv va.
  - by apply: le_lt_trans cNa (lt_trans cu uv).
  - exact: va.
have M0 : 0 <= M by rewrite /M le_max normr_ge0.
have xM (x : R) : u <= x <= v -> x ^+ 2 <= M ^+ 2.
  move=> /andP[ux xv]; rewrite -[x ^+ 2]real_normK ?num_real//.
  rewrite ler_pXn2r ?nnegrE ?normr_ge0//.
  have [x0|x0] := leP 0 x.
    by rewrite ger0_norm// le_max (le_trans xv (ler_norm v)) orbT.
  by rewrite ltr0_norm// le_max ltr0_norm ?(le_lt_trans ux x0)// lerN2 ux.
pose k := 2 / (pi * a ^+ 2) * Num.sqrt (a ^+ 2 - M ^+ 2).
have Ma2 : M ^+ 2 < a ^+ 2 by rewrite ltr_pXn2r// nnegrE ltW.
have k0 : 0 < k.
  rewrite mulr_gt0// ?divr_gt0// ?mulr_gt0// ?pi_gt0// ?exprn_gt0//.
  by rewrite sqrtr_gt0 subr_gt0.
have sub : `[u, v]%classic `<=` `]b, +oo[%classic.
  move=> x; rewrite /= !in_itv /= => /andP[ux _]; rewrite andbT.
  by apply: le_lt_trans bc (lt_le_trans cu ux).
rewrite /semicircle_prob.
have mpdf : measurable_fun setT (fun x => (semicircle_pdf r x)%:E).
  by apply/measurable_EFinP; exact: measurable_semicircle_pdf.
apply: (@lt_le_trans _ _ (\int[mu]_(x in `[u, v]) (semicircle_pdf r x)%:E)%E).
  apply: (@lt_le_trans _ _ (\int[mu]_(x in `[u, v]) k%:E)%E).
    rewrite integral_cst//= lebesgue_measure_itv/= lte_fin uv -EFinM lte_fin.
    by rewrite mulr_gt0// subr_gt0.
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin ltW.
  - exact: measurable_funTS.
  move=> x; rewrite /= in_itv /= => xI; rewrite lee_fin semicircle_pdfE// ra.
  rewrite ler_pM2l ?divr_gt0 ?mulr_gt0 ?pi_gt0 ?exprn_gt0// ler_sqrt.
    by have := xM _ xI; move: (x ^+ 2) (M ^+ 2) (a ^+ 2) Ma2 => p q t; lra.
  by rewrite lerD2l lerN2 xM.
apply: ge0_subset_integral => //.
- exact: measurable_funTS.
- by move=> x _; rewrite lee_fin semicircle_pdf_ge0.
Qed.

Lemma semicircle_restrict (f : R -> R) :
  mu.-integrable [set: R] (fun x => (f x * semicircle_pdf r x)%:E) ->
  exists g : R -> R, [/\ measurable_fun [set: R] g,
    forall x, g x * semicircle_pdf r x = f x * semicircle_pdf r x &
    forall x, g x = 0 \/ g x = f x].
Proof.
move=> fi; pose J := `]- a, a[%classic : set R.
have mJ : measurable J by exact: measurable_itv.
have pJ x : J x -> 0 < semicircle_pdf r x.
  rewrite /J /= in_itv /= -ltr_norml => xa; rewrite semicircle_pdfE// ra.
  rewrite mulr_gt0 ?divr_gt0 ?mulr_gt0 ?pi_gt0 ?exprn_gt0// sqrtr_gt0 subr_gt0.
  by rewrite -[x ^+ 2]real_normK ?num_real// ltr_pXn2r// ?nnegrE ?normr_ge0.
have pO x : ~ J x -> semicircle_pdf r x = 0.
  move=> xI; apply: semicircle_pdf_out => //; rewrite ra.
  rewrite -[x ^+ 2]real_normK ?num_real// ler_pXn2r// ?nnegrE ?normr_ge0//.
  rewrite leNgt; apply/negP => xa; apply: xI.
  by rewrite /J /= in_itv /= -ltr_norml.
pose F x := f x * semicircle_pdf r x.
have mF : measurable_fun [set: R] F.
  by apply/measurable_EFinP; exact: measurable_int fi.
exists ((fun x => F x / semicircle_pdf r x) \_ J); split.
- apply/(measurable_restrictT (fun x => F x / semicircle_pdf r x) mJ).
  apply: measurable_funM; first exact: measurable_funS mF.
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE => xI; apply: continuousV; first by rewrite gt_eqF ?pJ.
  exact: continuous_semicircle_pdf.
- move=> x; rewrite patchE; case: ifPn => [|xI].
    by rewrite inE => xI; rewrite /F mulfK// gt_eqF ?pJ.
  have xJ : ~ J x by move=> h; move: xI; rewrite (mem_set h).
  by rewrite (pO x xJ) !mulr0.
- move=> x; rewrite patchE; case: ifPn => [|_]; last by left.
  by rewrite inE => xI; right; rewrite /F mulfK// gt_eqF ?pJ.
Qed.

End semicircle_support.

Section semicircle_scale.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

Lemma semicircle_pdf_scale (r a x : R) : 0 < r -> 0 < a ->
  a * semicircle_pdf (a * r) (a * x) = semicircle_pdf r x.
Proof.
move=> r0 a0.
have ar0 : a * r != 0 by rewrite mulf_neq0 // gt_eqF.
have rn0 : r != 0 by rewrite gt_eqF.
rewrite (semicircle_pdfE _ ar0) (semicircle_pdfE _ rn0).
have -> : (a * r) ^+ 2 - (a * x) ^+ 2 = a ^+ 2 * (r ^+ 2 - x ^+ 2) by ring.
rewrite sqrtrM ?exprn_ge0 ?ltW // sqrtr_sqr ger0_norm ?ltW //.
have an0 : a != 0 by rewrite gt_eqF.
rewrite exprMn !invfM.
transitivity ((a * a^-1) * (a * a^-1) *
  (2 * (pi^-1 * (r^-1 / r)) * Num.sqrt (r ^+ 2 - x ^+ 2))); first by ring.
by rewrite mulfV // !mul1r.
Qed.

(* The semicircle law of radius a r is the image of the one of radius r under
   x |-> a x. *)
Lemma ge0_integral_semicircle_scale (r a : R) (f : R -> \bar R) :
  0 < r -> 0 < a -> (forall x, (0 <= f x)%E) -> measurable_fun [set: R] f ->
  (\int[semicircle_prob r]_x f (a * x)%R =
   \int[semicircle_prob (a * r)%R]_x f x)%E.
Proof.
move=> r0 a0 f0 mf.
have mfa : measurable_fun [set: R] (fun x => f (a * x)).
  by apply: measurableT_comp => //; apply: measurable_funM.
rewrite ge0_integral_semicircle_prob // ge0_integral_semicircle_prob //.
pose h y := (f y * (semicircle_pdf (a * r) y)%:E)%E.
have h0 y : (0 <= h y)%E by rewrite /h mule_ge0 // lee_fin semicircle_pdf_ge0.
have mh : measurable_fun [set: R] h.
  apply: emeasurable_funM => //; apply/measurable_EFinP.
  exact: measurable_semicircle_pdf.
have an0 : a != 0 by rewrite gt_eqF.
have := ge0_integral_lebesgue_affine 0 an0 mh h0.
rewrite (gtr0_norm a0) => e.
have -> : (\int[mu]_x (f x * (semicircle_pdf (a * r) x)%:E))%E =
    (a%:E * \int[mu]_x h (a * x + 0)%R)%E.
  by rewrite e muleA -EFinM mulfV // mul1e.
have mha : measurable_fun [set: R] (fun x => h (a * x + 0)%R).
  exact: (measurableT_comp mh (measurable_affine a 0)).
have a0' : (0 <= a%:E)%E by rewrite lee_fin ltW.
rewrite -ge0_integralZl //.
apply: eq_integral => x _; rewrite /h addr0 muleCA -EFinM.
by rewrite semicircle_pdf_scale.
Qed.

End semicircle_scale.
