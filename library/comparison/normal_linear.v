From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import normal_integral.
From GaussianAnalysis.comparison Require Import normal_mgf.

(**md**************************************************************************)
(* # Linear images of normal laws                                             *)
(*                                                                            *)
(* Lebesgue measure on the line, pushed forward by x |-> a x + b with a != 0, *)
(* is |a|^-1 times Lebesgue measure (lebesgue_measure_affine,                 *)
(* ge0_integral_lebesgue_affine). Hence the image of normal_prob m s under x  *)
(* |-> a x + b is normal_prob (a m + b) (a s) (normal_prob_affine), and a     *)
(* linear combination a X + b Y of independent normal variables X and Y, with *)
(* b != 0, is normal (normal_prob_lincomb): its law is normal_prob (a m1 + b  *)
(* m2) (sqrt (a^2 s1^2 + b^2 s2^2)) when X and Y have laws normal_prob m1 s1  *)
(* and normal_prob m2 s2. The proof computes the convolution of the two       *)
(* densities (normal_pdf_conv).                                               *)
(*                                                                            *)
(* Laws are compared on measurable sets only: normal_prob m s A is the        *)
(* Lebesgue integral of normal_pdf m s over A, which MathComp-Analysis        *)
(* defines for every set A.                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section lebesgue_affine.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Implicit Types a b c d : R.

Lemma measurable_affine a b : measurable_fun [set: R] (fun x => a * x + b).
Proof. by apply: measurable_funD => //; exact: measurable_funM. Qed.

Lemma affine_preimage_itv_pos a b c d : 0 < a ->
  (fun x => a * x + b) @^-1` `]c, d] = `](c - b) / a, (d - b) / a]%classic.
Proof.
move=> a0; apply/seteqP; split => x /=; rewrite !in_itv/= ltr_pdivrMr// ler_pdivlMr//.
  by move=> /andP[cx xd]; apply/andP; split; lra.
by move=> /andP[cx xd]; apply/andP; split; lra.
Qed.

Lemma affine_preimage_itv_neg a b c d : a < 0 ->
  (fun x => a * x + b) @^-1` `]c, d] = `[(d - b) / a, (c - b) / a[%classic.
Proof.
move=> a0; apply/seteqP; split => x /=; rewrite !in_itv/= ler_ndivrMr// ltr_ndivlMr//.
  by move=> /andP[cx xd]; apply/andP; split; lra.
by move=> /andP[cx xd]; apply/andP; split; lra.
Qed.

Lemma lebesgue_measure_affine a b A : a != 0 -> measurable A ->
  mu ((fun x => a * x + b) @^-1` A) = ((`|a|^-1)%:E * mu A)%E.
Proof.
move=> a0 mA; pose f := fun x : R => a * x + b.
pose g : measurableTypeR R -> measurableTypeR R := f.
have mg : measurable_fun [set: measurableTypeR R] g := measurable_affine a b.
pose nu0 : {measure set (measurableTypeR R) -> \bar R} := pushforward mu g.
pose nu := mscale (NngNum (normr_ge0 a)) (nu0 mg).
have numu X : measurable X -> mu X = nu X.
  apply: (@lebesgue_measure_unique R nu) => _ [[c d] _ <-].
  rewrite /nu /mscale /nu0 /= /g /f /mscale /pushforward /=.
  have [a_neg|a_pos|a_eq] := ltgtP a 0; last by rewrite a_eq eqxx in a0.
    rewrite /pushforward affine_preimage_itv_neg// !lebesgue_measure_itv/= !lte_fin.
    have -> : ((d - b) / a < (c - b) / a) = (c < d).
      by rewrite ltr_nM2r ?invr_lt0// ltrD2r.
    case: ifP => cd; last by rewrite mule0.
    rewrite -!EFinD -EFinM ltr0_norm//; congr EFin.
    by field; rewrite lt_eqF.
  rewrite /pushforward affine_preimage_itv_pos// !lebesgue_measure_itv/= !lte_fin.
  have -> : ((c - b) / a < (d - b) / a) = (c < d).
    by rewrite ltr_pM2r ?invr_gt0// ltrD2r.
  case: ifP => cd; last by rewrite mule0.
  rewrite -!EFinD -EFinM gtr0_norm//; congr EFin.
  by field; rewrite gt_eqF.
rewrite (numu A mA) /nu /mscale /nu0 /pushforward /= /g /f muleA -EFinM.
by rewrite mulVf ?normr_eq0// mul1e.
Qed.

Lemma ge0_integral_lebesgue_affine a b (h : R -> \bar R) : a != 0 ->
    measurable_fun [set: R] h -> (forall x, (0 <= h x)%E) ->
  (\int[mu]_x h (a * x + b)%R = (`|a|^-1)%:E * \int[mu]_x h x)%E.
Proof.
move=> a0 mh h0; pose f := fun x : R => a * x + b.
pose g : measurableTypeR R -> measurableTypeR R := f.
have mg : measurable_fun [set: measurableTypeR R] g := measurable_affine a b.
have := @ge0_integral_pushforward _ _ _ _ R g mg mu setT h measurableT mh.
move=> /(_ (fun y _ => h0 y)); rewrite preimage_setT => <-.
have k0 : 0 <= `|a|^-1 by rewrite invr_ge0.
have -> : (`|a|^-1)%:E = (NngNum k0)%:num%:E by [].
rewrite -ge0_integral_mscale//; apply: eq_measure_integral => /= A mA _.
by rewrite /mscale /= /pushforward lebesgue_measure_affine.
Qed.

End lebesgue_affine.

Section normal_affine.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Implicit Types m s a b x : R.

Lemma normal_pdf_affine m s a b x : a != 0 -> s != 0 ->
  normal_pdf m s x = `|a| * normal_pdf (a * m + b) (a * s) (a * x + b).
Proof.
move=> a0 s0; rewrite !normal_pdfE ?mulf_neq0// /normal_peak /normal_fun.
have sp : Num.sqrt (s ^+ 2 * trigo.pi *+ 2) != 0.
  by rewrite sqrtr_eq0 -ltNge pmulrn_lgt0// mulr_gt0 ?exprn_even_gt0// trigo.pi_gt0.
have -> : (a * s) ^+ 2 * trigo.pi *+ 2 = a ^+ 2 * (s ^+ 2 * trigo.pi *+ 2) by ring.
rewrite sqrtrM ?sqr_ge0// sqrtr_sqr invfM.
have -> : a * x + b - (a * m + b) = a * (x - m) by ring.
have na : `|a| != 0 by rewrite normr_eq0.
have -> : - (a * (x - m)) ^+ 2 / ((a * s) ^+ 2 *+ 2) = - (x - m) ^+ 2 / (s ^+ 2 *+ 2).
  by field.
by field.
Qed.

Lemma normal_prob_affine m s a b A : a != 0 -> s != 0 -> measurable A ->
  normal_prob m s ((fun x => a * x + b) @^-1` A) =
  normal_prob (a * m + b) (a * s) A.
Proof.
move=> a0 s0 mA; rewrite /normal_prob integral_mkcond [RHS]integral_mkcond.
pose h := (fun y : R => (`|a| * normal_pdf (a * m + b) (a * s) y)%:E) \_ A.
have mh : measurable_fun [set: R] h.
  apply/(measurable_restrictT _ _).1 => //.
  apply/measurable_EFinP/measurable_funTS; apply: measurable_funM => //.
  exact: measurable_normal_pdf.
have h0 x : (0 <= h x)%E.
  rewrite /h /patch; case: ifP => // _.
  by rewrite lee_fin mulr_ge0// normal_pdf_ge0.
transitivity (\int[mu]_x h (a * x + b)%R)%E.
  apply: eq_integral => x _; rewrite /h /patch /= (normal_pdf_affine m b x a0 s0).
  have -> : (x \in (fun x0 => a * x0 + b) @^-1` A) = (a * x + b \in A).
    by apply/idP/idP => /set_mem H; apply/mem_set.
  by [].
rewrite ge0_integral_lebesgue_affine//.
transitivity ((`|a|^-1)%:E * \int[mu]_x ((`|a|)%:E *
    ((fun y : R => (normal_pdf (a * m + b) (a * s) y)%:E) \_ A) x))%E.
  congr (_ * _)%E; apply: eq_integral => x _; rewrite /h /patch.
  by case: ifP => _; rewrite ?mule0// EFinM.
rewrite ge0_integralZl//.
- apply/(measurable_restrictT _ _).1 => //.
  by apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
- by move=> x _; rewrite /patch; case: ifP => // _; rewrite lee_fin normal_pdf_ge0.
by rewrite muleA -EFinM mulVf ?normr_eq0// mul1e.
Qed.

Lemma normal_pdf_conv m1 s1 m2 s2 a b x z : s1 != 0 -> s2 != 0 -> b != 0 ->
  let S := Num.sqrt (a ^+ 2 * s1 ^+ 2 + b ^+ 2 * s2 ^+ 2) in
  normal_pdf m1 s1 x * normal_pdf (b * m2 + a * x) (b * s2) z =
  normal_pdf (a * m1 + b * m2) S z *
  normal_pdf ((m1 * b ^+ 2 * s2 ^+ 2 + a * (z - b * m2) * s1 ^+ 2) / S ^+ 2)
    (s1 * b * s2 / S) x.
Proof.
move=> s10 s20 b0 S.
have S2gt0 : 0 < a ^+ 2 * s1 ^+ 2 + b ^+ 2 * s2 ^+ 2.
  have h1 : 0 <= a ^+ 2 * s1 ^+ 2 by rewrite mulr_ge0 ?sqr_ge0.
  have h2 : 0 < b ^+ 2 * s2 ^+ 2 by rewrite mulr_gt0 ?exprn_even_gt0.
  lra.
have S2E : S ^+ 2 = a ^+ 2 * s1 ^+ 2 + b ^+ 2 * s2 ^+ 2 by rewrite sqr_sqrtr// ltW.
have S0 : S != 0 by rewrite gt_eqF// sqrtr_gt0.
have t0 : s1 * b * s2 / S != 0 by rewrite !mulf_neq0// invr_eq0.
rewrite !normal_pdfE ?mulf_neq0 ?invr_eq0// /normal_peak /normal_fun.
have -> : (s1 * b * s2 / S) ^+ 2 = s1 ^+ 2 * b ^+ 2 * s2 ^+ 2 / S ^+ 2.
  by rewrite expr_div_n !exprMn.
rewrite mulrACA [RHS]mulrACA -!expRD; congr (_ * expR _).
  rewrite -!invfM -!sqrtrM; first last.
  - by congr (_^-1); congr Num.sqrt; field.
  - by rewrite mulrn_wge0// mulr_ge0 ?sqr_ge0// trigo.pi_ge0.
  - by rewrite mulrn_wge0// mulr_ge0 ?sqr_ge0// trigo.pi_ge0.
rewrite S2E.
have S2' : (a * s1) ^+ 2 + (b * s2) ^+ 2 != 0 by rewrite !exprMn gt_eqF.
by field.
Qed.

Lemma normal_prob_lincomb m1 s1 m2 s2 a b A :
    s1 != 0 -> s2 != 0 -> b != 0 -> measurable A ->
  ((normal_prob m1 s1 \x normal_prob m2 s2) [set p | A (a * p.1 + b * p.2)%R] =
   normal_prob (a * m1 + b * m2)
     (Num.sqrt (a ^+ 2 * s1 ^+ 2 + b ^+ 2 * s2 ^+ 2)) A)%E.
Proof.
move=> s10 s20 b0 mA; set S := Num.sqrt _; rewrite /product_measure1 /=.
transitivity (\int[normal_prob m1 s1]_x normal_prob (b * m2 + a * x) (b * s2) A)%E.
  apply: eq_integral => x _; rewrite -normal_prob_affine//.
  by congr (normal_prob _ _ _); apply/seteqP; split => y;
    rewrite /xsection /= inE /= addrC.
pose g (p : R * R) := (normal_pdf (b * m2 + a * p.1) (b * s2) p.2 * \1_A p.2)%:E.
have mg : measurable_fun [set: R * R] g.
  apply/measurable_EFinP; apply: measurable_funM; last first.
    by apply: measurableT_comp => //; exact: measurable_indic.
  rewrite /normal_pdf mulf_eq0 (negbTE b0) (negbTE s20) /=.
  apply: measurable_funM => //; rewrite /normal_fun.
  apply: measurableT_comp => //; apply: measurable_funM => //.
  apply: measurableT_comp => //; apply: measurable_funX => //.
  apply: measurable_funB => //; apply: measurable_funD => //.
  by apply: measurable_funM => //; exact: measurable_fst.
have g0 p : (0 <= g p)%E by rewrite lee_fin mulr_ge0 ?normal_pdf_ge0.
have gE x : normal_prob (b * m2 + a * x) (b * s2) A = (\int[mu]_z g (x, z))%E.
  rewrite /normal_prob integral_mkcond; apply: eq_integral => z _.
  by rewrite /g /patch /= indicE; case: ifP => _; rewrite ?mulr1 ?mulr0.
under eq_integral do rewrite gE.
rewrite ge0_integral_normal_prob; first by move=> x; exact: integral_ge0.
  exact: (@measurable_fun_fubini_tonelli_F _ _ _ _ _ mu g mg g0).
transitivity (\int[mu]_x \int[mu]_z (g (x, z) * (normal_pdf m1 s1 x)%:E))%E.
  apply: eq_integral => x _; rewrite ge0_integralZr//.
  - apply/measurable_EFinP; apply: measurable_funM.
      exact: (measurable_normal_pdf (b * m2 + a * x) (b * s2)).
    exact: (measurable_indic mA).
  - by rewrite lee_fin normal_pdf_ge0.
pose h (p : R * R) := (g p * (normal_pdf m1 s1 p.1)%:E)%E.
have mh : measurable_fun [set: R * R] h.
  apply: emeasurable_funM => //; apply/measurable_EFinP.
  by apply: measurableT_comp => //; exact: measurable_normal_pdf.
have h0 p : (0 <= h p)%E by rewrite mule_ge0// lee_fin normal_pdf_ge0.
rewrite (@fubini_tonelli _ _ _ _ _ mu mu h mh h0).
transitivity (\int[mu]_z (normal_pdf (a * m1 + b * m2) S z * \1_A z)%:E)%E.
  apply: eq_integral => z _.
  have hE x : h (x, z) = ((normal_pdf (a * m1 + b * m2) S z * \1_A z)%:E *
      (normal_pdf ((m1 * b ^+ 2 * s2 ^+ 2 + a * (z - b * m2) * s1 ^+ 2) / S ^+ 2)
        (s1 * b * s2 / S) x)%:E)%E.
    rewrite /h /g /= -!EFinM; congr EFin.
    rewrite mulrAC [_ * normal_pdf m1 s1 x]mulrC.
    by rewrite (normal_pdf_conv m1 m2 a x z s10 s20 b0) -/S mulrAC.
  under eq_integral do rewrite hE.
  rewrite ge0_integralZl//.
  - by apply/measurable_EFinP; exact: measurable_normal_pdf.
  - by move=> x _; rewrite lee_fin normal_pdf_ge0.
  - by rewrite lee_fin mulr_ge0// normal_pdf_ge0.
  - by rewrite integral_normal_pdf mule1.
rewrite /normal_prob [RHS]integral_mkcond; apply: eq_integral => z _.
by rewrite /patch indicE; case: ifP => _; rewrite ?mulr1 ?mulr0.
Qed.

End normal_affine.
