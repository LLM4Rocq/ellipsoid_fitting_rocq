From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun.
From mathcomp Require Import exp measure lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import normal_mgf.

(**md**************************************************************************)
(* # Exponential moments and tails of chi-square variables                    *)
(*                                                                            *)
(* For X of law normal_prob 0 s and 2 t s^2 < 1, E[expR (t X^2)] = 1 / sqrt   *)
(* (1 - 2 t s^2) (integral_normal_expR_sqr). For the standard normal law,     *)
(* E[expR (t (X^2 - 1))] = expR (- t) / sqrt (1 - 2 t), which is at most expR *)
(* (t^2 / (1 - 2 |t|)) when |2 t| < 1 (integral_normal_expR_sqrB1_le), by the *)
(* inequality - ln (1 - u) - u <= u^2 / (2 (1 - |u|)) for |u| < 1             *)
(* (ln_subgamma).                                                             *)
(*                                                                            *)
(* For x of law gauss n and a row vector of weights a, centered_chi2 a x is a *)
(* centered weighted chi-square variable. Its moment generating function is   *)
(* the product of the one-dimensional ones                                    *)
(* (integral_gauss_expR_centered_chi2) and is sub-gamma: if |a_i| <= L for    *)
(* every i, then E[expR (t centered_chi2 a x)] <= expR (t^2 |a|^2 / (1 - 2    *)
(* |t| L)) when 2 |t| L < 1 (integral_gauss_expR_centered_chi2_le). It        *)
(* follows that P(|centered_chi2 a x| >= u) <= 2 expR (- u^2 / (4 (|a|^2 + L  *)
(* u))) for u > 0 (gauss_centered_chi2_abs_tail), with one-sided versions.    *)
(*                                                                            *)
(* ```                                                                        *)
(*   centered_chi2 a x == \sum_i a_i (x_i^2 - 1), for a x : 'rV[R]_n          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section normal_sqr_mgf.
Context {R : realType}.
Implicit Types s t u x : R.

Lemma normal_pdf_expR_sqr s t x : s != 0 -> 2 * t * s ^+ 2 < 1 ->
  expR (t * x ^+ 2) * normal_pdf 0 s x =
  (Num.sqrt (1 - 2 * t * s ^+ 2))^-1 *
    normal_pdf 0 (s / Num.sqrt (1 - 2 * t * s ^+ 2)) x.
Proof.
move=> s0 ts; set c := 1 - 2 * t * s ^+ 2.
have c0 : 0 < c by rewrite /c subr_gt0.
have sc0 : 0 < Num.sqrt c by rewrite sqrtr_gt0.
have s'0 : s / Num.sqrt c != 0 by rewrite mulf_neq0// invr_eq0 gt_eqF.
have pi2 : 0 < s ^+ 2 * trigo.pi *+ 2.
  by rewrite pmulrn_lgt0// mulr_gt0 ?exprn_even_gt0// trigo.pi_gt0.
rewrite !normal_pdfE// /normal_peak /normal_fun.
have -> : (s / Num.sqrt c) ^+ 2 = s ^+ 2 / c.
  by rewrite exprMn exprVn sqr_sqrtr// ltW.
have -> : Num.sqrt (s ^+ 2 / c * trigo.pi *+ 2) =
    Num.sqrt (s ^+ 2 * trigo.pi *+ 2) / Num.sqrt c.
  have -> : s ^+ 2 / c * trigo.pi *+ 2 = (s ^+ 2 * trigo.pi *+ 2) * c^-1.
    by ring.
  by rewrite sqrtrM ?sqrtrV ?ltW.
have -> : expR (- (x - 0) ^+ 2 / (s ^+ 2 / c *+ 2)) =
    expR (t * x ^+ 2) * expR (- (x - 0) ^+ 2 / (s ^+ 2 *+ 2)).
  have c1 : 1 - 2 * t * s ^+ 2 != 0 by rewrite gt_eqF.
  by rewrite -expRD; congr expR; rewrite /c; field.
have A0 : Num.sqrt (s ^+ 2 * trigo.pi *+ 2) != 0 by rewrite gt_eqF// sqrtr_gt0.
have B0 : Num.sqrt c != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma measurable_expR_sqr t :
  measurable_fun [set: R] (fun x : R => expR (t * x ^+ 2)).
Proof.
by apply: measurableT_comp => //; apply: measurable_funM.
Qed.

Lemma integral_normal_expR_sqr s t : s != 0 -> 2 * t * s ^+ 2 < 1 ->
  (\int[normal_prob 0 s]_x (expR (t * x ^+ 2))%:E =
   ((Num.sqrt (1 - 2 * t * s ^+ 2))^-1)%:E)%E.
Proof.
move=> s0 ts; rewrite ge0_integral_normal_prob//.
  by apply/measurable_EFinP; exact: measurable_expR_sqr.
under eq_integral do rewrite -EFinM normal_pdf_expR_sqr// EFinM.
rewrite ge0_integralZl//.
- by apply/measurable_EFinP; exact: measurable_normal_pdf.
- by move=> x _; rewrite lee_fin normal_pdf_ge0.
- by rewrite integral_normal_pdf mule1.
Qed.

Lemma integrable_normal_expR_sqr s t : s != 0 -> 2 * t * s ^+ 2 < 1 ->
  (normal_prob 0 s).-integrable setT (fun x => (expR (t * x ^+ 2))%:E).
Proof.
move=> s0 ts; apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_expR_sqr.
under eq_integral do rewrite gee0_abs ?lee_fin ?expR_ge0//.
by rewrite integral_normal_expR_sqr// ltry.
Qed.

Lemma integral_normal_expR_sqrB1 t : 2 * t < 1 ->
  (\int[normal_prob 0 1]_x (expR (t * (x ^+ 2 - 1)))%:E =
   (expR (- t) / Num.sqrt (1 - 2 * t))%:E)%E.
Proof.
move=> t2; have t2' : 2 * t * 1 ^+ 2 < 1 by rewrite expr1n mulr1.
under eq_integral do rewrite mulrBr mulr1 addrC expRD EFinM.
rewrite ge0_integralZl//.
  by apply/measurable_EFinP; exact: measurable_expR_sqr.
by rewrite integral_normal_expR_sqr ?oner_eq0// expr1n mulr1 -EFinM.
Qed.

End normal_sqr_mgf.

Section subgamma.
Context {R : realType}.
Implicit Types t u y : R.

Lemma ln_ge_half_sub_inv y : 0 < y <= 1 -> (y - y^-1) / 2 <= ln y.
Proof.
move=> /andP[y0 y1].
pose h (z : R) := ln z - (z - z^-1) / 2.
have dh (z : R) : 0 < z -> is_derive z 1 h (z^-1 - (1 + z ^- 2) / 2).
  move=> z0; rewrite /h; apply: is_derive_eq; first apply: is_deriveB.
  - exact: is_derive1_ln.
  - apply: is_deriveM; apply: is_deriveB.
    by apply: is_deriveV; first by rewrite gt_eqF.
  rewrite /= !scaler0 add0r.
  change (z^-1 - 2^-1 * (1 - (- z ^- 2 * 1)) = z^-1 - (1 + z ^- 2) / 2).
  by rewrite mulr1 opprK mulrC.
have dhle (z : R) : 0 < z -> z^-1 - (1 + z ^- 2) / 2 <= 0.
  move=> z0; have z0' : z != 0 by rewrite gt_eqF.
  have -> : z^-1 - (1 + z ^- 2) / 2 = - (1 - z^-1) ^+ 2 / 2 by field.
  by rewrite mulNr oppr_le0 divr_ge0// sqr_ge0.
have hd (z : R) : 0 < z -> derivable h z 1.
  by move=> z0; have := dh z z0; case.
have : h 1 <= h y.
  apply: (@ler0_derive1_le_cc _ h y 1) => //.
  - move=> z; rewrite in_itv/= => /andP[yz _]; apply: hd.
    exact: lt_trans yz.
  - move=> z; rewrite in_itv/= => /andP[yz _].
    have z0 : 0 < z by exact: lt_trans yz.
    by rewrite derive1E; case: (dh z z0) => _ ->; exact: dhle.
  - apply: derivable_within_continuous => z; rewrite in_itv/= => /andP[yz _].
    by apply: hd; exact: lt_le_trans yz.
  - by rewrite in_itv/= lexx y1.
  - by rewrite in_itv/= y1 lexx.
by rewrite /h ln1 invr1 subrr mul0r subr0 subr_ge0.
Qed.

Lemma ln_ge_sub_half_sqr y : 1 <= y -> (y - 1) - (y - 1) ^+ 2 / 2 <= ln y.
Proof.
move=> y1; have y0 : 0 < y by exact: lt_le_trans y1.
pose h (z : R) := ln z - ((z - 1) - (z - 1) ^+ 2 / 2).
have dh (z : R) : 0 < z -> is_derive z 1 h (z^-1 - (1 - (z - 1))).
  move=> z0; rewrite /h; apply: is_derive_eq; first apply: is_deriveB.
    exact: is_derive1_ln.
  rewrite /= !scaler0 add0r.
  change (z^-1 - (1 - 0 - 2^-1 * ((z - 1) * (1 - 0) + (z - 1) * (1 - 0))) =
    z^-1 - (1 - (z - 1))).
  have z0' : z != 0 by rewrite gt_eqF.
  by field.
have dhge (z : R) : 0 < z -> 0 <= z^-1 - (1 - (z - 1)).
  move=> z0; have z0' : z != 0 by rewrite gt_eqF.
  have -> : z^-1 - (1 - (z - 1)) = (z - 1) ^+ 2 / z by field.
  by rewrite divr_ge0 ?sqr_ge0// ltW.
have hd (z : R) : 0 < z -> derivable h z 1.
  by move=> z0; have := dh z z0; case.
have : h 1 <= h y.
  apply: (@ger0_derive1_le_cc _ h 1 y) => //.
  - move=> z; rewrite in_itv/= => /andP[z1 _]; apply: hd.
    exact: lt_trans z1.
  - move=> z; rewrite in_itv/= => /andP[z1 _].
    have z0 : 0 < z by exact: lt_trans z1.
    by rewrite derive1E; case: (dh z z0) => _ ->; exact: dhge.
  - apply: derivable_within_continuous => z; rewrite in_itv/= => /andP[z1 _].
    by apply: hd; exact: lt_le_trans z1.
  - by rewrite in_itv/= lexx y1.
  - by rewrite in_itv/= y1 lexx.
by rewrite /h ln1 subrr expr0n /= mul0r subr0 subr0 subr_ge0.
Qed.

Lemma ln_subgamma u : `|u| < 1 -> - ln (1 - u) - u <= u ^+ 2 / (2 * (1 - `|u|)).
Proof.
move=> u1; have u1' : 0 < 1 - `|u| by rewrite subr_gt0.
have [u0|u0] := leP 0 u.
  rewrite ger0_norm// in u1 u1' *.
  have y0 : 0 < 1 - u <= 1 by rewrite u1' lerBlDr lerDl.
  have := ln_ge_half_sub_inv y0.
  have u1'' : 1 - u != 0 by rewrite gt_eqF.
  have -> : ((1 - u) - (1 - u)^-1) / 2 = - u - u ^+ 2 / (2 * (1 - u)) by field.
  by move=> h; lra.
rewrite ltr0_norm// in u1 u1' *.
have y1 : 1 <= 1 - u by rewrite lerDl oppr_ge0 ltW.
have := ln_ge_sub_half_sqr y1.
have -> : 1 - u - 1 = - u by ring.
rewrite sqrrN => h.
apply: (@le_trans _ _ (u ^+ 2 / 2)); first lra.
apply: ler_pM; [exact: sqr_ge0|by rewrite invr_ge0|done|].
by rewrite lef_pV2 ?posrE ?mulr_gt0// opprK; lra.
Qed.

End subgamma.

Section normal_sqr_mgf_le.
Context {R : realType}.
Implicit Types t : R.

Lemma integral_normal_expR_sqrB1_le t : `|2 * t| < 1 ->
  (\int[normal_prob 0 1]_x (expR (t * (x ^+ 2 - 1)))%:E <=
   (expR (t ^+ 2 / (1 - 2 * `|t|)))%:E)%E.
Proof.
move=> t1; have t2 : 2 * t < 1 by rewrite (le_lt_trans (ler_norm _)).
rewrite integral_normal_expR_sqrB1// lee_fin.
have c0 : 0 < 1 - 2 * t by rewrite subr_gt0.
rewrite -powR12_sqrt; first exact: ltW.
rewrite /powR (gt_eqF c0) -expRN -expRD ler_expR.
have := ln_subgamma t1; rewrite normrM (@ger0_norm _ 2)//.
have t1' : 0 < 1 - 2 * `|t|.
  by rewrite subr_gt0 -[X in X * _](@ger0_norm _ 2)// -normrM.
have -> : (2 * t) ^+ 2 / (2 * (1 - 2 * `|t|)) = 2 * (t ^+ 2 / (1 - 2 * `|t|)).
  have t1'' : 1 - 2 * `|t| != 0 by rewrite gt_eqF.
  by field.
by move=> h; lra.
Qed.

End normal_sqr_mgf_le.

Section centered_chi2.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (t u L : R).

Definition centered_chi2 n (a x : 'rV[R]_n) : R := \sum_i a 0 i * (x 0 i ^+ 2 - 1).

Lemma measurable_centered_chi2 n (a : 'rV[R]_n) :
  measurable_fun [set: 'rV[R]_n] (centered_chi2 a).
Proof.
rewrite /centered_chi2; apply: measurable_sum => i; apply: measurable_funM => //.
apply: measurable_funB => //; apply: measurable_funX.
exact: measurable_mxentry.
Qed.

Lemma integral_gauss_expR_centered_chi2 n (a : 'rV[R]_n) t :
  (forall i, 2 * (t * a 0 i) < 1) ->
  (\int[gauss n]_x (expR (t * centered_chi2 a x))%:E =
   (\prod_i (expR (- (t * a 0 i)) / Num.sqrt (1 - 2 * (t * a 0 i))))%:E)%E.
Proof.
move=> ta.
have E x : expR (t * centered_chi2 a x) =
    \prod_i expR (t * a 0 i * (x 0 i ^+ 2 - 1)).
  by rewrite /centered_chi2 mulr_sumr expR_sum; apply: eq_bigr => i _; rewrite mulrA.
under eq_integral do rewrite E.
rewrite (@ge0_integral_gauss_prod R n (fun i s => expR (t * a 0 i * (s ^+ 2 - 1)))).
- move=> i; apply: measurableT_comp => //; apply: measurable_funM => //.
  by apply: measurable_funB => //; exact: measurable_funX.
- by move=> i s; exact: expR_ge0.
rewrite -prodEFin; apply: eq_bigr => i _.
exact: integral_normal_expR_sqrB1.
Qed.

Lemma integral_gauss_expR_centered_chi2_le n (a : 'rV[R]_n) t L :
  (forall i, `|a 0 i| <= L) -> `|2 * t| * L < 1 ->
  (\int[gauss n]_x (expR (t * centered_chi2 a x))%:E <=
   (expR (t ^+ 2 * mxdot a a / (1 - 2 * `|t| * L)))%:E)%E.
Proof.
move=> aL tL; have taL i : `|2 * (t * a 0 i)| <= `|2 * t| * L.
  by rewrite mulrA normrM ler_wpM2l.
have ta i : 2 * (t * a 0 i) < 1.
  by rewrite (le_lt_trans (ler_norm _))// (le_lt_trans (taL i)).
rewrite integral_gauss_expR_centered_chi2// lee_fin.
have -> : t ^+ 2 * mxdot a a / (1 - 2 * `|t| * L) =
    \sum_i t ^+ 2 * a 0 i ^+ 2 / (1 - 2 * `|t| * L).
  rewrite /mxdot big_ord1 mulr_sumr mulr_suml; apply: eq_bigr => i _.
  by rewrite expr2 mulrA.
rewrite expR_sum; apply: ler_prod => i _; apply/andP; split.
  by rewrite divr_ge0 ?expR_ge0 ?sqrtr_ge0.
have ti1 : `|2 * (t * a 0 i)| < 1 by exact: le_lt_trans (taL i) tL.
have := integral_normal_expR_sqrB1_le ti1.
rewrite integral_normal_expR_sqrB1// lee_fin => /le_trans; apply.
rewrite ler_expR exprMn; apply: ler_wpM2l; first by rewrite mulr_ge0 ?sqr_ge0.
have h1 : 2 * `|t * a 0 i| <= 2 * `|t| * L.
  by have := taL i; rewrite !normrM (@ger0_norm _ 2)// mulrA.
have h2 : 0 < 1 - 2 * `|t| * L.
  by rewrite subr_gt0 -(@ger0_norm _ 2)// -normrM.
by rewrite lef_pV2 ?posrE ?lerB// (lt_le_trans h2)// lerB.
Qed.

Theorem gauss_centered_chi2_upper_tail n (a : 'rV[R]_n) L u :
  0 <= L -> (forall i, `|a 0 i| <= L) -> 0 < u -> 0 < mxdot a a + L * u ->
  (gauss n [set x | u <= centered_chi2 a x]%R <=
   (expR (- u ^+ 2 / (4 * (mxdot a a + L * u))))%:E)%E.
Proof.
move=> L0 aL u0 vLu; have [->|a0] := eqVneq a 0.
  have -> : [set x : 'rV[R]_n | u <= centered_chi2 0 x] = set0.
    apply/seteqP; split => x //=.
    have -> : centered_chi2 0 x = 0.
      by rewrite /centered_chi2 big1// => i _; rewrite mxE mul0r.
    by rewrite leNgt u0.
  by rewrite measure0 lee_fin expR_ge0.
set v := mxdot a a; have v0 : 0 < v by rewrite /v mxdot_gt0.
have vLu' : v + L * u != 0 by rewrite gt_eqF.
set t := u / (2 * (v + L * u)).
have t0 : 0 <= t by rewrite divr_ge0// ?mulr_ge0// ltW.
have tL : `|2 * t| * L < 1.
  rewrite ger0_norm ?mulr_ge0// /t.
  - exact: ltW.
  - by rewrite invr_ge0 mulr_ge0// ltW.
  have -> : 2 * (u / (2 * (v + L * u))) * L = L * u / (v + L * u) by field.
  by rewrite ltr_pdivrMr// mul1r ltrDr.
apply: (le_trans (measure_ge_expR (gauss n) u (measurable_centered_chi2 a) t0)).
under eq_integral do rewrite mulrBr expRD EFinM.
rewrite ge0_integralZr//.
  by apply/measurable_EFinP; apply: measurableT_comp => //;
    apply: measurable_funM => //; exact: measurable_centered_chi2.
apply: (le_trans (lee_wpmul2r _ (integral_gauss_expR_centered_chi2_le aL tL))).
  by rewrite lee_fin expR_ge0.
rewrite -EFinM -expRD lee_fin ler_expR (ger0_norm t0) -/v.
have v0' : v != 0 by rewrite gt_eqF.
have -> : 1 - 2 * t * L = v / (v + L * u) by rewrite /t; field.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite /t; field.
Qed.

Lemma centered_chi2N n (a x : 'rV[R]_n) :
  centered_chi2 (- a) x = - centered_chi2 a x.
Proof.
by rewrite /centered_chi2 -sumrN; apply: eq_bigr => i _; rewrite mxE mulNr.
Qed.

Theorem gauss_centered_chi2_lower_tail n (a : 'rV[R]_n) L u :
  0 <= L -> (forall i, `|a 0 i| <= L) -> 0 < u -> 0 < mxdot a a + L * u ->
  (gauss n [set x | centered_chi2 a x <= - u]%R <=
   (expR (- u ^+ 2 / (4 * (mxdot a a + L * u))))%:E)%E.
Proof.
move=> L0 aL u0 vLu.
have -> : [set x | centered_chi2 a x <= - u]%R =
    [set x | u <= centered_chi2 (- a) x]%R.
  by apply/seteqP; split => x /=; rewrite centered_chi2N lerNr.
rewrite -[mxdot a a]opprK -mxdotNl -mxdotNr.
apply: gauss_centered_chi2_upper_tail => //.
- by move=> i; rewrite mxE normrN.
- by rewrite mxdotNl mxdotNr opprK.
Qed.

Theorem gauss_centered_chi2_abs_tail n (a : 'rV[R]_n) L u :
  0 <= L -> (forall i, `|a 0 i| <= L) -> 0 < u -> 0 < mxdot a a + L * u ->
  (gauss n [set x | u <= `|centered_chi2 a x|]%R <=
   (2 * expR (- u ^+ 2 / (4 * (mxdot a a + L * u))))%:E)%E.
Proof.
move=> L0 aL u0 vLu.
have -> : [set x | u <= `|centered_chi2 a x|]%R =
    [set x | u <= centered_chi2 a x]%R `|` [set x | centered_chi2 a x <= - u]%R.
  apply/seteqP; split => x /=; first by rewrite ler_normr => /orP[|]; [left|right; lra].
  by move=> [h|h]; rewrite ler_normr; apply/orP; [left|right; lra].
have mQ := measurable_centered_chi2 a.
apply: (le_trans (measureU2 _ _ _)).
- have -> : [set x | u <= centered_chi2 a x]%R = centered_chi2 a @^-1` `[u, +oo[.
    by rewrite preimage_itvcy.
  by rewrite -[X in measurable X]setTI; apply: mQ => //; exact: measurable_itv.
- have -> : [set x | centered_chi2 a x <= - u]%R = centered_chi2 a @^-1` `]-oo, - u].
    by rewrite preimage_itvNyc.
  by rewrite -[X in measurable X]setTI; apply: mQ => //; exact: measurable_itv.
rewrite mulr_natl mulr2n EFinD.
apply: leeD; first exact: gauss_centered_chi2_upper_tail.
exact: gauss_centered_chi2_lower_tail.
Qed.

End centered_chi2.
