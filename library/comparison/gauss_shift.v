From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import normal_linear gauss_linear.

(**md**************************************************************************)
(* # Shifts of the standard Gaussian measure                                  *)
(*                                                                            *)
(* The Cameron-Martin formula for gauss n: shifting a vector of law gauss n   *)
(* by h multiplies its law by the density expR (<h, x> - |h|^2 / 2). For f    *)
(* nonnegative and measurable, E[f (x + h)] = E[f x expR (<h, x> - |h|^2 /    *)
(* 2)] (ge0_integral_gauss_shift); the same identity holds for every          *)
(* measurable f, with integrals in the extended reals (integral_gauss_shift), *)
(* and one side is integrable exactly when the other is                       *)
(* (integrable_gauss_shift). The one-dimensional case is                      *)
(* ge0_integral_normal_shift. The general case follows by induction on n,     *)
(* splitting off the first coordinate with rV_cons.                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section normal_shift.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Local Notation mu := (@lebesgue_measure R).

Lemma normal_pdf01_shift (a x : R) :
  normal_pdf 0 1 (x - a) = expR (a * x - a ^+ 2 / 2) * normal_pdf 0 1 x.
Proof.
rewrite !normal_pdfE ?oner_neq0// mulrCA; congr (_ * _).
by rewrite /normal_fun -expRD; congr expR; field.
Qed.

Lemma ge0_integral_normal_shift (a : R) (f : R -> \bar R) :
    measurable_fun [set: R] f -> (forall x, (0 <= f x)%E) ->
  (\int[N]_x f (x + a)%R = \int[N]_x (f x * (expR (a * x - a ^+ 2 / 2)%R)%:E))%E.
Proof.
move=> mf f0.
have mfa : measurable_fun [set: R] (fun x => f (x + a)).
  by apply: measurableT_comp => //; exact: measurable_funD.
have me : measurable_fun [set: R] (fun x => (expR (a * x - a ^+ 2 / 2))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funB => //; exact: measurable_funM.
have mfe := emeasurable_funM mf me.
have fe0 x : (0 <= f x * (expR (a * x - a ^+ 2 / 2))%:E)%E.
  by rewrite mule_ge0// lee_fin expR_ge0.
rewrite [LHS]ge0_integral_normal_prob ?oner_neq0//.
rewrite [RHS]ge0_integral_normal_prob ?oner_neq0//.
pose h x := (f x * (normal_pdf 0 1 (x - a))%:E)%E.
have mh : measurable_fun [set: R] h.
  apply: emeasurable_funM => //; apply/measurable_EFinP.
  apply: measurableT_comp; first exact: measurable_normal_pdf.
  exact: measurable_funB.
have h0 x : (0 <= h x)%E by rewrite mule_ge0// lee_fin normal_pdf_ge0.
transitivity (\int[mu]_x h (1 * x + a)%R)%E.
  by apply: eq_integral => x _; rewrite /h mul1r addrK.
rewrite ge0_integral_lebesgue_affine ?oner_neq0// normr1 invr1 mul1e.
by apply: eq_integral => x _; rewrite /h normal_pdf01_shift EFinM muleA.
Qed.

End normal_shift.

Section rV_cons_shift.
Context {R : realType} {n : nat}.

Lemma rV_cons_row_tail (h : 'rV[R]_n.+1) : h = rV_cons (h 0 ord0, row_tail h).
Proof.
apply/rowP => j; case: (unliftP ord0 j) => [j' ->|->].
  by rewrite rV_consS mxE.
by rewrite rV_cons0.
Qed.

Lemma rV_consD2 (t u : R) (v w : 'rV[R]_n) :
  rV_cons (t, v) + rV_cons (u, w) = rV_cons (t + u, v + w).
Proof.
apply/rowP => j; rewrite mxE; case: (unliftP ord0 j) => [j' ->|->].
  by rewrite !rV_consS mxE.
by rewrite !rV_cons0.
Qed.

Lemma measurable_mxdotl (a : 'rV[R]_n) : measurable_fun [set: 'rV[R]_n] (mxdot a).
Proof.
have -> : mxdot a = fun x => mxdot x a by apply/funext => x; rewrite mxdotC.
exact: measurable_mxdot.
Qed.

Lemma measurable_shift_density (h : 'rV[R]_n) (c : R) :
  measurable_fun [set: 'rV[R]_n] (fun x => (expR (mxdot h x - c))%:E).
Proof.
apply/measurable_EFinP; apply: measurableT_comp => //.
by apply: measurable_funB => //; exact: measurable_mxdotl.
Qed.

End rV_cons_shift.

Section gauss_shift.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Local Open Scope ereal_scope.

(* The Cameron-Martin formula: shifting a vector of law gauss n by h
   multiplies the law by the density expR (<h, x> - |h|^2 / 2). *)
Theorem ge0_integral_gauss_shift n (h : 'rV[R]_n) (f : 'rV[R]_n -> \bar R) :
    measurable_fun [set: 'rV[R]_n] f -> (forall x, 0 <= f x) ->
  \int[gauss n]_x f (x + h)%R =
  \int[gauss n]_x (f x * (expR (mxdot h x - mxdot h h / 2))%:E).
Proof.
elim: n h f => [|n IH] h f mf f0.
  have -> : h = 0%R by apply/rowP => -[].
  by apply: eq_integral => x _; rewrite addr0 !mxdot0l mul0r subrr expR0 mule1.
have mfh : measurable_fun [set: 'rV[R]_n.+1] (fun x => f (x + h)%R).
  by apply: measurableT_comp => //; apply: measurable_addmx.
have mfe := emeasurable_funM mf (measurable_shift_density h (mxdot h h / 2)%R).
have fe0 x : 0 <= f x * (expR (mxdot h x - mxdot h h / 2))%:E.
  by rewrite mule_ge0// lee_fin expR_ge0.
rewrite [LHS]ge0_integral_gauss_cons// [RHS]ge0_integral_gauss_cons//.
set h0 := h 0%R ord0; set h' := row_tail h.
have hE : h = rV_cons (h0, h') := rV_cons_row_tail h.
have mfc : measurable_fun [set: measurableTypeR R * 'rV[R]_n]
    (fun p => f (rV_cons (p.1, p.2 + h')%R)).
  apply: measurableT_comp => //; apply: measurableT_comp; first exact: measurable_rV_cons.
  apply: measurable_fun_pair; first exact: measurable_fst.
  by apply: measurable_addmx => //; exact: measurable_snd.
pose G (t : R) := \int[gauss n]_v f (rV_cons (t, v + h')%R).
have mG : measurable_fun [set: R] G.
  have := @measurable_fun_fubini_tonelli_F _ _ (measurableTypeR R) _ R (gauss n) _
    mfc (fun p => f0 _).
  exact.
have G0 t : 0 <= G t by apply: integral_ge0 => v _; exact: f0.
transitivity (\int[N]_t G (t + h0)%R).
  apply: eq_integral => t _; apply: eq_integral => v _.
  by rewrite hE rV_consD2.
rewrite ge0_integral_normal_shift//; apply: eq_integral => t _.
have mft : measurable_fun [set: 'rV[R]_n] (fun v => f (rV_cons (t, v))).
  apply: measurableT_comp => //; apply: measurableT_comp; first exact: measurable_rV_cons.
  by apply: measurable_fun_pair => //; exact: measurable_cst.
have me' := measurable_shift_density h' (mxdot h' h' / 2)%R.
have mfe' := emeasurable_funM mft me'.
have fe0' v : 0 <= f (rV_cons (t, v)) * (expR (mxdot h' v - mxdot h' h' / 2))%:E.
  by rewrite mule_ge0// lee_fin expR_ge0.
have e0 : 0 <= (expR (h0 * t - h0 ^+ 2 / 2))%:E by rewrite lee_fin expR_ge0.
rewrite /G (IH h' (fun v => f (rV_cons (t, v))))// -ge0_integralZr//.
apply: eq_integral => v _; rewrite -muleA -EFinM -expRD; congr (_ * (expR _)%:E).
rewrite (mxdotC h) mxdot_rV_cons mxdot_row_tail -/h0 -/h' (mxdotC v).
by field.
Qed.

Lemma integrable_gauss_shift n (h : 'rV[R]_n) (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f ->
  (gauss n).-integrable setT (fun x => f (x + h)%R) <->
  (gauss n).-integrable setT (fun x => f x * (expR (mxdot h x - mxdot h h / 2))%:E).
Proof.
move=> mf.
have mfa : measurable_fun [set: 'rV[R]_n] (fun x => `|f x|) by exact: measurableT_comp.
have E := ge0_integral_gauss_shift h mfa (fun x => abse_ge0 (f x)).
have me := measurable_shift_density h (mxdot h h / 2)%R.
have Ea : \int[gauss n]_x `|f x * (expR (mxdot h x - mxdot h h / 2))%:E| =
    \int[gauss n]_x (`|f x| * (expR (mxdot h x - mxdot h h / 2))%:E).
  apply: eq_integral => x _; rewrite abseM; congr (_ * _).
  by rewrite gee0_abs// lee_fin expR_ge0.
split=> /integrableP[_ fi]; apply/integrableP; split.
- exact: emeasurable_funM.
- by rewrite Ea -E.
- by apply: measurableT_comp => //; exact: measurable_addmx.
- by rewrite E -Ea.
Qed.

Lemma integral_gauss_shift n (h : 'rV[R]_n) (f : 'rV[R]_n -> \bar R) :
  measurable_fun [set: 'rV[R]_n] f ->
  \int[gauss n]_x f (x + h)%R =
  \int[gauss n]_x (f x * (expR (mxdot h x - mxdot h h / 2))%:E).
Proof.
move=> mf.
set e := fun x : 'rV[R]_n => expR (mxdot h x - mxdot h h / 2).
have e0 x : (0 < e x)%R by exact: expR_gt0.
rewrite integralE [RHS]integralE; congr (_ - _).
  transitivity (\int[gauss n]_x f^\+ (x + h)%R).
    by apply: eq_integral => x _; rewrite !funeposE.
  rewrite (ge0_integral_gauss_shift h (measurable_funepos mf) (funepos_ge0 f)).
  apply: eq_integral => x _; rewrite !funeposE -/(e x).
  have [fx0|fx0] := leP 0 (f x).
    by rewrite !max_l// mule_ge0// lee_fin ltW.
  by rewrite mul0e max_r// mule_le0_ge0// ?lee_fin ?ltW.
transitivity (\int[gauss n]_x f^\- (x + h)%R).
  by apply: eq_integral => x _; rewrite !funenegE.
rewrite (ge0_integral_gauss_shift h (measurable_funeneg mf) (funeneg_ge0 f)).
apply: eq_integral => x _; rewrite !funenegE -/(e x) -mulNe.
have [fx0|fx0] := leP 0 (- f x).
  by rewrite !max_l// mule_ge0// lee_fin ltW.
by rewrite mul0e max_r// mule_le0_ge0// ?lee_fin ?ltW.
Qed.

End gauss_shift.
