From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution ftc.
From GaussianAnalysis.gaussian Require Import normal_integral gauss.
From GaussianAnalysis.gaussian Require Import parameter_integral.
From GaussianAnalysis.comparison Require Import normal_mgf normal_linear.
From GaussianAnalysis.comparison Require Import gauss_smoothing.

(**md**************************************************************************)
(* # The Ornstein-Uhlenbeck semigroup                                         *)
(*                                                                            *)
(* For f : R -> R bounded and measurable, the Mehler transform mehler r f x   *)
(* is E[f (r x + sqrt (1 - r^2) Z)] for Z of law normal_prob 0 1, and the     *)
(* Ornstein-Uhlenbeck semigroup is ou t f = mehler (expR (- t)) f (Mehler's   *)
(* formula, ouE). Then mehler 1 f = f and mehler 0 f is the mean of f         *)
(* (mehler1, mehler0, ou0), mehler r f keeps the bounds of f (mehler_le,      *)
(* mehler_ge), the standard normal law is invariant (integral_mehler) and     *)
(* mehler r is a contraction of L^1 of that law (mehler_contraction).         *)
(*                                                                            *)
(* For |r| < 1 the law of r x + sqrt (1 - r^2) Z has the density              *)
(* mehler_kernel r x against normal_prob 0 1 (mehler_kernel_integral): the    *)
(* exponential of a quadratic polynomial in x and y. Differentiating it under *)
(* the integral (is_derive_normal_kernel) gives the derivatives of mehler r f *)
(* of order 1, 2 and 3 in x and the derivative in r (is_derive_mehler,        *)
(* is_derive_mehler_d1, is_derive_mehler_d2, is_derive_mehler_r), written as  *)
(* integrals against Hermite polynomials. They satisfy the generator identity *)
(* r d/dr mehler r f = x (mehler r f)' - (mehler r f)'' (mehler_generator);   *)
(* for t > 0 it reads d/dt ou t f = (ou t f)'' - x (ou t f)'                  *)
(* (is_derive_ou_t). The derivatives are bounded (mehler_d1_le, mehler_d2_le, *)
(* mehler_dr_le) and continuous (continuous_mehler, continuous_mehler_d1,     *)
(* continuous_mehler_d2).                                                     *)
(* The kernel gives the derivative in t as well as those in x, so it replaces *)
(* the Cameron-Martin formula, which only shifts x.                           *)
(*                                                                            *)
(* As t -> +oo, ou t f x tends to the mean of f (ou_cvgy). As t -> 0 from the *)
(* right, ou t f x tends to f x when f is continuous (ou_cvg0, mehler_cvg1),  *)
(* and ou t f tends to f in L^1 of the standard normal law for every bounded  *)
(* measurable f (ou_cvg0_L1, mehler_cvg_L1). The last limit goes through the  *)
(* density of bounded continuous functions in that space                      *)
(* (normal_continuous_approx), which follows from the density of continuous   *)
(* functions in L^1 of Lebesgue measure on a segment                          *)
(* (approximation_continuous_integrable of MathComp-Analysis).                *)
(*                                                                            *)
(* ```                                                                        *)
(*     mehler_kernel r x y == the density at y, against normal_prob 0 1, of   *)
(*                            the law of r x + sqrt (1 - r^2) Z, |r| < 1      *)
(*            mehler r f x == E[f (r x + b Z)], with b = sqrt (1 - r^2)       *)
(*         mehler_d1 r f x == r / b * E[f (r x + b Z) Z], the derivative of   *)
(*                            mehler r f at x                                 *)
(*         mehler_d2 r f x == r^2 / b^2 * E[f (r x + b Z) (Z^2 - 1)]          *)
(*         mehler_d3 r f x == r^3 / b^3 * E[f (r x + b Z) (Z^3 - 3 Z)]        *)
(*         mehler_dr r f x == E[f (r x + b Z) (x Z / b - r (Z^2 - 1) / b^2)], *)
(*                            the derivative of r |-> mehler r f x            *)
(*                ou t f x == mehler (expR (- t)) f x                         *)
(*       mehler_bound r1 X == a constant C such that the kernel times a       *)
(*                            polynomial factor of degree 3 is at most        *)
(*                            C expR (c |y|) for |r| <= r1 < 1, |x| <= X      *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section mehler_def.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (r x y : R) (f : R -> R).

(* The density at y, against the standard normal law, of the law of
   r x + sqrt (1 - r^2) Z for Z standard normal, when |r| < 1. *)
Definition mehler_kernel r x y : R :=
  expR (- ln (1 - r ^+ 2) / 2 +
    (2 * r * x * y - r ^+ 2 * (x ^+ 2 + y ^+ 2)) / (2 * (1 - r ^+ 2))).

(* The Mehler transform with correlation r: E[f (r x + sqrt (1 - r^2) Z)]. *)
Definition mehler r f x : R :=
  \int[N]_z f (r * x + Num.sqrt (1 - r ^+ 2) * z).

(* Its derivatives of order 1, 2 and 3 in x, and its derivative in r. *)
Definition mehler_d1 r f x : R :=
  r / Num.sqrt (1 - r ^+ 2) *
  \int[N]_z (f (r * x + Num.sqrt (1 - r ^+ 2) * z) * z).

Definition mehler_d2 r f x : R :=
  r ^+ 2 / (1 - r ^+ 2) *
  \int[N]_z (f (r * x + Num.sqrt (1 - r ^+ 2) * z) * (z ^+ 2 - 1)).

Definition mehler_d3 r f x : R :=
  r ^+ 3 / Num.sqrt (1 - r ^+ 2) ^+ 3 *
  \int[N]_z (f (r * x + Num.sqrt (1 - r ^+ 2) * z) * (z ^+ 3 - 3 * z)).

Definition mehler_dr r f x : R :=
  \int[N]_z (f (r * x + Num.sqrt (1 - r ^+ 2) * z) *
    (x * z / Num.sqrt (1 - r ^+ 2) - r * (z ^+ 2 - 1) / (1 - r ^+ 2))).

(* The Ornstein-Uhlenbeck semigroup, by Mehler's formula. *)
Definition ou (t : R) f x : R := mehler (expR (- t)) f x.

End mehler_def.

Section mehler_basic.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (r x y : R) (f : R -> R).

Lemma mehler1 f x : mehler 1 f x = f x.
Proof.
rewrite /mehler expr1n subrr sqrtr0.
under eq_Rintegral do rewrite mul0r addr0 mul1r.
by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
Qed.

Lemma mehler0 f x : mehler 0 f x = \int[N]_z f z.
Proof.
rewrite /mehler expr0n /= subr0 sqrtr1.
by under eq_Rintegral do rewrite mul0r add0r mul1r.
Qed.

Lemma ouE (t : R) f x :
  ou t f x = \int[N]_z f (expR (- t) * x + Num.sqrt (1 - expR (- (2 * t))) * z).
Proof. by rewrite /ou /mehler -expRM_natl mulrN. Qed.

Lemma ou0 f x : ou 0 f x = f x.
Proof. by rewrite /ou oppr0 expR0 mehler1. Qed.

Lemma integrable_normal_bounded (F : R -> R) (K : R) :
  measurable_fun [set: R] F -> (forall z, `|F z| <= K) ->
  N.-integrable [set: R] (EFin \o F).
Proof.
move=> mF FK; apply: (@integrable_normal_poly _ _ K 0) => // z.
have K0 : 0 <= K := le_trans (normr_ge0 _) (FK 0).
by rewrite expr0 (le_trans (FK _))// ler_peMr// lerDl.
Qed.

Lemma normr_Rintegral_normal_le (F : R -> R) (K : R) :
  measurable_fun [set: R] F -> (forall z, `|F z| <= K) ->
  `|\int[N]_z F z| <= K.
Proof.
move=> mF FK; have K0 : 0 <= K := le_trans (normr_ge0 _) (FK 0).
have iF := integrable_normal_bounded mF FK.
have mA : measurable_fun [set: R] (fun z => `|F z|) by exact: measurableT_comp.
have iA : N.-integrable [set: R] (EFin \o (fun z => `|F z|)).
  by apply: (integrable_normal_bounded mA) => z; rewrite normr_id.
have iK : N.-integrable [set: R] (EFin \o (fun _ : R => K)).
  by apply: (@integrable_normal_bounded _ K) => // z; rewrite ger0_norm.
apply: (le_trans (le_normr_Rintegral measurableT iF)).
apply: (@le_trans _ _ (\int[N]_z K)).
  by apply: le_Rintegral => // z _; exact: FK.
by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
Qed.

Lemma Rintegral_normal_ge (F : R -> R) (a K : R) :
  measurable_fun [set: R] F -> (forall z, `|F z| <= K) -> (forall z, a <= F z)
    ->
  a <= \int[N]_z F z.
Proof.
move=> mF FK Fa; have K0 : 0 <= K := le_trans (normr_ge0 _) (FK 0).
have iF := integrable_normal_bounded mF FK.
have iC : N.-integrable [set: R] (EFin \o (fun _ : R => a)).
  by apply: (@integrable_normal_bounded _ `|a|).
apply: (@le_trans _ _ (\int[N]_z a)).
  by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
by apply: le_Rintegral => // z _; exact: Fa.
Qed.

Let maff r x : measurable_fun [set: R] (fun z => r * x + Num.sqrt (1 - r ^+ 2)
  * z).
Proof. by apply: measurable_funD => //; exact: measurable_funM. Qed.

Lemma mehler_le f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|mehler r f x| <= K.
Proof.
move=> mf fK; apply: normr_Rintegral_normal_le => //.
exact: measurableT_comp mf (maff r x).
Qed.

Lemma mehler_ge f r x (a K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> (forall y, a <= f y) -> a <= mehler r f x.
Proof.
move=> mf fK fa; apply: (@Rintegral_normal_ge _ a K) => //.
exact: measurableT_comp mf (maff r x).
Qed.

End mehler_basic.

Section derive_poly.
Context {R : realType}.

Lemma is_derive_cubic (a0 a1 a2 a3 x : R) :
  is_derive x 1 (fun x => a0 + a1 * x + a2 * x ^+ 2 + a3 * x ^+ 3)
    (a1 + 2 * a2 * x + 3 * a3 * x ^+ 2).
Proof.
have h1 := is_derive_id x (1 : R).
have h2 : is_derive x 1 (@GRing.exp R ^~ 2) (2%:R *: x ^+ 1 *: 1).
  by apply: DeriveDef; [exact: exprn_derivable|exact: exp_derive].
have h3 : is_derive x 1 (@GRing.exp R ^~ 3) (3%:R *: x ^+ 2 *: 1).
  by apply: DeriveDef; [exact: exprn_derivable|exact: exp_derive].
have h := is_deriveD (is_deriveD (is_deriveD (is_derive_cst a0 x 1)
  (is_deriveZ a1 h1)) (is_deriveZ a2 h2)) (is_deriveZ a3 h3).
have -> : (fun x => a0 + a1 * x + a2 * x ^+ 2 + a3 * x ^+ 3) =
    cst a0 + a1 \*: id + a2 \*: (@GRing.exp R ^~ 2) +
    a3 \*: (@GRing.exp R ^~ 3).
  by apply/funext => t; rewrite !fctE /GRing.scale /=.
by apply: (is_derive_eq h); rewrite /GRing.scale /= !mulr1 expr1; ring.
Qed.

End derive_poly.

Section mehler_kernel.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Local Notation mu := (@lebesgue_measure R).
Implicit Types (r x y : R).

Lemma onem_sqr_gt0 r : `|r| < 1 -> 0 < 1 - r ^+ 2.
Proof. by rewrite ltr_norml => /andP[h1 h2]; nra. Qed.

Lemma mehler_kernel_gt0 r x y : 0 < mehler_kernel r x y.
Proof. exact: expR_gt0. Qed.

Lemma expR_lnN_half (v : R) : 0 < v -> expR (- ln v / 2) = (Num.sqrt v)^-1.
Proof.
move=> v0; rewrite -powR12_sqrt ?(ltW v0)// /powR gt_eqF// -expRN.
by congr expR; rewrite mulNr mulrC.
Qed.

Lemma normal_pdf_mehler r x y : `|r| < 1 ->
  normal_pdf (r * x) (Num.sqrt (1 - r ^+ 2)) y =
  mehler_kernel r x y * normal_pdf 0 1 y.
Proof.
move=> r1; have w0 := onem_sqr_gt0 r1; set w := 1 - r ^+ 2 in w0 *.
have b0 : Num.sqrt w != 0 by rewrite gt_eqF// sqrtr_gt0.
rewrite !normal_pdfE ?oner_neq0// /normal_peak /normal_fun sqr_sqrtr ?(ltW
  w0)//.
rewrite expr1n mul1r -mulrnAr sqrtrM ?(ltW w0)// invfM.
rewrite /mehler_kernel expRD expR_lnN_half// -/w.
have e : - (y - r * x) ^+ 2 / (w *+ 2) =
    - (y - 0) ^+ 2 / 2 + (2 * r * x * y - r ^+ 2 * (x ^+ 2 + y ^+ 2)) / (2 * w).
  have w1 : 1 - r ^+ 2 != 0 := lt0r_neq0 w0.
  by rewrite /w; field.
by rewrite e expRD; ring.
Qed.

Lemma measurable_mehler_kernel r x :
  measurable_fun [set: R] (mehler_kernel r x).
Proof.
apply: measurableT_comp => //; apply: measurable_funD => //.
apply: measurable_funM => //; apply: measurable_funB => //.
by apply: measurable_funM => //; apply: measurable_funD => //; exact:
  measurable_funX.
Qed.

(* The law of r x + sqrt (1 - r^2) Z, for Z standard normal and |r| < 1,
   has the density mehler_kernel r x against the standard normal law. *)
Lemma mehler_kernel_integral r x (F : R -> R) : `|r| < 1 ->
  measurable_fun [set: R] F ->
  N.-integrable [set: R] (EFin \o (fun z => F (r * x + Num.sqrt (1 - r ^+ 2) *
    z))) ->
  \int[N]_z F (r * x + Num.sqrt (1 - r ^+ 2) * z) =
  \int[N]_y (F y * mehler_kernel r x y).
Proof.
move=> r1 mF iF; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2) in iF *.
have b0 : b != 0 by rewrite gt_eqF// sqrtr_gt0.
pose P := normal_prob (r * x) b.
pose g : measurableTypeR R -> measurableTypeR R := fun z => r * x + b * z.
have mg : measurable_fun [set: measurableTypeR R] g.
  by apply: measurable_funD => //; exact: measurable_funM.
have gE A : measurable A -> N (g @^-1` A) = P A.
  move=> mA; rewrite (_ : g = fun z => b * z + r * x).
    by apply/funext => z; rewrite /g addrC.
  by rewrite (normal_prob_affine 0 (r * x) b0 (oner_neq0 _) mA) mulr0 add0r
    mulr1.
have T0 (G : R -> \bar R) : measurable_fun [set: R] G -> (forall y, 0 <= G y)%E
  ->
    (\int[N]_z G (r * x + b * z)%R = \int[P]_y G y)%E.
  move=> mG G0.
  have := @ge0_integral_pushforward _ _ _ _ R g mg N setT G measurableT mG
    (fun y _ => G0 y).
  rewrite preimage_setT => <-.
  by apply: eq_measure_integral => A mA _; exact: gE.
have mFE : measurable_fun [set: R] (EFin \o F) by exact/measurable_EFinP.
have mFa : measurable_fun [set: R] (fun y => `|(F y)%:E|)%E.
  exact: measurableT_comp.
have iF2 : P.-integrable [set: R] (EFin \o F).
  apply/integrableP; split => //.
  rewrite -(T0 (fun y => `|(F y)%:E|)%E) //.
  by case/integrableP : iF.
have E1 : (\int[N]_z (F (r * x + b * z))%:E = \int[P]_y (F y)%:E)%E.
  exact: (integral_image mg gE iF2).
have mK := measurable_mehler_kernel r x.
have mFK : measurable_fun [set: R] (EFin \o (fun y => F y * mehler_kernel r x
  y)).
  by apply/measurable_EFinP; exact: measurable_funM.
have iFK : N.-integrable [set: R] (EFin \o (fun y => F y * mehler_kernel r x
  y)).
  apply/(integrable_normal_prob 0 1 mFK).
  have := (integrable_normal_prob (r * x) b mFE).1 iF2.
  apply: (eq_integrable measurableT) => y _.
  rewrite /comp /b.
  have := normal_pdf_mehler x y r1.
  move=> ->.
  by rewrite -!EFinM mulrA.
rewrite /Rintegral; apply: congr1.
rewrite E1 (integral_normal_prob iF2) (integral_normal_prob iFK).
apply: eq_integral => y _.
rewrite /comp /b.
have := normal_pdf_mehler x y r1.
move=> ->.
by rewrite -!EFinM mulrA.
Qed.

End mehler_kernel.

Section mehler_kernel_bounds.
Context {R : realType}.
Implicit Types (r x y : R).

Lemma mehler_kernel_le r x y r1 X : 0 <= r1 < 1 -> `|r| <= r1 -> `|x| <= X ->
  mehler_kernel r x y <=
  expR (- ln (1 - r1 ^+ 2) / 2) * expR (X / (1 - r1 ^+ 2) * `|y|).
Proof.
move=> /andP[r10 r11] rr1 xX.
have X0 : 0 <= X := le_trans (normr_ge0 _) xX.
have w1 : 0 < 1 - r1 ^+ 2 by nra.
have rr : r ^+ 2 <= r1 ^+ 2.
  by rewrite -[r ^+ 2]real_normK ?num_real// lerXn2r// ?nnegrE.
have w0 : 0 < 1 - r ^+ 2 by lra.
have ww : 1 - r1 ^+ 2 <= 1 - r ^+ 2 by lra.
rewrite /mehler_kernel -expRD ler_expR; apply: lerD.
  have : ln (1 - r1 ^+ 2) <= ln (1 - r ^+ 2) by rewrite ler_ln ?posrE.
  lra.
have h1 : 2 * r * x * y - r ^+ 2 * (x ^+ 2 + y ^+ 2) <= 2 * X * `|y|.
  have e1 : r * x * y <= `|r| * `|x| * `|y| by rewrite -!normrM ler_norm.
  have e2 : `|r| * `|x| * `|y| <= X * `|y|.
    have r1' : `|r| <= 1 by lra.
    rewrite ler_wpM2r//; apply: (le_trans _ xX); exact: ler_piMl.
  have e3 : 0 <= r ^+ 2 * (x ^+ 2 + y ^+ 2) by rewrite mulr_ge0 ?addr_ge0
    ?sqr_ge0.
  lra.
rewrite ler_pdivrMr ?mulr_gt0//; apply: (le_trans h1).
have -> : X / (1 - r1 ^+ 2) * `|y| * (2 * (1 - r ^+ 2)) =
    2 * X * `|y| * ((1 - r ^+ 2) / (1 - r1 ^+ 2)).
  by have w1' : 1 - r1 ^+ 2 != 0 := lt0r_neq0 w1; field.
rewrite ler_peMr ?mulr_ge0//.
by rewrite ler_pdivlMr// mul1r.
Qed.

Definition mehler_bound (r1 X : R) : R :=
  24 * expR (- ln (1 - r1 ^+ 2) / 2) * expR (X + 1) / (1 - r1 ^+ 2) ^+ 3.

Lemma mehler_kernel_mul_le r x y r1 X (p : R) : 0 <= r1 < 1 -> `|r| <= r1 ->
  `|x| <= X -> `|p| <= 4 * (`|y| + X + 1) ^+ 3 / (1 - r1 ^+ 2) ^+ 3 ->
  `|mehler_kernel r x y * p| <=
  mehler_bound r1 X * expR ((X / (1 - r1 ^+ 2) + 1) * `|y|).
Proof.
move=> r1I rr1 xX pb; have /andP[r10 r11] := r1I.
have X0 : 0 <= X := le_trans (normr_ge0 _) xX.
have w1 : 0 < 1 - r1 ^+ 2 by nra.
set P := `|y| + X + 1.
have P0 : 0 <= P by rewrite /P; have := normr_ge0 y; lra.
have P3 : P ^+ 3 <= 6 * (expR (X + 1) * expR `|y|).
  have := expR_ge1Dxn 2 P0; rewrite -expRD.
  have -> : X + 1 + `|y| = P by rewrite /P; ring.
  have -> : 3`!%:R = 6 :> R by rewrite /= !natrM; lra.
  have := expR_ge0 P; have := exprn_ge0 3 P0; lra.
have Kle := mehler_kernel_le y r1I rr1 xX.
set A := expR (- ln (1 - r1 ^+ 2) / 2) in Kle *.
set E0 := expR (X / (1 - r1 ^+ 2) * `|y|) in Kle *.
have A0 : 0 < A := expR_gt0 _.
have E00 : 0 < E0 := expR_gt0 _.
have K0 := mehler_kernel_gt0 r x y.
rewrite normrM (gtr0_norm K0).
apply: (le_trans (ler_pM (ltW K0) (normr_ge0 _) Kle pb)).
have -> : expR ((X / (1 - r1 ^+ 2) + 1) * `|y|) = E0 * expR `|y|.
  by rewrite /E0 -expRD mulrDl mul1r.
rewrite /mehler_bound.
have W0 : 0 < (1 - r1 ^+ 2) ^+ 3 := exprn_gt0 _ w1.
have -> : A * E0 * (4 * P ^+ 3 / (1 - r1 ^+ 2) ^+ 3) =
    (4 * A * E0 / (1 - r1 ^+ 2) ^+ 3) * P ^+ 3.
  by have w1' : 1 - r1 ^+ 2 != 0 := lt0r_neq0 w1; field.
have -> : 24 * A * expR (X + 1) / (1 - r1 ^+ 2) ^+ 3 * (E0 * expR `|y|) =
    (4 * A * E0 / (1 - r1 ^+ 2) ^+ 3) * (6 * (expR (X + 1) * expR `|y|)).
  by have w1' : 1 - r1 ^+ 2 != 0 := lt0r_neq0 w1; field.
by rewrite ler_wpM2l// divr_ge0// ?mulr_ge0// ltW.
Qed.

End mehler_kernel_bounds.

Section normal_kernel_derive.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

(* Differentiation under the integral sign against the standard normal law,
   for a parameter kernel k s y and its derivative dk s y in s, both
   dominated by C expR (c |y|) for s in an open interval. *)
Lemma is_derive_normal_kernel (f : R -> R) (K : R) (k dk : R -> R -> R)
    (u v s C c : R) :
  measurable_fun [set: R] f -> (forall y, `|f y| <= K) -> s \in `]u, v[ ->
  (forall s', measurable_fun [set: R] (k s')) ->
  (forall s' y, s' \in `]u, v[ -> is_derive s' 1 (k ^~ y) (dk s' y)) ->
  (forall s' y, s' \in `]u, v[ -> `|k s' y| <= C * expR (c * `|y|)) ->
  (forall s' y, s' \in `]u, v[ -> `|dk s' y| <= C * expR (c * `|y|)) ->
  is_derive s 1 (fun s' => \int[N]_y (f y * k s' y)) (\int[N]_y (f y * dk s y)).
Proof.
move=> mf fK sI mk dk_ kb dkb.
have K0 : 0 <= K := le_trans (normr_ge0 _) (fK 0).
have C0 : 0 <= C.
  by have := le_trans (normr_ge0 _) (kb s 0 sI); rewrite pmulr_lge0// expR_gt0.
pose D (y : R) := K * C * expR (c * `|y|).
have D0 y : 0 <= D y by rewrite /D !mulr_ge0// expR_ge0.
have Di : N.-integrable [set: R] (EFin \o D).
  have := integrableZl measurableT (K * C) (integrable_normal_expR_abs c).
  by apply: (eq_integrable measurableT) => y _; rewrite /D /= EFinM.
have fi s' : s' \in `]u, v[ ->
    N.-integrable [set: R] (EFin \o (fun y => f y * k s' y)).
  move=> s'I; apply: (le_integrable measurableT _ _ Di).
    by apply/measurable_EFinP; exact: measurable_funM mf (mk s').
  move=> y _; rewrite /comp lee_fin (ger0_norm (D0 y)) normrM /D -mulrA.
  by apply: ler_pM => //; exact: kb.
apply: (is_derive_Rintegral (df := fun s' (y : measurableTypeR R) => f y * dk
  s' y)
  sI fi _ D0 Di).
- by move=> s' y s'I; exact: (is_deriveZ (f y) (dk_ s' y s'I)).
- move=> s' y s'I; rewrite normrM /D -mulrA.
  by apply: ler_pM => //; exact: dkb.
Qed.

End normal_kernel_derive.

Section mehler_derive.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (r x y : R) (f : R -> R).

Lemma is_derive_cubicE (p : R -> R) (a0 a1 a2 a3 x d : R) :
  (forall t, p t = a0 + a1 * t + a2 * t ^+ 2 + a3 * t ^+ 3) ->
  d = a1 + 2 * a2 * x + 3 * a3 * x ^+ 2 -> is_derive x 1 p d.
Proof.
move=> pE ->.
have -> : p = (fun t => a0 + a1 * t + a2 * t ^+ 2 + a3 * t ^+ 3) by
  apply/funext.
exact: is_derive_cubic.
Qed.

(* The polynomial factors of the derivatives of the kernel. *)
Let mk1 r x y := r * (y - r * x) / (1 - r ^+ 2).
Let mk2 r x y := r ^+ 2 * ((y - r * x) ^+ 2 - (1 - r ^+ 2)) / (1 - r ^+ 2) ^+ 2.
Let mk3 r x y :=
  r ^+ 3 * ((y - r * x) ^+ 3 - 3 * (1 - r ^+ 2) * (y - r * x)) / (1 - r ^+ 2)
    ^+ 3.
Let mkr r x y := (x * (y - r * x) * (1 - r ^+ 2) - r * (y - r * x) ^+ 2 +
  r * (1 - r ^+ 2)) / (1 - r ^+ 2) ^+ 2.

Let is_derive_kx r x y : `|r| < 1 ->
  is_derive x 1 (fun x => mehler_kernel r x y)
    (mehler_kernel r x y * mk1 r x y).
Proof.
move=> r1; have w0 := onem_sqr_gt0 r1; have w1 : 1 - r ^+ 2 != 0 := lt0r_neq0
  w0.
have hq : is_derive x 1 (fun x => - ln (1 - r ^+ 2) / 2 +
    (2 * r * x * y - r ^+ 2 * (x ^+ 2 + y ^+ 2)) / (2 * (1 - r ^+ 2)))
    (mk1 r x y).
  apply: (@is_derive_cubicE _
    (- ln (1 - r ^+ 2) / 2 - r ^+ 2 * y ^+ 2 / (2 * (1 - r ^+ 2)))
    (r * y / (1 - r ^+ 2)) (- r ^+ 2 / (2 * (1 - r ^+ 2))) 0).
    by move=> t; field.
  by rewrite /mk1; field.
have h := is_derive1_comp (is_derive_expR _) hq.
by apply: (is_derive_eq h); rewrite mulrC.
Qed.

Let is_derive_kpx r x y (p : R -> R) (dp : R) : `|r| < 1 -> is_derive x 1 p dp
  ->
  is_derive x 1 (fun x => mehler_kernel r x y * p x)
    (mehler_kernel r x y * (mk1 r x y * p x + dp)).
Proof.
move=> r1 dpp; have h := is_deriveM (is_derive_kx x y r1) dpp.
by apply: (is_derive_eq h); rewrite /GRing.scale /=; ring.
Qed.

Let is_derive_k1 r x y : `|r| < 1 ->
  is_derive x 1 (fun x => mehler_kernel r x y * mk1 r x y)
    (mehler_kernel r x y * mk2 r x y).
Proof.
move=> r1; have w0 := onem_sqr_gt0 r1; have w1 : 1 - r ^+ 2 != 0 := lt0r_neq0
  w0.
have h : is_derive x 1 (fun x => mk1 r x y) (- r ^+ 2 / (1 - r ^+ 2)).
  apply: (@is_derive_cubicE _ (r * y / (1 - r ^+ 2))
    (- r ^+ 2 / (1 - r ^+ 2)) 0 0).
    by move=> t; rewrite /mk1; field.
  by field.
have h' := is_derive_kpx y r1 h.
by apply: (is_derive_eq h'); congr (_ * _); rewrite /mk1 /mk2; field.
Qed.

Let is_derive_k2 r x y : `|r| < 1 ->
  is_derive x 1 (fun x => mehler_kernel r x y * mk2 r x y)
    (mehler_kernel r x y * mk3 r x y).
Proof.
move=> r1; have w0 := onem_sqr_gt0 r1; have w1 : 1 - r ^+ 2 != 0 := lt0r_neq0
  w0.
have h : is_derive x 1 (fun x => mk2 r x y)
    (- 2 * r ^+ 3 * (y - r * x) / (1 - r ^+ 2) ^+ 2).
  apply: (@is_derive_cubicE _ (r ^+ 2 * (y ^+ 2 - (1 - r ^+ 2)) / (1 - r ^+ 2)
    ^+ 2)
    (- 2 * r ^+ 3 * y / (1 - r ^+ 2) ^+ 2) (r ^+ 4 / (1 - r ^+ 2) ^+ 2) 0).
    by move=> t; rewrite /mk2; field.
  by field.
have h' := is_derive_kpx y r1 h.
by apply: (is_derive_eq h'); congr (_ * _); rewrite /mk1 /mk2 /mk3; field.
Qed.

Let is_derive_kr r x y : `|r| < 1 ->
  is_derive r 1 (fun r => mehler_kernel r x y)
    (mehler_kernel r x y * mkr r x y).
Proof.
move=> r1; have w0 := onem_sqr_gt0 r1; have w1 : 1 - r ^+ 2 != 0 := lt0r_neq0
  w0.
have w2 : 2 * (1 - r ^+ 2) != 0 by rewrite mulf_neq0.
have hw : is_derive r 1 (fun r => 1 - r ^+ 2) (- 2 * r).
  by apply: (@is_derive_cubicE _ 1 0 (-1) 0) => [t|]; ring.
have hl := is_derive1_comp (f := @ln R) (g := fun r => 1 - r ^+ 2)
  (is_derive1_ln w0) hw.
have hn : is_derive r 1 (fun r => 2 * r * x * y - r ^+ 2 * (x ^+ 2 + y ^+ 2))
    (2 * x * y - 2 * r * (x ^+ 2 + y ^+ 2)).
  by apply: (@is_derive_cubicE _ 0 (2 * x * y) (- (x ^+ 2 + y ^+ 2)) 0) =>
    [t|]; ring.
have hd : is_derive r 1 (fun r => 2 * (1 - r ^+ 2)) (- 4 * r).
  by apply: (@is_derive_cubicE _ 2 0 (-2) 0) => [t|]; ring.
have hv := is_deriveV (f := fun r => 2 * (1 - r ^+ 2)) w2 hd.
have hl2 : is_derive r 1 (fun r => - ln (1 - r ^+ 2) / 2)
    (- 2^-1 * ((1 - r ^+ 2)^-1 * (- 2 * r))).
  have h1 : is_derive (ln (1 - r ^+ 2)) 1 (fun l : R => - l / 2) (- 2^-1).
    by apply: (@is_derive_cubicE _ 0 (- 2^-1) 0 0) => [t|]; field.
  exact: (is_derive1_comp (g := @ln R \o (fun r => 1 - r ^+ 2)) (x := r) h1 hl).
have h := is_deriveD hl2 (is_deriveM hn hv).
have hE : is_derive r 1 (fun r => - ln (1 - r ^+ 2) / 2 +
    (2 * r * x * y - r ^+ 2 * (x ^+ 2 + y ^+ 2)) / (2 * (1 - r ^+ 2)))
    (mkr r x y).
  apply: (is_derive_eq h); rewrite /mkr /GRing.scale /=; field.
have h' := is_derive1_comp (is_derive_expR _) hE.
by apply: (is_derive_eq h'); rewrite mulrC.
Qed.

(* Bounds on the polynomial factors, for |r| <= r1 < 1 and |x| <= X. *)
Let frac_le (a P w w1 : R) (j : nat) : 0 < w1 -> w1 <= w -> w <= 1 ->
  (j <= 3)%N -> `|a| <= 4 * P ^+ 3 -> `|a / w ^+ j| <= 4 * P ^+ 3 / w1 ^+ 3.
Proof.
move=> w10 w1w w1' j3 aP.
have w0 : 0 < w := lt_le_trans w10 w1w.
have P0 : 0 <= 4 * P ^+ 3 := le_trans (normr_ge0 _) aP.
rewrite normrM normfV normrX (gtr0_norm w0).
apply: (le_trans (ler_wpM2r _ aP)); first by rewrite invr_ge0 exprn_ge0// ltW.
rewrite ler_wpM2l// lef_pV2 ?posrE ?exprn_gt0//.
apply: (@le_trans _ _ (w1 ^+ j)).
  exact: (ler_wiXn2l (ltW w10) (le_trans w1w w1') j3).
by rewrite lerXn2r// ?nnegrE ltW.
Qed.

Let num_le r x y X : `|r| <= 1 -> `|x| <= X ->
  let P := `|y| + X + 1 in let z := y - r * x in let w := 1 - r ^+ 2 in
  [/\ `|r * z| <= 4 * P ^+ 3, `|r ^+ 2 * (z ^+ 2 - w)| <= 4 * P ^+ 3,
      `|r ^+ 3 * (z ^+ 3 - 3 * w * z)| <= 4 * P ^+ 3 &
      `|x * z * w - r * z ^+ 2 + r * w| <= 4 * P ^+ 3].
Proof.
move=> r1 xX P z w.
have X0 : 0 <= X := le_trans (normr_ge0 _) xX.
have P1 : 1 <= P by rewrite /P; have := normr_ge0 y; lra.
have zP : `|z| <= P.
  rewrite /z (le_trans (ler_normB _ _))// normrM.
  have : `|r| * `|x| <= X by rewrite (le_trans _ xX)// ler_piMl.
  rewrite /P; lra.
have xP : `|x| <= P by rewrite /P; have := normr_ge0 y; lra.
have w0 : 0 <= w by rewrite /w subr_ge0 -(expr1n _ 2) -real_normK ?num_real//;
  rewrite lerXn2r// ?nnegrE.
have w1 : w <= 1 by rewrite /w lerBlDr lerDl sqr_ge0.
have r2 : `|r ^+ 2| <= 1 by rewrite normrX exprn_ile1.
have r3 : `|r ^+ 3| <= 1 by rewrite normrX exprn_ile1.
have a0 := normr_ge0 z.
have P2 : P ^+ 2 <= P ^+ 3 by rewrite (ler_weXn2l P1).
have P12 : P <= P ^+ 2 by rewrite -[X in X <= _]expr1 (ler_weXn2l P1).
have P3 : 0 <= P ^+ 3 by rewrite exprn_ge0// (le_trans _ P1).
have zz : `|z| ^+ 2 <= P ^+ 2 by rewrite lerXn2r// ?nnegrE (le_trans _ P1).
have zzz : `|z| ^+ 3 <= P ^+ 3 by rewrite lerXn2r// ?nnegrE (le_trans _ P1).
have z2 : z ^+ 2 <= P ^+ 2 by rewrite -real_normK ?num_real.
have z20 : 0 <= z ^+ 2 := sqr_ge0 z.
have z3 : `|z ^+ 3| <= P ^+ 3 by rewrite normrX.
have wz : `|w * z| <= P by rewrite normrM (ger0_norm w0) (le_trans (ler_piMl _
  w1)).
have xzw : `|x * z * w| <= P ^+ 2.
  by rewrite !normrM (ger0_norm w0) (le_trans (ler_piMr _ w1)) ?mulr_ge0//
    expr2 ler_pM.
have rz2 : `|r * z ^+ 2| <= P ^+ 2.
  by rewrite normrM (ger0_norm z20) (le_trans (ler_piMl _ r1)).
have rw : `|r * w| <= P ^+ 2.
  rewrite normrM (ger0_norm w0) (le_trans (ler_piMl _ r1))//.
  by rewrite (le_trans w1)// (le_trans P1).
split.
- rewrite normrM (le_trans (ler_piMl _ r1))//; lra.
- rewrite normrM (le_trans (ler_piMl _ r2))//.
  rewrite ler_norml; apply/andP; split; lra.
- rewrite normrM (le_trans (ler_piMl _ r3))//.
  move: z3 wz; rewrite !ler_norml => /andP[h1 h2] /andP[h3 h4].
  rewrite -mulrA; apply/andP; split; lra.
- move: xzw rz2 rw; rewrite !ler_norml => /andP[h1 h2] /andP[h3 h4] /andP[h5
  h6].
  apply/andP; split; lra.
Qed.

Let kernel_bounds r x y r1 X (j : nat) (a : R) : 0 <= r1 < 1 -> `|r| <= r1 ->
  `|x| <= X -> (j <= 3)%N -> `|a| <= 4 * (`|y| + X + 1) ^+ 3 ->
  `|mehler_kernel r x y * (a / (1 - r ^+ 2) ^+ j)| <=
  mehler_bound r1 X * expR ((X / (1 - r1 ^+ 2) + 1) * `|y|).
Proof.
move=> r1I rr1 xX j3 aP; have /andP[r10 r11] := r1I.
apply: mehler_kernel_mul_le => //.
have w1 : 0 < 1 - r1 ^+ 2 by nra.
apply: frac_le => //.
- by rewrite lerD2l lerN2 -[r ^+ 2]real_normK ?num_real// lerXn2r// ?nnegrE.
- by rewrite lerBlDr lerDl sqr_ge0.
Qed.

Let integrable_fpoly f r x (h : R -> R) (K C0 : R) (k : nat) :
  measurable_fun [set: R] f -> (forall y, `|f y| <= K) ->
  measurable_fun [set: R] h -> (forall z, `|h z| <= C0 * (1 + `|z| ^+ k)) ->
  N.-integrable [set: R]
    (EFin \o (fun z => f (r * x + Num.sqrt (1 - r ^+ 2) * z) * h z)).
Proof.
move=> mf fK mh hC; have K0 : 0 <= K := le_trans (normr_ge0 _) (fK 0).
apply: (@integrable_normal_poly _ _ (K * C0) k).
  apply: measurable_funM => //; apply: measurableT_comp mf _.
  by apply: measurable_funD => //; exact: measurable_funM.
by move=> z; rewrite normrM -mulrA ler_pM.
Qed.

Let hermite_eq f r x (K : R) (q h : R -> R) (C0 : R) (k : nat) : `|r| < 1 ->
  measurable_fun [set: R] f -> (forall y, `|f y| <= K) ->
  measurable_fun [set: R] q -> measurable_fun [set: R] h ->
  (forall z, q (r * x + Num.sqrt (1 - r ^+ 2) * z) = h z) ->
  (forall z, `|h z| <= C0 * (1 + `|z| ^+ k)) ->
  \int[N]_z (f (r * x + Num.sqrt (1 - r ^+ 2) * z) * h z) =
  \int[N]_y (f y * (mehler_kernel r x y * q y)).
Proof.
move=> r1 mf fK mq mh qh hC.
have -> : \int[N]_y (f y * (mehler_kernel r x y * q y)) =
    \int[N]_y ((f y * q y) * mehler_kernel r x y).
  by apply: eq_Rintegral => y _; ring.
rewrite -(mehler_kernel_integral (F := fun y => f y * q y))//.
- exact: measurable_funM.
- have := integrable_fpoly r x mf fK mh hC.
  by apply: (eq_integrable measurableT) => z _; rewrite /= qh.
- by apply: eq_Rintegral => z _; rewrite qh.
Qed.

Let mehlerE f r x (K : R) : `|r| < 1 -> measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  mehler r f x = \int[N]_y (f y * mehler_kernel r x y).
Proof.
move=> r1 mf fK; rewrite /mehler (@mehler_kernel_integral R r x f r1 mf)//.
apply: (integrable_normal_bounded _ (fun z => fK _)).
apply: measurableT_comp mf _.
by apply: measurable_funD => //; exact: measurable_funM.
Qed.

Let measurable_mk1 r x : measurable_fun [set: R] (mk1 r x).
Proof.
by apply: measurable_funM => //; apply: measurable_funM => //; exact:
  measurable_funB.
Qed.

Let measurable_mk2 r x : measurable_fun [set: R] (mk2 r x).
Proof.
apply: measurable_funM => //; apply: measurable_funM => //.
by apply: measurable_funB => //; apply: measurable_funX; exact: measurable_funB.
Qed.

Let measurable_mk3 r x : measurable_fun [set: R] (mk3 r x).
Proof.
apply: measurable_funM => //; apply: measurable_funM => //.
apply: measurable_funB => //; first by apply: measurable_funX; exact:
  measurable_funB.
by apply: measurable_funM => //; exact: measurable_funB.
Qed.

Let measurable_mkr r x : measurable_fun [set: R] (mkr r x).
Proof.
apply: measurable_funM => //; apply: measurable_funD => //.
apply: measurable_funB => //.
  by apply: measurable_funM => //; apply: measurable_funM => //; exact:
    measurable_funB.
by apply: measurable_funM => //; apply: measurable_funX; exact: measurable_funB.
Qed.

Let normz_le1 (z : R) : `|z| <= 1 + `|z| ^+ 2.
Proof. by have := sqr_ge0 (`|z| - 1); have := normr_ge0 z; nra. Qed.

Let mehler_d1E f r x (K : R) : `|r| < 1 -> measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  mehler_d1 r f x = \int[N]_y (f y * (mehler_kernel r x y * mk1 r x y)).
Proof.
move=> r1 mf fK; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2).
have b0 : 0 < b by rewrite sqrtr_gt0.
have b0' : b != 0 := lt0r_neq0 b0.
have bE : b ^+ 2 = 1 - r ^+ 2 by rewrite sqr_sqrtr// ltW.
have mh : measurable_fun [set: R] (fun z : R => r / b * z) by exact:
  measurable_funM.
have qh z : mk1 r x (r * x + b * z) = r / b * z.
  by rewrite /mk1 -bE; field.
have hC z : `|r / b * z| <= `|r / b| * (1 + `|z| ^+ 1).
  by rewrite normrM ler_wpM2l// expr1 lerDr.
rewrite -(hermite_eq r1 mf fK (measurable_mk1 r x) mh qh hC).
rewrite /mehler_d1 -/b -RintegralZl//.
  by apply: (@integrable_fpoly f r x id K 1 1) => // z; rewrite mul1r expr1
    lerDr.
by apply: eq_Rintegral => z _; ring.
Qed.

Let mehler_d2E f r x (K : R) : `|r| < 1 -> measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  mehler_d2 r f x = \int[N]_y (f y * (mehler_kernel r x y * mk2 r x y)).
Proof.
move=> r1 mf fK; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2).
have b0 : 0 < b by rewrite sqrtr_gt0.
have b0' : b != 0 := lt0r_neq0 b0.
have bE : b ^+ 2 = 1 - r ^+ 2 by rewrite sqr_sqrtr// ltW.
pose c := r ^+ 2 / (1 - r ^+ 2).
have mh : measurable_fun [set: R] (fun z : R => c * (z ^+ 2 - 1)).
  by apply: measurable_funM => //; apply: measurable_funB => //; exact:
    measurable_funX.
have qh z : mk2 r x (r * x + b * z) = c * (z ^+ 2 - 1).
  by rewrite /mk2 /c -bE; field.
have hC z : `|c * (z ^+ 2 - 1)| <= `|c| * (1 + `|z| ^+ 2).
  rewrite normrM ler_wpM2l// real_normK ?num_real// ler_norml.
  by have z0 := sqr_ge0 z; apply/andP; split; lra.
rewrite -(hermite_eq r1 mf fK (measurable_mk2 r x) mh qh hC).
rewrite /mehler_d2 -/b -/c -RintegralZl//.
  apply: (@integrable_fpoly f r x (fun z => z ^+ 2 - 1) K 1 2) => //.
    by apply: measurable_funB => //; exact: measurable_funX.
  move=> z; rewrite mul1r real_normK ?num_real// ler_norml.
  by have z0 := sqr_ge0 z; apply/andP; split; lra.
by apply: eq_Rintegral => z _; ring.
Qed.

Let mehler_d3E f r x (K : R) : `|r| < 1 -> measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  mehler_d3 r f x = \int[N]_y (f y * (mehler_kernel r x y * mk3 r x y)).
Proof.
move=> r1 mf fK; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2).
have b0 : 0 < b by rewrite sqrtr_gt0.
have b0' : b != 0 := lt0r_neq0 b0.
have bE : b ^+ 2 = 1 - r ^+ 2 by rewrite sqr_sqrtr// ltW.
pose c := r ^+ 3 / b ^+ 3.
have mh : measurable_fun [set: R] (fun z : R => c * (z ^+ 3 - 3 * z)).
  by apply: measurable_funM => //; apply: measurable_funB.
have qh z : mk3 r x (r * x + b * z) = c * (z ^+ 3 - 3 * z).
  by rewrite /mk3 /c -bE; field.
have h3 (z : R) : `|z ^+ 3 - 3 * z| <= 4 * (1 + `|z| ^+ 3).
  have := normr_ge0 z; have h := normz_le1 z.
  have e3 : `|z ^+ 3| = `|z| ^+ 3 by rewrite normrX.
  rewrite (le_trans (ler_normB _ _))// e3 normrM ger0_norm//.
  have : `|z| <= 1 + `|z| ^+ 3.
    have := mulr_ge0 (sqr_ge0 (`|z| - 1)) (addr_ge0 (normr_ge0 z) ler01).
    have := normr_ge0 z; nra.
  lra.
have hC z : `|c * (z ^+ 3 - 3 * z)| <= (4 * `|c|) * (1 + `|z| ^+ 3).
  by rewrite normrM -mulrA mulrCA ler_wpM2l.
rewrite -(hermite_eq r1 mf fK (measurable_mk3 r x) mh qh hC).
rewrite /mehler_d3 -/b -/c -RintegralZl//.
  apply: (@integrable_fpoly f r x (fun z => z ^+ 3 - 3 * z) K 4 3) => //.
  by apply: measurable_funB => //; exact: measurable_funX.
by apply: eq_Rintegral => z _; ring.
Qed.

Let mehler_drE f r x (K : R) : `|r| < 1 -> measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  mehler_dr r f x = \int[N]_y (f y * (mehler_kernel r x y * mkr r x y)).
Proof.
move=> r1 mf fK; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2).
have b0 : 0 < b by rewrite sqrtr_gt0.
have b0' : b != 0 := lt0r_neq0 b0.
have bE : b ^+ 2 = 1 - r ^+ 2 by rewrite sqr_sqrtr// ltW.
pose h z := x * z / b - r * (z ^+ 2 - 1) / (1 - r ^+ 2).
have mh : measurable_fun [set: R] h.
  apply: measurable_funB => //.
    by apply: measurable_funM => //; exact: measurable_funM.
  apply: measurable_funM => //; apply: measurable_funM => //.
  by apply: measurable_funB => //; exact: measurable_funX.
have qh z : mkr r x (r * x + b * z) = h z.
  by rewrite /mkr /h -bE; field.
have hC z : `|h z| <= (`|x / b| + `|r / (1 - r ^+ 2)|) * (1 + `|z| ^+ 2).
  rewrite /h (le_trans (ler_normB _ _))// mulrDl.
  apply: lerD.
    rewrite mulrAC normrM ler_wpM2l// (le_trans _ (normz_le1 z))//.
  rewrite mulrAC normrM ler_wpM2l// real_normK ?num_real// ler_norml.
  by have z0 := sqr_ge0 z; apply/andP; split; lra.
exact: (hermite_eq r1 mf fK (measurable_mkr r x) mh qh hC).
Qed.

Let x_near (x x' : R) : x' \in `]x - 1, x + 1[ -> `|x'| <= `|x| + 1.
Proof.
rewrite in_itv /= => /andP[h1 h2].
have h : `|x' - x| <= 1 by rewrite ler_norml; apply/andP; split; lra.
by have := ler_normD (x' - x) x; rewrite subrK; lra.
Qed.

Let x_in (x : R) : x \in `]x - 1, x + 1[.
Proof. by rewrite in_itv /=; apply/andP; split; lra. Qed.

Theorem is_derive_mehler f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  is_derive x 1 (mehler r f) (mehler_d1 r f x).
Proof.
move=> mf fK r1; have r1I : 0 <= `|r| < 1 by rewrite normr_ge0 r1.
have -> : mehler r f = fun x' => \int[N]_y (f y * mehler_kernel r x' y).
  by apply/funext => x'; exact: mehlerE.
rewrite (mehler_d1E x r1 mf fK).
apply: (@is_derive_normal_kernel _ f K (fun x' y => mehler_kernel r x' y)
  (fun x' y => mehler_kernel r x' y * mk1 r x' y) (x - 1) (x + 1) x
  (mehler_bound `|r| (`|x| + 1)) ((`|x| + 1) / (1 - `|r| ^+ 2) + 1) mf fK (x_in
    x)).
- by move=> x'; exact: measurable_mehler_kernel.
- by move=> x' y _; exact: is_derive_kx.
- move=> x' y x'I; have xX := x_near x'I.
  have P1 : 1 <= `|y| + (`|x| + 1) + 1.
    by have := normr_ge0 y; have := normr_ge0 x; lra.
  have h1 : `|1 : R| <= 4 * (`|y| + (`|x| + 1) + 1) ^+ 3.
    by rewrite normr1; have := exprn_ege1 3 P1; lra.
  have := @kernel_bounds r x' y `|r| (`|x| + 1) 0 1 r1I (lexx _) xX isT h1.
  by rewrite expr0 divr1 mulr1.
- move=> x' y x'I; have xX := x_near x'I; have r' : `|r| <= 1 by rewrite ltW.
  have [n1 _ _ _] := num_le y r' xX.
  have := @kernel_bounds r x' y `|r| (`|x| + 1) 1 _ r1I (lexx _) xX isT n1.
  by rewrite expr1.
Qed.

Theorem is_derive_mehler_d1 f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  is_derive x 1 (mehler_d1 r f) (mehler_d2 r f x).
Proof.
move=> mf fK r1; have r1I : 0 <= `|r| < 1 by rewrite normr_ge0 r1.
have r' : `|r| <= 1 by rewrite ltW.
have -> : mehler_d1 r f = fun x' => \int[N]_y (f y * (mehler_kernel r x' y *
  mk1 r x' y)).
  by apply/funext => x'; exact: mehler_d1E.
rewrite (mehler_d2E x r1 mf fK).
apply: (@is_derive_normal_kernel _ f K (fun x' y => mehler_kernel r x' y * mk1
  r x' y)
  (fun x' y => mehler_kernel r x' y * mk2 r x' y) (x - 1) (x + 1) x
  (mehler_bound `|r| (`|x| + 1)) ((`|x| + 1) / (1 - `|r| ^+ 2) + 1) mf fK (x_in
    x)).
- by move=> x'; exact: measurable_funM (measurable_mehler_kernel r x')
  (measurable_mk1 r x').
- by move=> x' y _; exact: is_derive_k1.
- move=> x' y x'I; have xX := x_near x'I.
  have [n1 _ _ _] := num_le y r' xX.
  have := @kernel_bounds r x' y `|r| (`|x| + 1) 1 _ r1I (lexx _) xX isT n1.
  by rewrite expr1.
- move=> x' y x'I; have xX := x_near x'I.
  have [_ n2 _ _] := num_le y r' xX.
  exact: (@kernel_bounds r x' y `|r| (`|x| + 1) 2 _ r1I (lexx _) xX isT n2).
Qed.

Theorem is_derive_mehler_d2 f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  is_derive x 1 (mehler_d2 r f) (mehler_d3 r f x).
Proof.
move=> mf fK r1; have r1I : 0 <= `|r| < 1 by rewrite normr_ge0 r1.
have r' : `|r| <= 1 by rewrite ltW.
have -> : mehler_d2 r f = fun x' => \int[N]_y (f y * (mehler_kernel r x' y *
  mk2 r x' y)).
  by apply/funext => x'; exact: mehler_d2E.
rewrite (mehler_d3E x r1 mf fK).
apply: (@is_derive_normal_kernel _ f K (fun x' y => mehler_kernel r x' y * mk2
  r x' y)
  (fun x' y => mehler_kernel r x' y * mk3 r x' y) (x - 1) (x + 1) x
  (mehler_bound `|r| (`|x| + 1)) ((`|x| + 1) / (1 - `|r| ^+ 2) + 1) mf fK (x_in
    x)).
- by move=> x'; exact: measurable_funM (measurable_mehler_kernel r x')
  (measurable_mk2 r x').
- by move=> x' y _; exact: is_derive_k2.
- move=> x' y x'I; have xX := x_near x'I.
  have [_ n2 _ _] := num_le y r' xX.
  exact: (@kernel_bounds r x' y `|r| (`|x| + 1) 2 _ r1I (lexx _) xX isT n2).
- move=> x' y x'I; have xX := x_near x'I.
  have [_ _ n3 _] := num_le y r' xX.
  exact: (@kernel_bounds r x' y `|r| (`|x| + 1) 3 _ r1I (lexx _) xX isT n3).
Qed.

Theorem is_derive_mehler_r f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  is_derive r 1 (fun r => mehler r f x) (mehler_dr r f x).
Proof.
move=> mf fK r1.
pose e := (1 - `|r|) / 2; pose r2 := (1 + `|r|) / 2.
have e0 : 0 < e by rewrite /e divr_gt0// subr_gt0.
have r2I : 0 <= r2 < 1.
  by rewrite /r2; have r0 := normr_ge0 r; apply/andP; split; lra.
have rI : r \in `]r - e, r + e[ by rewrite in_itv /=; apply/andP; split; lra.
have Ib r' : r' \in `]r - e, r + e[ -> `|r'| <= r2.
  rewrite in_itv /= => /andP[h1 h2].
  have h : `|r' - r| <= e by rewrite ler_norml; apply/andP; split; lra.
  have := ler_normD (r' - r) r; rewrite subrK => hn.
  by move: h; rewrite /r2 /e; lra.
have I1 r' : r' \in `]r - e, r + e[ -> `|r'| < 1.
  by move=> /Ib h; rewrite (le_lt_trans h)//; case/andP: r2I.
have xX : `|x| <= `|x| := lexx _.
have P1 y : 1 <= `|y| + `|x| + 1 by have := normr_ge0 y; have := normr_ge0 x;
  lra.
have H : is_derive r 1 (fun r' => \int[N]_y (f y * mehler_kernel r' x y))
    (\int[N]_y (f y * (mehler_kernel r x y * mkr r x y))).
  apply: (@is_derive_normal_kernel _ f K (fun r' y => mehler_kernel r' x y)
    (fun r' y => mehler_kernel r' x y * mkr r' x y) (r - e) (r + e) r
    (mehler_bound r2 `|x|) (`|x| / (1 - r2 ^+ 2) + 1) mf fK rI).
  - by move=> r'; exact: measurable_mehler_kernel.
  - by move=> r' y r'I; exact: is_derive_kr (I1 _ r'I).
  - move=> r' y r'I.
    have h1 : `|1 : R| <= 4 * (`|y| + `|x| + 1) ^+ 3.
      by rewrite normr1; have := exprn_ege1 3 (P1 y); lra.
    have := @kernel_bounds r' x y r2 `|x| 0 1 r2I (Ib _ r'I) xX isT h1.
    by rewrite expr0 divr1 mulr1.
  - move=> r' y r'I; have r'1 : `|r'| <= 1 by rewrite ltW// I1.
    have [_ _ _ nr] := num_le y r'1 xX.
    exact: (@kernel_bounds r' x y r2 `|x| 2 _ r2I (Ib _ r'I) xX isT nr).
rewrite (mehler_drE x r1 mf fK).
apply: (near_eq_is_derive _ H).
apply: filterS (near_in_itvoo rI) => r' r'I.
by rewrite (mehlerE x (I1 _ r'I) mf fK).
Qed.

(* The generator identity, in the variable r = expR (- t). *)
Theorem mehler_generator f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  r * mehler_dr r f x = x * mehler_d1 r f x - mehler_d2 r f x.
Proof.
move=> mf fK r1; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2).
have b0 : 0 < b by rewrite sqrtr_gt0.
have b0' : b != 0 := lt0r_neq0 b0.
have w0' : 1 - r ^+ 2 != 0 := lt0r_neq0 w0.
have i1 : N.-integrable [set: R] (EFin \o (fun z => f (r * x + b * z) * z)).
  by apply: (@integrable_fpoly f r x id K 1 1) => // z; rewrite mul1r expr1
    lerDr.
have i2 : N.-integrable [set: R] (EFin \o (fun z => f (r * x + b * z) * (z ^+ 2
  - 1))).
  apply: (@integrable_fpoly f r x (fun z => z ^+ 2 - 1) K 1 2) => //.
    by apply: measurable_funB => //; exact: measurable_funX.
  move=> z; rewrite mul1r real_normK ?num_real// ler_norml.
  by have z0 := sqr_ge0 z; apply/andP; split; lra.
have i1' : N.-integrable [set: R]
    (EFin \o (fun z => x / b * (f (r * x + b * z) * z))).
  have := integrableZl measurableT (x / b) i1.
  by apply: (eq_integrable measurableT) => z _; rewrite /= EFinM.
have i2' : N.-integrable [set: R]
    (EFin \o (fun z => r / (1 - r ^+ 2) * (f (r * x + b * z) * (z ^+ 2 - 1)))).
  have := integrableZl measurableT (r / (1 - r ^+ 2)) i2.
  by apply: (eq_integrable measurableT) => z _; rewrite /= EFinM.
have E : \int[N]_z (f (r * x + b * z) *
      (x * z / b - r * (z ^+ 2 - 1) / (1 - r ^+ 2))) =
    \int[N]_z (x / b * (f (r * x + b * z) * z)) -
    \int[N]_z (r / (1 - r ^+ 2) * (f (r * x + b * z) * (z ^+ 2 - 1))).
  rewrite -(RintegralB measurableT i1' i2').
  by apply: eq_Rintegral => z _; field.
rewrite /mehler_dr /mehler_d1 /mehler_d2 -/b E.
rewrite (RintegralZl (x / b) measurableT i1) (RintegralZl (r / (1 - r ^+ 2))
  measurableT i2).
by field.
Qed.

End mehler_derive.

Section mehler_properties.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (r x y : R) (f : R -> R).

Let maff r x : measurable_fun [set: R] (fun z => r * x + Num.sqrt (1 - r ^+ 2)
  * z).
Proof. by apply: measurable_funD => //; exact: measurable_funM. Qed.

Lemma continuous_mehler f r (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 -> continuous (mehler r f).
Proof.
move=> mf fK r1 x; apply: differentiable_continuous; apply/derivable1_diffP.
exact: (@ex_derive _ _ _ _ _ _ _ (is_derive_mehler x mf fK r1)).
Qed.

Lemma continuous_mehler_d1 f r (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 -> continuous (mehler_d1 r f).
Proof.
move=> mf fK r1 x; apply: differentiable_continuous; apply/derivable1_diffP.
exact: (@ex_derive _ _ _ _ _ _ _ (is_derive_mehler_d1 x mf fK r1)).
Qed.

Lemma continuous_mehler_d2 f r (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 -> continuous (mehler_d2 r f).
Proof.
move=> mf fK r1 x; apply: differentiable_continuous; apply/derivable1_diffP.
exact: (@ex_derive _ _ _ _ _ _ _ (is_derive_mehler_d2 x mf fK r1)).
Qed.

Lemma measurable_mehler f r (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 -> measurable_fun [set: R] (mehler r f).
Proof. by move=> mf fK r1; apply: continuous_measurable_fun; exact:
  continuous_mehler mf fK r1. Qed.

Lemma normr_Rintegral_normal_mul_le (F h : R -> R) (K : R) :
  measurable_fun [set: R] F -> (forall z, `|F z| <= K) ->
  measurable_fun [set: R] h -> N.-integrable [set: R] (EFin \o h) ->
  `|\int[N]_z (F z * h z)| <= K * \int[N]_z `|h z|.
Proof.
move=> mF FK mh ih; have K0 : 0 <= K := le_trans (normr_ge0 _) (FK 0).
have ia : N.-integrable [set: R] (EFin \o (fun z => `|h z|)).
  have := integrable_abse ih.
  by apply: (eq_integrable measurableT) => z _; rewrite /comp abse_EFin.
have iK : N.-integrable [set: R] (EFin \o (fun z => K * `|h z|)).
  have := integrableZl measurableT K ia.
  by apply: (eq_integrable measurableT) => z _; rewrite /= EFinM.
have iFh : N.-integrable [set: R] (EFin \o (fun z => F z * h z)).
  apply: (le_integrable measurableT _ _ iK).
    by apply/measurable_EFinP; exact: measurable_funM.
  move=> z _; rewrite /comp !abse_EFin lee_fin [X in _ <= X]ger0_norm
    ?mulr_ge0//.
  by rewrite normrM ler_wpM2r//; exact: FK.
apply: (le_trans (le_normr_Rintegral measurableT iFh)).
rewrite -(RintegralZl K measurableT ia).
apply: le_Rintegral => //.
- apply: (le_integrable measurableT _ _ iK).
    by apply/measurable_EFinP; apply: measurableT_comp => //; exact:
      measurable_funM.
  move=> z _; rewrite /comp !abse_EFin lee_fin [X in _ <= X]ger0_norm
    ?mulr_ge0//.
  by rewrite normr_id normrM ler_wpM2r//; exact: FK.
- by move=> z _; rewrite normrM ler_wpM2r//; exact: FK.
Qed.

Lemma mehler_d1_le f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  `|mehler_d1 r f x| <= `|r| / Num.sqrt (1 - r ^+ 2) * (K * \int[N]_z `|z|).
Proof.
move=> mf fK r1; have w0 := onem_sqr_gt0 r1.
have b0 : 0 < Num.sqrt (1 - r ^+ 2) by rewrite sqrtr_gt0.
rewrite /mehler_d1 normrM normf_div (gtr0_norm b0) ler_wpM2l ?divr_ge0 ?(ltW
  b0)//.
apply: normr_Rintegral_normal_mul_le => //.
- exact: measurableT_comp mf (maff r x).
- apply: (@integrable_normal_poly _ _ 1 1) => // z.
  by rewrite mul1r expr1 lerDr.
Qed.

Lemma mehler_d2_le f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  `|mehler_d2 r f x| <= r ^+ 2 / (1 - r ^+ 2) * (K * \int[N]_z `|z ^+ 2 - 1|).
Proof.
move=> mf fK r1; have w0 := onem_sqr_gt0 r1.
rewrite /mehler_d2 normrM ger0_norm ?divr_ge0 ?sqr_ge0 ?(ltW w0)//.
rewrite ler_wpM2l ?divr_ge0 ?sqr_ge0 ?(ltW w0)//.
apply: normr_Rintegral_normal_mul_le => //.
- exact: measurableT_comp mf (maff r x).
- by apply: measurable_funB => //; exact: measurable_funX.
- apply: (@integrable_normal_poly _ _ 1 2).
    by apply: measurable_funB => //; exact: measurable_funX.
  move=> z; rewrite mul1r real_normK ?num_real// ler_norml.
  by have z0 := sqr_ge0 z; apply/andP; split; lra.
Qed.

End mehler_properties.

Section mehler_semigroup.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (r x y : R) (f : R -> R).

Let maff r x : measurable_fun [set: R] (fun z => r * x + Num.sqrt (1 - r ^+ 2)
  * z).
Proof. by apply: measurable_funD => //; exact: measurable_funM. Qed.

Let integrable_maff f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  N.-integrable [set: R] (EFin \o (fun z => f (r * x + Num.sqrt (1 - r ^+ 2) *
    z))).
Proof.
by move=> mf fK; apply: (integrable_normal_bounded _ (fun z => fK _));
  exact: measurableT_comp mf (maff r x).
Qed.

(* The standard normal law is invariant: integrating mehler r f against it
   is integrating f. *)
Theorem integral_mehler f r (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  \int[N]_x mehler r f x = \int[N]_y f y.
Proof.
move=> mf fK r1; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2).
have b0 : b != 0 by rewrite gt_eqF// sqrtr_gt0.
have bE : b ^+ 2 = 1 - r ^+ 2 by rewrite sqr_sqrtr// ltW.
pose g : measurableTypeR R * measurableTypeR R -> measurableTypeR R :=
  fun p => r * p.1 + b * p.2.
have mg : measurable_fun [set: measurableTypeR R * measurableTypeR R] g.
  apply: measurable_funD => //.
    by apply: measurable_funM => //; exact: measurable_fst.
  by apply: measurable_funM => //; exact: measurable_snd.
have gE A : measurable A -> (N \x N)%E (g @^-1` A) = N A.
  move=> mA; have := normal_prob_lincomb 0 0 r (oner_neq0 R) (oner_neq0 R) b0
    mA.
  rewrite !mulr0 addr0 !expr1n !mulr1 bE addrC subrK sqrtr1 => <-.
  by [].
have iF : N.-integrable [set: R] (EFin \o f) := integrable_normal_bounded mf fK.
have ifg := integrable_image mg gE iF.
rewrite /Rintegral; apply: congr1.
rewrite -(integral_image mg gE iF) -(integral12_prod_meas1 ifg).
apply: eq_integral => x _; rewrite /mehler -/b fineK//.
exact: (integrable_fin_num measurableT (integrable_maff r x mf fK)).
Qed.

Theorem mehler_contraction f (h : R -> R) r (K : R) :
  measurable_fun [set: R] f -> measurable_fun [set: R] h ->
  (forall y, `|f y| <= K) -> (forall y, `|h y| <= K) -> `|r| < 1 ->
  \int[N]_x `|mehler r f x - mehler r h x| <= \int[N]_y `|f y - h y|.
Proof.
move=> mf mh fK hK r1; have K0 : 0 <= K := le_trans (normr_ge0 _) (fK 0).
have mfh : measurable_fun [set: R] (fun y => f y - h y) by exact:
  measurable_funB.
have fhK y : `|f y - h y| <= K + K by rewrite (le_trans (ler_normB _ _))// lerD.
have mafh : measurable_fun [set: R] (fun y => `|f y - h y|) by exact:
  measurableT_comp.
have afhK y : `|(`|f y - h y|)| <= K + K by rewrite normr_id.
have E x : mehler r f x - mehler r h x = mehler r (fun y => f y - h y) x.
  by rewrite /mehler -RintegralB//; [exact: integrable_maff mf fK|
    exact: integrable_maff mh hK].
have le x : `|mehler r f x - mehler r h x| <= mehler r (fun y => `|f y - h y|)
  x.
  rewrite E; apply: le_normr_Rintegral => //.
  exact: integrable_maff mfh fhK.
rewrite -(integral_mehler mafh afhK r1).
have mM := measurable_mehler mf fK r1; have mM' := measurable_mehler mh hK r1.
apply: le_Rintegral => //.
- apply: (integrable_normal_bounded (K := (K + K))).
    by apply: measurableT_comp => //; exact: measurable_funB.
  by move=> x; rewrite normr_id (le_trans (ler_normB _ _))// lerD// mehler_le.
- apply: (integrable_normal_bounded (K := (K + K))).
    exact: measurable_mehler mafh afhK r1.
  by move=> x; rewrite mehler_le.
Qed.

End mehler_semigroup.

Section normal_continuous_dense.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Local Notation mu := (@lebesgue_measure R).

Let clip (lo hi a : R) := Num.min hi (Num.max lo a).

Let clip_le (lo hi a b : R) : lo <= hi -> lo <= b <= hi ->
  `|b - clip lo hi a| <= `|b - a|.
Proof.
move=> lohi /andP[h1 h2]; rewrite /clip.
have [alo|loa] := leP a lo.
  have ab : a <= b := le_trans alo h1.
  by rewrite (min_r lohi) !ger0_norm ?subr_ge0//; lra.
have [ahi|hia] := leP a hi; first by [].
have ba : b <= a := le_trans h2 (ltW hia).
by rewrite !ler0_norm ?subr_le0//; lra.
Qed.

Let clip_in (lo hi a : R) : lo <= hi -> lo <= clip lo hi a <= hi.
Proof.
move=> lohi; rewrite /clip; apply/andP; split.
  by rewrite le_min lohi le_max lexx.
by rewrite ge_min lexx.
Qed.

Let normal_pdf01_le1 (y : R) : normal_pdf 0 1 y <= 1.
Proof.
apply: (le_trans (normal_pdf_ub _ _ (oner_neq0 R))).
have p2 : 1 <= trigo.pi *+ 2 :> R by have := @trigo.pi_ge2 R; rewrite mulr2n;
  lra.
have s1 : 1 <= Num.sqrt (trigo.pi *+ 2 : R).
  by rewrite -sqrtr1 ler_sqrt ?(le_trans ler01 p2).
have s0 : 0 < Num.sqrt (trigo.pi *+ 2 : R) := lt_le_trans ltr01 s1.
by rewrite /normal_peak expr1n mul1r invr_le1// unitfE gt_eqF.
Qed.

(* Bounded continuous functions are dense in L^1 of the standard normal law,
   within the same bounds. *)
Theorem normal_continuous_approx (f : R -> R) (lo hi eps : R) :
  measurable_fun [set: R] f -> (forall y, lo <= f y <= hi) -> 0 < eps ->
  exists h : R -> R, [/\ continuous h, (forall y, lo <= h y <= hi) &
    \int[N]_y `|f y - h y| < eps].
Proof.
move=> mf fb e0.
have lohi : lo <= hi by have /andP[h1 h2] := fb 0; exact: le_trans h1 h2.
pose D := hi - lo; have D0 : 0 <= D by rewrite /D subr_ge0.
pose M := 1 + 8 * (D + 1) / eps.
have M1 : 1 <= M by rewrite /M lerDl divr_ge0// ?mulr_ge0// ?ltW//; lra.
pose E := `[- M, M]%classic.
have mE : measurable E := measurable_itv _.
have muE : (mu E < +oo)%E.
  by rewrite /E lebesgue_measure_itv/=; case: ifP => _; rewrite ?ltry ?lt0y.
have fE : mu.-integrable E (EFin \o f).
  apply: measurable_bounded_integrable => //; first exact: measurable_funTS.
  exists (`|lo| + `|hi|); split; first by rewrite num_real.
  move=> c cb y _ /=.
  rewrite (le_trans _ (ltW cb))// ler_norml.
  have /andP[h1 h2] := fb y.
  have l1 := ler_norm lo; have l2 := ler_norm hi; have l3 := ler_norm (- lo).
  have l4 := ler_norm (- hi); rewrite !normrN in l3 l4; apply/andP; split; lra.
have [g [cg ig gcvg]] := approximation_continuous_integrable mE muE fE.
have [n gn] : exists n,
    (\int[mu]_(z in E) `|(f z - g n z)%:E| < (eps / 2)%:E)%E.
  move/fine_cvgP : gcvg => [gfin /cvgrPdist_lt/(_ (eps / 2))].
  rewrite divr_gt0// => /(_ isT) gc.
  have [n [/= gnfin gnlt]] := (filter_ex (filterI gfin gc)).
  exists n; rewrite -(fineK gnfin) lte_fin.
  by move: gnlt; rewrite sub0r normrN; apply: le_lt_trans; exact: ler_norm.
pose h y := clip lo hi (g n y).
have ch : continuous h.
  move=> y; rewrite /h /clip.
  apply: (@continuous_min R R (cst hi) (fun y => Num.max lo (g n y))).
    exact: cvg_cst.
  apply: (@continuous_max R R (cst lo) (g n)); first exact: cvg_cst.
  exact: cg.
have hb y : lo <= h y <= hi := clip_in (g n y) lohi.
exists h; split => //.
have mh : measurable_fun [set: R] h := continuous_measurable_fun ch.
have mF : measurable_fun [set: R] (fun y => `|f y - h y|).
  by apply: measurableT_comp => //; exact: measurable_funB.
have mg : measurable_fun [set: R] (g n) := continuous_measurable_fun (cg n).
have FD y : `|f y - h y| <= D.
  have /andP[h1 h2] := fb y; have /andP[h3 h4] := hb y.
  by rewrite ler_norml /D; apply/andP; split; lra.
have Fle y : `|f y - h y| <= `|f y - g n y| * \1_E y + D * \1_(~` E) y.
  rewrite !indicE in_setC; case: (boolP (y \in E)) => yE /=.
    by rewrite mulr1 mulr0 addr0 clip_le.
  by rewrite mulr0 mulr1 add0r.
have iF : N.-integrable [set: R] (EFin \o (fun y => `|f y - h y|)).
  by apply: (integrable_normal_bounded mF) => y; rewrite normr_id.
have mI1 : measurable_fun [set: R] (fun y => (`|f y - g n y| * \1_E y)%:E).
  apply/measurable_EFinP; apply: measurable_funM.
    by apply: measurableT_comp => //; exact: measurable_funB.
  exact: measurable_indic.
have mI2 : measurable_fun [set: R] (fun y => (D * \1_(~` E) y)%:E).
  apply/measurable_EFinP; apply: measurable_funM => //.
  by apply: measurable_indic; exact: measurableC.
have I1 : (\int[N]_y (`|f y - g n y| * \1_E y)%:E < (eps / 2)%:E)%E.
  rewrite ge0_integral_normal_prob//.
  have gn' : (\int[mu]_(z in E) `|(f z - g n z)%:E| < (eps / 2)%:E)%E.
    exact: gn.
  apply: le_lt_trans gn'; rewrite [X in (_ <= X)%E]integral_mkcond.
  apply: (@ge0_le_integral _ _ R mu setT measurableT).
  - by move=> y _; rewrite mule_ge0// lee_fin ?mulr_ge0// normal_pdf_ge0.
  - apply: emeasurable_funM => //; apply/measurable_EFinP.
    exact: measurable_normal_pdf.
  - apply/(measurable_restrictT _ _).1 => //; apply: measurable_funTS.
    by apply: measurableT_comp => //; apply/measurable_EFinP; exact:
      measurable_funB.
  - move=> y _; rewrite /patch indicE; case: ifP => yE /=.
      by rewrite mulr1 -EFinM lee_fin ler_piMr// normal_pdf01_le1.
    by rewrite mulr0 mul0e.
have NE : (N (~` E) <= (2 * expR (- M ^+ 2 / 2))%:E)%E.
  have M0' : 0 <= M := le_trans ler01 M1.
  have := normal_prob_abs_tail 0 (oner_neq0 R) M0'.
  rewrite expr1n mulr1; apply: le_trans.
    apply: le_measure; rewrite ?inE.
    - exact: measurableC.
    - rewrite (_ : [set x | M <= `|x - 0|] = [set x | M <= `|x|]).
        by apply/seteqP; split => x /=; rewrite subr0.
      rewrite (_ : [set x | M <= `|x|] = [set x | M <= x] `|` [set x | x <= -
        M]).
        apply/seteqP; split => x /=.
          by rewrite ler_normr => /orP[hh|hh]; [left|right; lra].
        by move=> [hh|hh]; rewrite ler_normr; apply/orP; [left|right; lra].
      by apply: measurableU; [rewrite -set_itvcy|rewrite -set_itvNyc];
        exact: measurable_itv.
    - move=> x; rewrite /E /= => /negP; rewrite in_itv /= negb_and -!ltNge
      subr0.
      by move=> /orP[hh|hh]; rewrite ler_normr; apply/orP; [right; lra|left;
        lra].
have I2 : (\int[N]_y (D * \1_(~` E) y)%:E <= (eps / 2)%:E)%E.
  under eq_integral do rewrite EFinM.
  have mCE : measurable (~` E) by exact: measurableC.
  rewrite ge0_integralZl_EFin//.
    by apply/measurable_EFinP; exact: measurable_indic.
  have IE0 : (\int[N]_y (\1_(~` E) y)%:E = N (~` E))%E.
    by rewrite -[X in _ = N X]setIT -integral_indic.
  rewrite -[X in (_ * X <= _)%E]/(\int[N]_y (\1_(~` E) y)%:E)%E IE0.
  apply: (le_trans (lee_wpmul2l _ NE)); first by rewrite lee_fin.
  rewrite -EFinM lee_fin.
  have eM : expR (- M ^+ 2 / 2) <= 2 / M ^+ 2.
    have hpos : 0 < M ^+ 2 / 2 by rewrite divr_gt0// exprn_gt0// (lt_le_trans
      ltr01 M1).
    rewrite mulNr expRN.
    have -> : 2 / M ^+ 2 = (M ^+ 2 / 2)^-1 by rewrite invf_div.
    rewrite lef_pV2 ?posrE ?expR_gt0//.
    by have := expR_ge1Dx (M ^+ 2 / 2); lra.
  have MM : M <= M ^+ 2 by rewrite expr2 ler_peMl// (le_trans ler01 M1).
  have M0 : 0 < M := lt_le_trans ltr01 M1.
  have h8 : 8 * (D + 1) <= eps * M.
    have e0' : eps != 0 := lt0r_neq0 e0.
    have -> : eps * M = eps + 8 * (D + 1) by rewrite /M; field.
    by rewrite lerDr ltW.
  have M2 : 0 < M ^+ 2 := exprn_gt0 2 M0.
  have M2' : M ^+ 2 != 0 := lt0r_neq0 M2.
  have M0' : M != 0 := lt0r_neq0 M0.
  apply: (@le_trans _ _ (4 * (D + 1) / M ^+ 2)).
    apply: (@le_trans _ _ (D * (2 * (2 / M ^+ 2)))).
      by rewrite ler_wpM2l// ler_wpM2l.
    have -> : D * (2 * (2 / M ^+ 2)) = 4 * D / M ^+ 2 by field.
    by rewrite ler_wpM2r ?invr_ge0 ?ltW//; lra.
  rewrite ler_pdivrMr//.
  have : eps * M <= eps * M ^+ 2 by rewrite ler_wpM2l// ltW.
  lra.
have intFle : (\int[N]_y (`|f y - h y|)%:E <=
    \int[N]_y ((`|f y - g n y| * \1_E y)%:E + (D * \1_(~` E) y)%:E))%E.
  apply: (@ge0_le_integral _ _ R N setT measurableT).
  - by move=> y _; rewrite lee_fin.
  - exact/measurable_EFinP.
  - exact: emeasurable_funD.
  - by move=> y _; rewrite -EFinD lee_fin.
rewrite /Rintegral -lte_fin fineK ?(integrable_fin_num measurableT iF)//.
apply: (le_lt_trans intFle).
rewrite ge0_integralD//.
  by move=> y _; rewrite lee_fin mulr_ge0.
have I2fin : (\int[N]_y (D * \1_(~` E) y)%:E)%E \is a fin_num.
  rewrite ge0_fin_numE.
    by apply: integral_ge0 => y _; rewrite lee_fin mulr_ge0.
  exact: le_lt_trans I2 (ltry _).
by rewrite [eps]splitr EFinD; exact: (lte_leD I2fin I1 I2).
Qed.

End normal_continuous_dense.

Section ou_semigroup.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (r x y t : R) (f : R -> R).

Lemma mehler_dr_split f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  mehler_dr r f x =
  x / Num.sqrt (1 - r ^+ 2) *
    \int[N]_z (f (r * x + Num.sqrt (1 - r ^+ 2) * z) * z) -
  r / (1 - r ^+ 2) *
    \int[N]_z (f (r * x + Num.sqrt (1 - r ^+ 2) * z) * (z ^+ 2 - 1)).
Proof.
move=> mf fK r1; have w0 := onem_sqr_gt0 r1.
set b := Num.sqrt (1 - r ^+ 2).
have b0 : b != 0 by rewrite gt_eqF// sqrtr_gt0.
have maff : measurable_fun [set: R] (fun z => f (r * x + b * z)).
  by apply: measurableT_comp mf _; apply: measurable_funD => //; exact:
    measurable_funM.
have i1 : N.-integrable [set: R] (EFin \o (fun z => f (r * x + b * z) * z)).
  apply: (@integrable_normal_poly _ _ K 1).
    by apply: measurable_funM => //.
  by move=> z; rewrite normrM expr1 ler_pM// lerDr.
have i2 : N.-integrable [set: R] (EFin \o (fun z => f (r * x + b * z) * (z ^+ 2
  - 1))).
  apply: (@integrable_normal_poly _ _ K 2).
    by apply: measurable_funM => //; apply: measurable_funB => //; exact:
      measurable_funX.
  move=> z; rewrite normrM ler_pM// real_normK ?num_real// ler_norml.
  by have z0 := sqr_ge0 z; apply/andP; split; lra.
have i1' : N.-integrable [set: R]
    (EFin \o (fun z => x / b * (f (r * x + b * z) * z))).
  have := integrableZl measurableT (x / b) i1.
  by apply: (eq_integrable measurableT) => z _; rewrite /= EFinM.
have i2' : N.-integrable [set: R]
    (EFin \o (fun z => r / (1 - r ^+ 2) * (f (r * x + b * z) * (z ^+ 2 - 1)))).
  have := integrableZl measurableT (r / (1 - r ^+ 2)) i2.
  by apply: (eq_integrable measurableT) => z _; rewrite /= EFinM.
rewrite -(RintegralZl _ measurableT i1) -(RintegralZl _ measurableT i2).
rewrite -(RintegralB measurableT i1' i2').
rewrite /mehler_dr -/b; apply: eq_Rintegral => z _.
have w0' : 1 - r ^+ 2 != 0 := lt0r_neq0 w0.
by field.
Qed.

Lemma mehler_dr_le f r x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> `|r| < 1 ->
  `|mehler_dr r f x| <= `|x| / Num.sqrt (1 - r ^+ 2) * (K * \int[N]_z `|z|) +
    `|r| / (1 - r ^+ 2) * (K * \int[N]_z `|z ^+ 2 - 1|).
Proof.
move=> mf fK r1; have w0 := onem_sqr_gt0 r1.
have b0 : 0 < Num.sqrt (1 - r ^+ 2) by rewrite sqrtr_gt0.
have maff : measurable_fun [set: R] (fun z => f (r * x + Num.sqrt (1 - r ^+ 2)
  * z)).
  by apply: measurableT_comp mf _; apply: measurable_funD => //; exact:
    measurable_funM.
rewrite (mehler_dr_split x mf fK r1) (le_trans (ler_normB _ _))//.
apply: lerD; rewrite normrM.
  rewrite normf_div (gtr0_norm b0) ler_wpM2l ?divr_ge0 ?(ltW b0)//.
  apply: normr_Rintegral_normal_mul_le => //.
  by apply: (@integrable_normal_poly _ _ 1 1) => // z; rewrite mul1r expr1
    lerDr.
rewrite normf_div (gtr0_norm w0) ler_wpM2l ?divr_ge0 ?(ltW w0)//.
apply: normr_Rintegral_normal_mul_le => //.
- by apply: measurable_funB => //; exact: measurable_funX.
- apply: (@integrable_normal_poly _ _ 1 2).
    by apply: measurable_funB => //; exact: measurable_funX.
  move=> z; rewrite mul1r real_normK ?num_real// ler_norml.
  by have z0 := sqr_ge0 z; apply/andP; split; lra.
Qed.

Lemma expRN_lt1 t : 0 < t -> `|expR (- t)| < 1.
Proof. by move=> t0; rewrite gtr0_norm ?expR_gt0// expR_lt1 oppr_lt0. Qed.

Theorem is_derive_ou f t x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> 0 < t ->
  is_derive x 1 (ou t f) (mehler_d1 (expR (- t)) f x).
Proof. by move=> mf fK t0; exact: is_derive_mehler mf fK (expRN_lt1 t0). Qed.

Theorem is_derive_ou_d1 f t x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> 0 < t ->
  is_derive x 1 (mehler_d1 (expR (- t)) f) (mehler_d2 (expR (- t)) f x).
Proof. by move=> mf fK t0; exact: is_derive_mehler_d1 mf fK (expRN_lt1 t0). Qed.

(* The generator identity: d/dt ou t f = (ou t f)'' - x (ou t f)'. *)
Theorem is_derive_ou_t f t x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> 0 < t ->
  is_derive t 1 (fun t => ou t f x)
    (mehler_d2 (expR (- t)) f x - x * mehler_d1 (expR (- t)) f x).
Proof.
move=> mf fK t0; have r1 := expRN_lt1 t0.
have hr := is_derive_mehler_r x mf fK r1.
have he : is_derive t 1 (fun t => expR (- t)) (expR (- t) * - 1).
  exact: (is_derive1_comp (f := expR) (g := -%R) (is_derive_expR _)
    (is_deriveNid t 1)).
have h := is_derive1_comp (g := fun t => expR (- t)) (x := t) hr he.
apply: (is_derive_eq h).
have g := mehler_generator x mf fK r1.
by rewrite mulrN1 mulrN mulrC g opprB.
Qed.

Theorem ou_cvgy f x (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> ou t f x @[t --> +oo] --> \int[N]_y f y.
Proof.
move=> mf fK; rewrite -(mehler0 f x).
have r0 : `|0 : R| < 1 by rewrite normr0 ltr01.
have c0 : {for 0, continuous (fun r => mehler r f x)}.
  apply: differentiable_continuous; apply/derivable1_diffP.
  exact: (@ex_derive _ _ _ _ _ _ _ (is_derive_mehler_r x mf fK r0)).
have := @cvg_comp _ _ _ _ _ _ _ _ (@cvgr_expR R) c0.
by apply: cvg_trans; apply: near_eq_cvg; apply: nearW => t.
Qed.

End ou_semigroup.

Section mehler_limits.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Implicit Types (r x y t : R) (f h : R -> R).

Let integrable_cst (K : R) : N.-integrable [set: R] (EFin \o (fun=> K)).
Proof. by apply: (integrable_normal_bounded (K := `|K|)). Qed.

(* For h continuous and bounded, mehler r h x is continuous in x and in r,
   for every r. *)
Lemma continuous_mehler_x h r (K : R) : continuous h -> (forall y, `|h y| <= K)
  ->
  continuous (mehler r h).
Proof.
move=> ch hK x0; have mh := continuous_measurable_fun ch.
apply: (@continuity_under_integral_at _ _ _ _ N
  (fun x z => h (r * x + Num.sqrt (1 - r ^+ 2) * z)) setT x0 setT (fun=> K)) =>
    //.
- exact: filterT.
- move=> x _; apply: (integrable_normal_bounded _ (fun z => hK _)).
  by apply: measurableT_comp mh _; apply: measurable_funD => //; exact:
    measurable_funM.
- move=> z _; apply: continuous_comp; last exact: ch.
  apply: cvgD; last exact: cvg_cst.
  by apply: cvgM; [exact: cvg_cst|exact: cvg_id].
Qed.

Lemma continuous_mehler_r h x (K : R) : continuous h -> (forall y, `|h y| <= K)
  ->
  continuous (fun r => mehler r h x).
Proof.
move=> ch hK r0; have mh := continuous_measurable_fun ch.
apply: (@continuity_under_integral_at _ _ _ _ N
  (fun r z => h (r * x + Num.sqrt (1 - r ^+ 2) * z)) setT r0 setT (fun=> K)) =>
    //.
- exact: filterT.
- move=> r _; apply: (integrable_normal_bounded _ (fun z => hK _)).
  by apply: measurableT_comp mh _; apply: measurable_funD => //; exact:
    measurable_funM.
- move=> z _; apply: continuous_comp; last exact: ch.
  apply: cvgD; first by apply: cvgM; [exact: cvg_id|exact: cvg_cst].
  apply: cvgM; last exact: cvg_cst.
  apply: continuous_comp; last exact: sqrt_continuous.
  by apply: cvgB; [exact: cvg_cst|exact: exprn_continuous].
Qed.

Theorem mehler_cvg1 h x (K : R) : continuous h -> (forall y, `|h y| <= K) ->
  mehler r h x @[r --> (1 : R)] --> h x.
Proof.
by move=> ch hK; rewrite -[X in _ --> X](mehler1 h x); exact:
  continuous_mehler_r.
Qed.

Let integrable_abs_bounded (F : R -> R) (C : R) :
  measurable_fun [set: R] F -> (forall y, `|F y| <= C) ->
  N.-integrable [set: R] (EFin \o (fun y => `|F y|)).
Proof.
move=> mF FC; apply: (integrable_normal_bounded (K := C)).
  exact: measurableT_comp.
by move=> y; rewrite normr_id.
Qed.

Let mehler_L1_le f h r (K : R) :
  measurable_fun [set: R] f -> measurable_fun [set: R] h ->
  (forall y, `|f y| <= K) -> (forall y, `|h y| <= K) -> `|r| < 1 ->
  \int[N]_x `|mehler r f x - f x| <=
  \int[N]_y `|f y - h y| + \int[N]_x `|mehler r h x - h x| +
  \int[N]_y `|h y - f y|.
Proof.
move=> mf mh fK hK r1; have K0 : 0 <= K := le_trans (normr_ge0 _) (fK 0).
have mMf := measurable_mehler mf fK r1; have mMh := measurable_mehler mh hK r1.
have KK (a b : R) : `|a| <= K -> `|b| <= K -> `|a - b| <= K + K.
  by move=> aK bK; rewrite (le_trans (ler_normB _ _))// lerD.
have i1 : N.-integrable [set: R] (EFin \o (fun x => `|mehler r f x - mehler r h
  x|)).
  apply: (integrable_abs_bounded (C := K + K)); first exact: measurable_funB.
  by move=> x; rewrite KK// mehler_le.
have i2 : N.-integrable [set: R] (EFin \o (fun x => `|mehler r h x - h x|)).
  apply: (integrable_abs_bounded (C := K + K)); first exact: measurable_funB.
  by move=> x; rewrite KK// mehler_le.
have i3 : N.-integrable [set: R] (EFin \o (fun x => `|h x - f x|)).
  by apply: (integrable_abs_bounded (C := K + K)); [exact:
    measurable_funB|move=> x; rewrite KK].
have i4 : N.-integrable [set: R] (EFin \o (fun x => `|mehler r f x - f x|)).
  apply: (integrable_abs_bounded (C := K + K)); first exact: measurable_funB.
  by move=> x; rewrite KK// mehler_le.
have i12 := integrableD measurableT i1 i2.
have i123 := integrableD measurableT i12 i3.
apply: (@le_trans _ _ (\int[N]_x (`|mehler r f x - mehler r h x| +
    `|mehler r h x - h x| + `|h x - f x|))).
  apply: le_Rintegral => // x _.
  have -> : mehler r f x - f x = (mehler r f x - mehler r h x) +
      (mehler r h x - h x) + (h x - f x) by ring.
  by rewrite (le_trans (ler_normD _ _))// lerD2r ler_normD.
rewrite RintegralD// RintegralD// lerD2r lerD2r.
exact: (mehler_contraction mf mh fK hK r1).
Qed.

Let continuous_mehler_r_abs h (x K : R) : continuous h -> (forall y, `|h y| <=
  K) ->
  continuous (fun r => `|mehler r h x - h x|).
Proof.
move=> ch hK r.
exact: (cvg_norm (cvgB (@continuous_mehler_r h x K ch hK r) (cvg_cst (h x)))).
Qed.

Let sum3_lt (a b c e : R) : a < e / 3 -> b < e / 3 -> c < e / 3 -> a + b + c <=
  e.
Proof. by move=> ha hb hc; lra. Qed.

Let mehler_L1_near f (K eps : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) -> 0 < eps ->
  \forall r \near (1 : R), `|r| < 1 -> \int[N]_x `|mehler r f x - f x| <= eps.
Proof.
move=> mf fK e0; have K0 : 0 <= K := le_trans (normr_ge0 _) (fK 0).
have fb y : - K <= f y <= K by rewrite -ler_norml.
have e3 : 0 < eps / 3 by rewrite divr_gt0.
have [h [ch hb hfh]] := normal_continuous_approx mf fb e3.
have hK y : `|h y| <= K by rewrite ler_norml.
have mh := continuous_measurable_fun ch.
pose phi r := \int[N]_x `|mehler r h x - h x|.
have phi1 : phi 1 = 0.
  rewrite /phi; under eq_Rintegral do rewrite mehler1 subrr normr0.
  by rewrite Rintegral_cst// mul0r.
have cphi : phi r @[r --> (1 : R)] --> 0.
  rewrite -phi1.
  apply: (@continuity_under_integral_at _ _ _ _ N
    (fun r x => `|mehler r h x - h x|) setT 1 setT (fun=> K + K)) => //.
  - exact: filterT.
  - move=> r _; apply: (integrable_abs_bounded (C := K + K)).
      apply: measurable_funB => //.
      apply: continuous_measurable_fun; exact: continuous_mehler_x ch hK.
    by move=> x; rewrite (le_trans (ler_normB _ _))// lerD// mehler_le.
  - by move=> x _; exact: (@continuous_mehler_r_abs h x K ch hK).
  - by move=> r _ x _; rewrite normr_id (le_trans (ler_normB _ _))// lerD//
    mehler_le.
have := cphi; move=> /cvgr_lt /(_ (eps / 3) e3) phiL.
near=> r => r1.
have pr : phi r < eps / 3 by near: r.
rewrite (le_trans (mehler_L1_le mf mh fK hK r1))//.
have hfh' : \int[N]_y `|h y - f y| < eps / 3.
  by under eq_Rintegral do rewrite distrC.
rewrite /phi in pr; exact: sum3_lt hfh pr hfh'.
Unshelve. all: by end_near.
Qed.

(* For f bounded and measurable, mehler r f tends to f in L^1 of the
   standard normal law as r tends to 1 from the left. *)
Theorem mehler_cvg_L1 f (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  \int[N]_x `|mehler r f x - f x| @[r --> (1 : R)^'-] --> 0.
Proof.
move=> mf fK; apply/cvgrPdist_le => eps e0.
have H := cvg_within (fun u => u < 1) (mehler_L1_near mf fK e0).
near=> r.
have r0 : 0 < r by near: r; exact: nbhs_left_gt.
have r1 : r < 1 by near: r; exact: nbhs_left_lt.
have Hr : `|r| < 1 -> \int[N]_x `|mehler r f x - f x| <= eps by near: r; exact:
  H.
rewrite sub0r normrN ger0_norm ?Rintegral_ge0//.
by apply: Hr; rewrite gtr0_norm.
Unshelve. all: by end_near.
Qed.

Theorem ou_cvg0_L1 f (K : R) : measurable_fun [set: R] f ->
  (forall y, `|f y| <= K) ->
  \int[N]_x `|ou t f x - f x| @[t --> (0 : R)^'+] --> 0.
Proof.
move=> mf fK.
apply: (@decreasing_cvg_at_right_comp _ (fun t => expR (- t))
  (fun r => \int[N]_x `|mehler r f x - f x|) 0 (BInfty _ false) 0) => //.
- by move=> x y _ _ xy; rewrite ltr_expR ltrN2.
- apply: cvg_at_right_filter; apply: continuous_comp; first exact: continuousN.
  exact: continuous_expR.
- by rewrite oppr0 expR0; exact: mehler_cvg_L1 mf fK.
Qed.

Theorem ou_cvg0 h x (K : R) : continuous h -> (forall y, `|h y| <= K) ->
  ou t h x @[t --> (0 : R)^'+] --> h x.
Proof.
move=> ch hK; apply: cvg_at_right_filter.
rewrite -[X in _ --> X](ou0 h x) /ou.
apply: (@continuous_comp _ _ _ (fun t => expR (- t)) (fun r => mehler r h x)).
  apply: continuous_comp; first exact: continuousN.
  exact: continuous_expR.
by rewrite oppr0 expR0; exact: (@continuous_mehler_r h x K ch hK 1).
Qed.

End mehler_limits.
