From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import archimedean ring_tactic field_tactic.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun convex exp trigo measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import numfun measurable_realfun lebesgue_integral ftc.
From mathcomp Require Import probability gauss_integral.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.comparison Require Import normal_linear.
From GaussianAnalysis.fourier Require Import charfun.

(**md**************************************************************************)
(* # Esseen's inequality and the concentration of sums                        *)
(*                                                                            *)
(* The Levy concentration function Q(mu, L) = sup_a mu [a, a + L] of a law mu *)
(* on the real line (conc_fun) is at most one, nondecreasing in L, satisfies  *)
(* Q(mu, L) <= (L / L' + 1) Q(mu, L') (conc_fun_cover), and does not increase *)
(* when an independent variable is added (conc_fun_add).                      *)
(*                                                                            *)
(* Esseen's inequality bounds it by the characteristic function:             *)
(*   Q(mu, 2 pi / T) <= pi^2 / (4 T) \int_{-T}^T |cf mu t| dt    (esseen)     *)
(*                    = pi^2 / (2 T) \int_0^T |cf mu t| dt       (esseen0),   *)
(* through the Fejer kernel 2 \int_0^T (1 - t / T) cos (t z) dt =             *)
(* 2 (1 - cos (T z)) / (T z^2) (fejerE), which is at least 4 T / pi^2 for     *)
(* |z| <= pi / T by Jordan's inequality (jordan_sin, jordan_cos).             *)
(*                                                                            *)
(* For independent X_1, ..., X_n of laws mu_k with E[X_k^2] <= v and          *)
(* Q(mu_k, lambda) <= 1 - eps, the law of S = X_1 + ... + X_n satisfies       *)
(*   Q(S, L) <= 2 pi^2 sqrt pi (L + sqrt (v / eps)) / (lambda sqrt (eps n))   *)
(* (conc_fun_sum). The proof goes through the symmetrization X - X', for      *)
(* which P(|X - X'| < lambda / 2) <= Q(mu, lambda) (sym_small_ball) and       *)
(* 1 - |cf mu t|^2 >= lambda^2 eps t^2 / (4 pi^2) for small |t|               *)
(* (sym_cf_bound).                                                            *)
(*                                                                            *)
(* Laws on the line are probabilities on measurableTypeR R, as in charfun.v.  *)
(*                                                                            *)
(* ```                                                                        *)
(*   conc_fun mu L == sup_a mu [a, a + L], the Levy concentration function    *)
(*      fejer T z == \int_0^T (1 - t / T) cos (t z) dt, half the Fejer kernel *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section jordan.
Context {R : realType}.

(* Jordan's inequality: sin is above its chord on [0, pi / 2]. *)
Lemma jordan_sin (x : R) : 0 <= x <= pi / 2 -> 2 / pi * x <= sin x.
Proof.
move=> /andP[x0 x1]; have pi0 : 0 < pi :> R := pi_gt0 R.
have pi2 : 0 < pi / 2 :> R by rewrite divr_gt0.
have h1 : 2 / pi * (pi / 2) = 1 :> R.
  by rewrite mulrC !mulrA divfK ?pnatr_eq0// mulfV// gt_eqF.
pose t := 1 - 2 / pi * x.
have t1 : t <= 1 by rewrite /t gerBl mulr_ge0// divr_ge0// ltW.
have t0 : 0 <= t.
  by rewrite /t subr_ge0 -[X in _ <= X]h1 ler_pM2l// divr_gt0.
have cN : continuous (fun y : R => - sin y).
  move=> y; apply: (@continuous_comp _ _ _ sin -%R).
    exact: continuous_sin.
  exact: opp_continuous.
have Dsin : 'D_1 (fun y : R => - sin y) = (fun y => - cos y).
  by apply/funext => y; rewrite deriveN// derive_val.
have DD y : 0 < y < pi / 2 -> 0 <= 'D_1 ('D_1 (fun y : R => - sin y)) y.
  move=> /andP[y0 y1]; rewrite Dsin deriveN// derive_val opprK.
  by apply: sin_ge0_pi; apply/andP; split; lra.
have Dd : {in `]0, pi / 2[, forall y, derivable (fun y : R => - sin y) y 1}.
  by move=> y _; apply: derivableN; exact: derivable_sin.
have DDd : {in `]0, pi / 2[,
    forall y, derivable ('D_1 (fun y : R => - sin y)) y 1}.
  by move=> y _; rewrite Dsin; apply: derivableN; exact: derivable_cos.
have := @second_derivative_convex R (fun y => - sin y) 0 (pi / 2) DD
  (cvg_at_left_filter (cN _)) (cvg_at_right_filter (cN _)) Dd DDd
  (Itv01 t0 t1) (ltW pi2).
rewrite !convRE /=.
have ot : unstable.onem t = 2 / pi * x.
  by rewrite /unstable.onem /t opprB addrCA subrr addr0.
rewrite ot sin0 oppr0 !mulr0 !add0r [2 / pi * x * _]mulrAC h1 mul1r.
by rewrite sin_pihalf mulrN1 lerN2.
Qed.

(* Hence 1 - cos u >= 2 u^2 / pi^2 for |u| <= pi. *)
Lemma jordan_cos (u : R) : `|u| <= pi -> 2 / pi ^+ 2 * u ^+ 2 <= 1 - cos u.
Proof.
move=> upi; have pi0 : 0 < pi :> R := pi_gt0 R.
have pin0 : pi != 0 :> R by rewrite gt_eqF.
have two0 : 2 != 0 :> R by rewrite pnatr_eq0.
have -> : 1 - cos u = 2 * sin (u / 2) ^+ 2.
  have hu : u = (u / 2) *+ 2 by rewrite -mulr_natr divfK// pnatr_eq0.
  by rewrite [in cos u]hu cos_mulr2n cos2sin2; ring.
have hs : sin (u / 2) ^+ 2 = sin `|u / 2| ^+ 2.
  have [h|h] := leP 0 (u / 2); first by rewrite ger0_norm.
  by rewrite ltr0_norm// sinN sqrrN.
have h : 2 / pi * `|u / 2| <= sin `|u / 2|.
  apply: jordan_sin; rewrite normr_ge0 /= normrM [`|2^-1|]ger0_norm ?invr_ge0//.
  by rewrite ler_pM2r ?invr_gt0.
have a0 : 0 <= 2 / pi * `|u / 2| by rewrite mulr_ge0// divr_ge0// ltW.
have ha : (2 / pi * `|u / 2|) ^+ 2 = u ^+ 2 / pi ^+ 2.
  rewrite exprMn real_normK ?num_real// -exprMn [2 / pi * _]mulrC mulrA.
  by rewrite divfK// expr_div_n.
rewrite hs; have : (2 / pi * `|u / 2|) ^+ 2 <= sin `|u / 2| ^+ 2 by nra.
by rewrite ha => hh; rewrite mulrAC -mulrA ler_pM2l.
Qed.

End jordan.


Section fejer.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

(* The fundamental theorem of calculus, for an antiderivative on R. *)
Lemma Rintegral_FTC (f F : R -> R) (a b : R) : a < b -> continuous f ->
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

(* The Fejer kernel, without its factor 2: the integral over [0, T] of the
   triangle function 1 - t / T against cos (t z). *)
Definition fejer (T z : R) : R :=
  \int[mu]_(t in `[0, T]) ((1 - t / T) * cos (t * z)).

Let is_derive_triangle (T t : R) :
  is_derive t 1 (fun s : R => 1 - s / T) (- T^-1).
Proof.
have := is_deriveB (is_derive_cst (1 : R) t 1) (is_derive_mulr T^-1 t).
by move=> H; apply: (is_derive_eq H); rewrite sub0r.
Qed.

Let continuous_fejer_integrand (T z : R) :
  continuous (fun t : R => (1 - t / T) * cos (t * z)).
Proof.
move=> t; apply: differentiable_continuous; apply/derivable1_diffP.
exact: (@ex_derive _ _ _ _ _ _ _
  (is_deriveM (is_derive_triangle T t) (is_derive_cos_mulr z t))).
Qed.

Lemma fejerE (T z : R) : 0 < T -> z != 0 ->
  fejer T z = (1 - cos (T * z)) / (T * z ^+ 2).
Proof.
move=> T0 z0; have Tn0 : T != 0 by rewrite gt_eqF.
pose F (t : R) := (1 - t / T) * (z^-1 * sin (t * z)) -
  (T * z ^+ 2)^-1 * cos (t * z).
have dF (t : R) : is_derive t 1 F ((1 - t / T) * cos (t * z)).
  have d1 := is_derive_triangle T t.
  have d2 : is_derive t 1 (fun s : R => z^-1 * sin (s * z)) (cos (t * z)).
    have := is_deriveZ z^-1 (is_derive_sin_mulr z t).
    by move=> H; apply: (is_derive_eq H); rewrite /GRing.scale /= mulKf.
  have d3 : is_derive t 1 (fun s : R => (T * z ^+ 2)^-1 * cos (s * z))
      ((T * z ^+ 2)^-1 * - (z * sin (t * z))).
    exact: (is_deriveZ (T * z ^+ 2)^-1 (is_derive_cos_mulr z t)).
  have := is_deriveB (is_deriveM d1 d2) d3.
  move=> H; apply: (is_derive_eq H); rewrite /GRing.scale /=.
  by field.
rewrite /fejer (Rintegral_FTC T0 (@continuous_fejer_integrand T z) dF).
rewrite /F !mul0r sin0 mulr0 subr0 mul1r cos0 mulr1 mulfV// subrr mul0r.
by rewrite add0r sub0r opprK; field.
Qed.

Lemma fejer0 (T : R) : 0 < T -> fejer T 0 = T / 2.
Proof.
move=> T0; have Tn0 : T != 0 by rewrite gt_eqF.
pose F (t : R) := t - (T * 2)^-1 * t ^+ 2.
have dF (t : R) : is_derive t 1 F ((1 - t / T) * cos (t * 0)).
  have hsq : is_derive t 1 (@GRing.exp R ^~ 2) (2%:R *: t ^+ 1 *: 1).
    by apply: DeriveDef; [exact: exprn_derivable|exact: exp_derive].
  have := is_deriveB (is_derive_id t 1) (is_deriveZ (T * 2)^-1 hsq).
  move=> H; apply: (is_derive_eq H); rewrite /GRing.scale /= mulr0 cos0 mulr1.
  by rewrite expr1; field.
rewrite /fejer (Rintegral_FTC T0 (@continuous_fejer_integrand T 0) dF).
by rewrite /F expr0n /= mulr0 !subr0; field.
Qed.

End fejer.

Section fejer_bounds.
Context {R : realType}.

Lemma fejer_ge0 (T z : R) : 0 < T -> 0 <= fejer T z.
Proof.
move=> T0; have [->|z0] := eqVneq z 0; first by rewrite fejer0// divr_ge0// ltW.
rewrite fejerE// divr_ge0// ?subr_ge0 ?cos_le1//.
by rewrite mulr_ge0// ?sqr_ge0// ltW.
Qed.

Lemma fejer_ge (T z : R) : 0 < T -> `|z| <= pi / T ->
  2 * T / pi ^+ 2 <= fejer T z.
Proof.
move=> T0 zT; have pi0 : 0 < pi :> R := pi_gt0 R.
have pin0 : pi != 0 :> R by rewrite gt_eqF.
have Tn0 : T != 0 by rewrite gt_eqF.
have [->|z0] := eqVneq z 0.
  rewrite fejer0// ler_pdivrMr ?exprn_gt0//.
  have pi2 : 2 <= pi :> R := pi_ge2 R.
  have h4 : 4 <= pi ^+ 2 :> R by nra.
  have : T / 2 * 4 <= T / 2 * pi ^+ 2 by rewrite ler_pM2l ?divr_gt0.
  lra.
rewrite fejerE//.
have Tz : `|T * z| <= pi.
  by rewrite normrM gtr0_norm// -ler_pdivlMl// mulrC.
have h := jordan_cos Tz.
have Tz2 : 0 < T * z ^+ 2 by rewrite mulr_gt0// exprn_even_gt0.
rewrite ler_pdivlMr//; apply: le_trans h; rewrite le_eqVlt; apply/orP; left.
by apply/eqP; rewrite exprMn; ring.
Qed.

End fejer_bounds.

Section conc_fun.
Context {R : realType}.
Implicit Types (mu nu : probability (measurableTypeR R) R) (L a : R).

Definition conc_fun mu L : R :=
  sup [set fine (mu `[a, a + L]%classic) | a in [set: R]].

Let prob_fin mu (A : set (measurableTypeR R)) :
  measurable A -> mu A \is a fin_num.
Proof.
move=> mA; rewrite ge0_fin_numE ?measure_ge0//.
by rewrite (le_lt_trans (probability_le1 mu mA)) ?ltry.
Qed.

Let has_sup_conc mu L :
  has_sup [set fine (mu `[a, a + L]%classic) | a in [set: R]].
Proof.
split; first by exists (fine (mu `[0, 0 + L]%classic)), 0.
exists 1 => _ [a _ <-]; rewrite -lee_fin fineK ?prob_fin//.
exact: probability_le1.
Qed.

Lemma conc_fun_ub mu L a : fine (mu `[a, a + L]%classic) <= conc_fun mu L.
Proof. by apply: (sup_upper_bound (has_sup_conc mu L)); exists a. Qed.

Lemma conc_fun_ubE mu L a :
  (mu `[a, (a + L)%R]%classic <= (conc_fun mu L)%:E)%E.
Proof.
by rewrite -(fineK (prob_fin mu (measurable_itv _))) lee_fin conc_fun_ub.
Qed.

Lemma conc_fun_le mu L c :
  (forall a, mu `[a, (a + L)%R]%classic <= c%:E)%E -> conc_fun mu L <= c.
Proof.
move=> h; apply: ge_sup; first by exists (fine (mu `[0, 0 + L]%classic)), 0.
by move=> _ [a _ <-]; rewrite -lee_fin fineK ?prob_fin.
Qed.

Lemma conc_fun_ge0 mu L : 0 <= conc_fun mu L.
Proof. by apply: le_trans (conc_fun_ub mu L 0); exact: fine_ge0. Qed.

Lemma conc_fun_le1 mu L : conc_fun mu L <= 1.
Proof. by apply: conc_fun_le => a; exact: probability_le1. Qed.

Lemma le_conc_fun mu L1 L2 : L1 <= L2 -> conc_fun mu L1 <= conc_fun mu L2.
Proof.
move=> L12; apply: conc_fun_le => a; apply: le_trans (conc_fun_ubE mu L2 a).
apply: le_measure; rewrite ?inE//.
by move=> x /=; rewrite !in_itv/= => /andP[h1 h2]; apply/andP; split; lra.
Qed.

(* An interval of length L is covered by L / L' + 1 intervals of length L'. *)
Lemma conc_fun_cover mu L L' : 0 <= L -> 0 < L' ->
  conc_fun mu L <= (L / L' + 1) * conc_fun mu L'.
Proof.
move=> L0 L'0; have L'n0 : L' != 0 by rewrite gt_eqF.
set k := Num.truncn (L / L').
have /andP[kL Lk] : k%:R <= L / L' < k.+1%:R.
  by apply: truncn_itv; rewrite divr_ge0// ltW.
apply: conc_fun_le => a.
pose F (j : nat) := `[a + j%:R * L', a + j%:R * L' + L']%classic.
have cover : `[a, a + L]%classic `<=` \big[setU/set0]_(j < k.+1) F j.
  move=> x /=; rewrite in_itv /= => /andP[ax xb].
  have xa0 : 0 <= (x - a) / L' by rewrite divr_ge0// ?subr_ge0// ltW.
  have /andP[j1 j2] := truncn_itv xa0.
  have jk : (Num.truncn ((x - a) / L') < k.+1)%N.
    rewrite ltnS truncn_le_nat (le_lt_trans _ Lk)//.
    by rewrite ler_pM2r ?invr_gt0// lerBlDl.
  rewrite -bigcup_mkord; exists (Num.truncn ((x - a) / L')) => //=.
  rewrite /F /= in_itv /=; apply/andP; split.
    by rewrite -lerBrDl -ler_pdivlMr.
  move: j2; rewrite ltr_pdivrMr// -natr1 mulrDl mul1r => j2.
  by rewrite ltW//; lra.
have mF (j : nat) : `I_k.+1 j -> measurable (F j).
  by move=> _; exact: measurable_itv.
apply: le_trans (@content_subadditive _ _ _ mu _ F k.+1 mF
  (measurable_itv _) cover) _.
apply: (@le_trans _ _ (\sum_(j < k.+1) (conc_fun mu L')%:E)%E).
  by apply: lee_sum => j _; exact: conc_fun_ubE.
rewrite sumEFin lee_fin sumr_const card_ord -mulr_natl ler_wpM2r//.
  exact: conc_fun_ge0.
by rewrite -natr1 lerD2r.
Qed.

(* Adding an independent variable does not increase the concentration
   function: if nu is the law of g X + e Y for X of law P independent of Y
   of law mu, then Q(nu, |e| L) <= Q(mu, L). *)
Lemma conc_fun_add d (T : measurableType d) (P : probability T R)
    (g : T -> R) mu nu (e L : R) :
  measurable_fun [set: T] g -> e != 0 ->
  (forall A : set (measurableTypeR R), measurable A ->
     (P \x mu)%E ((fun p => g p.1 + e * p.2) @^-1` A) = nu A) ->
  conc_fun nu (`|e| * L) <= conc_fun mu L.
Proof.
move=> mg e0 numu; apply: conc_fun_le => a.
have mh : measurable_fun [set: T * measurableTypeR R]
    (fun p => g p.1 + e * p.2).
  apply: measurable_funD; first exact: measurableT_comp.
  by apply: measurable_funM => //; exact: measurable_snd.
set B := (fun p => g p.1 + e * p.2) @^-1` `[a, (a + `|e| * L)%R]%classic.
have mB : measurable B.
  by rewrite -[B]setTI; apply: mh => //; exact: measurable_itv.
rewrite -numu; first exact: measurable_itv.
rewrite /product_measure1 /=.
apply: (@le_trans _ _ (\int[P]_x (conc_fun mu L)%:E)%E); last first.
  by rewrite integral_cst// [X in (_ * X)%E]probability_setT mule1.
apply: ge0_le_integral => //.
- exact: (measurable_fun_xsection mu mB).
- move=> x _; pose b := if 0 < e then (a - g x) / e else (a - g x) / e - L.
  apply: le_trans (conc_fun_ubE mu L b); apply: le_measure.
  + by rewrite inE; exact: measurable_xsection.
  + by rewrite inE; exact: measurable_itv.
  move=> y; rewrite /xsection /B /= inE /= !in_itv /= => /andP[h1 h2].
  rewrite /b; have [ep|en] := ltP 0 e.
    rewrite gtr0_norm// in h2; apply/andP; split.
      by rewrite ler_pdivrMr//; lra.
    by rewrite -lerBlDr ler_pdivlMr//; lra.
  have en' : e < 0 by rewrite lt_neqAle e0.
  rewrite ltr0_norm// in h2; apply/andP; split.
    by rewrite lerBlDr ler_ndivrMr//; lra.
  by rewrite subrK ler_ndivlMr//; lra.
Qed.

End conc_fun.

(* Fubini's theorem for real integrals against a probability and a
   sigma-finite measure, for a measurable function dominated by an
   integrable function of the second variable. *)
Section fubini_dominated.
Context {R : realType} d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Variables (P : probability T1 R) (m : {sigma_finite_measure set T2 -> \bar R}).
Variables (F : T1 * T2 -> R) (g : T2 -> R).
Hypotheses (mF : measurable_fun [set: T1 * T2] F)
  (ig : m.-integrable [set: T2] (EFin \o g))
  (Fg : forall x y, `|F (x, y)| <= g y).

Let mFx x : measurable_fun [set: T2] (fun y => F (x, y)).
Proof. exact: measurableT_comp. Qed.

Let mFy y : measurable_fun [set: T1] (fun x => F (x, y)).
Proof. exact: measurableT_comp. Qed.

Let iFx x : m.-integrable [set: T2] (EFin \o (fun y => F (x, y))).
Proof.
apply: (le_integrable measurableT _ _ ig); first exact/measurable_EFinP.
by move=> y _; rewrite /comp !abse_EFin lee_fin (le_trans (Fg x y))// ler_norm.
Qed.

Let iFy y : P.-integrable [set: T1] (EFin \o (fun x => F (x, y))).
Proof. exact: (bounded_integrable P (@mFy y) (fun x => Fg x y)). Qed.

Let iF : (P \x m)%E.-integrable [set: T1 * T2] (EFin \o F).
Proof.
have mg2 : measurable_fun [set: T1 * T2] (fun p => (g p.2)%:E).
  apply/measurable_EFinP; apply: measurableT_comp; last exact: measurable_snd.
  by have /measurable_EFinP := measurable_int _ ig.
have g0 (p : T1 * T2) : (0 <= (g p.2)%:E)%E.
  by rewrite lee_fin (le_trans _ (Fg p.1 p.2)).
apply/integrableP; split; first exact/measurable_EFinP.
apply: (@le_lt_trans _ _ (\int[(P \x m)%E]_p (g p.2)%:E)%E).
  apply: ge0_le_integral => //.
  - by apply/measurableT_comp => //; exact/measurable_EFinP.
  - by move=> [x y] _; rewrite /comp abse_EFin lee_fin.
rewrite fubini_tonelli1//= /fubini_F /=.
rewrite integral_cst//= [X in (_ * X)%E]probability_setT mule1.
by have /fin_numPlt/andP[] := integrable_fin_num measurableT ig.
Qed.

Lemma Rintegral_fubini :
  \int[P]_x \int[m]_y F (x, y) = \int[m]_y \int[P]_x F (x, y).
Proof.
rewrite [LHS]/Rintegral [RHS]/Rintegral; congr fine.
transitivity (\int[P]_x \int[m]_y (F (x, y))%:E)%E.
  apply: eq_integral => x _; rewrite fineK//.
  by have := integrable_fin_num measurableT (@iFx x).
rewrite (Fubini iF); apply: eq_integral => y _; rewrite fineK//.
by have := integrable_fin_num measurableT (@iFy y).
Qed.

Lemma measurable_Rintegral1 :
  measurable_fun [set: T1] (fun x => \int[m]_y F (x, y)).
Proof.
apply: measurableT_comp (fine_measurable measurableT) _.
exact: (measurable_fubini_F iF).
Qed.

Lemma measurable_Rintegral2 :
  measurable_fun [set: T2] (fun y => \int[P]_x F (x, y)).
Proof.
apply: measurableT_comp (fine_measurable measurableT) _.
exact: (measurable_fubini_G iF).
Qed.

End fubini_dominated.

Section esseen.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).
Implicit Types (mu : probability (measurableTypeR R) R).

(* Esseen's inequality, with the integral over [0, T]. *)
Theorem esseen0 mu (T : R) : 0 < T ->
  conc_fun mu (2 * pi / T) <=
  pi ^+ 2 / (2 * T) * \int[leb]_(t in `[0, T]) cf_norm mu t.
Proof.
move=> T0; have pi0 : 0 < pi :> R := pi_gt0 R.
have Tn0 : T != 0 by rewrite gt_eqF.
have pin0 : pi != 0 :> R by rewrite gt_eqF.
apply: conc_fun_le => a.
set y0 := a + pi / T; set c := pi ^+ 2 / (2 * T).
have c0 : 0 < c by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
pose I : set (measurableTypeR R) := `[0, T]%classic.
have mI : measurable I by exact: measurable_itv.
pose F (p : measurableTypeR R * measurableTypeR R) : R :=
  (1 - p.2 / T) * \1_I p.2 * cos (p.2 * (p.1 - y0)).
have m2 : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => p.2 : R).
  exact: measurableT_comp (@measurable_idR R) measurable_snd.
have m1 : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => p.1 : R).
  exact: measurableT_comp (@measurable_idR R) measurable_fst.
have mF : measurable_fun [set: measurableTypeR R * measurableTypeR R] F.
  apply: measurable_funM; first apply: measurable_funM.
  - by apply: measurable_funB => //; apply: measurable_funM.
  - by apply: measurableT_comp; [exact: measurable_indic|exact: measurable_snd].
  - apply: measurable_cos_comp; apply: measurable_funM => //.
    exact: measurable_funB.
have ig : leb.-integrable [set: measurableTypeR R] (EFin \o \1_I).
  exact: integrable_indic_itv.
have Fg x t : `|F (x, t)| <= \1_I t.
  rewrite /F /= !normrM indicE; case: (t \in I) / boolP => tI; last first.
    by rewrite normr0 mulr0 mul0r.
  move: tI; rewrite /I inE /= in_itv /= => /andP[t0 tT].
  have h1 : 0 <= 1 - t / T by rewrite subr_ge0 ler_pdivrMr// mul1r.
  have h2 : 1 - t / T <= 1 by rewrite gerBl divr_ge0// ltW.
  rewrite normr1 mulr1 [`|1 - t / T|]ger0_norm//.
  have := cos_max (t * (x - y0)); have := normr_ge0 (cos (t * (x - y0))).
  nra.
have kernel x : \int[leb]_t F (x, t) = fejer T (x - y0).
  rewrite /fejer [RHS]Rintegral_mkcond; apply: eq_Rintegral => t _.
  by rewrite /F /patch /= indicE; case: ifP => _; rewrite ?mulr1 ?mulr0 ?mul0r.
have mK : measurable_fun [set: measurableTypeR R] (fun x => fejer T (x - y0)).
  apply: (eq_measurable_fun (fun x => \int[leb]_t F (x, t))) => [x _|].
    exact: kernel.
  exact: (measurable_Rintegral1 mu mF ig Fg).
have K0 x : 0 <= fejer T (x - y0) by exact: fejer_ge0.
have KT x : fejer T (x - y0) <= T.
  rewrite -kernel; apply: le_trans (ler_norm _) _.
  apply: le_trans (le_normr_Rintegral _ _) _ => //.
    by apply: (le_integrable measurableT _ _ ig) => [|t _];
      [exact/measurable_EFinP/measurableT_comp|
       rewrite /comp !abse_EFin lee_fin (le_trans (Fg x t))// ler_norm].
  apply: le_trans (le_Rintegral _ _ _ (fun t _ => Fg x t)) _ => //.
  - apply: (le_integrable measurableT _ _ ig) => [|t _].
      by apply/measurable_EFinP; apply: measurableT_comp => //;
        exact: measurableT_comp.
    by rewrite /comp !abse_EFin lee_fin normr_id (le_trans (Fg x t))// ler_norm.
  have hI : leb I = T%:E.
    have := @lebesgue_measure_itv R `[0, T]; rewrite /= lte_fin T0 oppr0 adde0.
    by move=> h; exact: h.
  rewrite /Rintegral integral_indic// setIT le_eqVlt; apply/orP; left.
  by apply/eqP; exact: (congr1 fine hI).
(* The window [a, a + 2 pi / T] is covered by the kernel. *)
have bound x : \1_`[a, (a + 2 * pi / T)%R]%classic x <= c * fejer T (x - y0).
  rewrite indicE; case: (x \in _) / boolP => xJ; last first.
    by rewrite /= mulr_ge0// ltW.
  move: xJ; rewrite inE /= in_itv /= => /andP[ax xb].
  have : 2 * T / pi ^+ 2 <= fejer T (x - y0).
    apply: fejer_ge => //; rewrite /y0 ler_norml; apply/andP; split.
      have : 2 * pi / T = pi / T + pi / T by rewrite -mulrDl -mulr2n mulr_natl.
      lra.
    have : 2 * pi / T = pi / T + pi / T by rewrite -mulrDl -mulr2n mulr_natl.
    lra.
  move=> h; apply: le_trans (ler_wpM2l (ltW c0) h).
  rewrite /c /= le_eqVlt; apply/orP; left; apply/eqP/esym.
  by rewrite mulrC mulrA divfK ?expf_neq0// mulfV// mulf_neq0// pnatr_eq0.
set J := `[a, (a + 2 * pi / T)%R]%classic.
have mJ : measurable J by exact: measurable_itv.
have mJ1 : measurable_fun [set: measurableTypeR R] (\1_J : _ -> R).
  exact: measurable_indic.
have iK : mu.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => fejer T (x - y0))).
  apply: (bounded_integrable mu mK (C := T)) => x.
  by rewrite ger0_norm.
have mJfin : mu J \is a fin_num.
  rewrite ge0_fin_numE ?measure_ge0//.
  by rewrite (le_lt_trans (probability_le1 mu mJ)) ?ltry.
have E1 : mu J = (\int[mu]_x \1_J x)%:E.
  rewrite /Rintegral integral_indic// setIT fineK//.
rewrite E1 lee_fin.
apply: (@le_trans _ _ (\int[mu]_x (c * fejer T (x - y0)))).
  apply: le_Rintegral => //.
  - by apply: (bounded_integrable mu mJ1 (C := 1)) => x; rewrite indicE;
      case: (x \in J) => /=; rewrite ?normr1 ?normr0.
  - apply: (bounded_integrable mu (C := c * T)).
      by apply: measurable_funM => //; exact: mK.
    by move=> x; rewrite normrM gtr0_norm// ger0_norm// ler_pM2l.
rewrite (RintegralZl c measurableT iK) ler_pM2l//.
under eq_Rintegral do rewrite -kernel.
rewrite (Rintegral_fubini mu mF ig Fg).
(* Each t contributes at most cf_norm mu t on [0, T]. *)
have inner t : \int[mu]_x F (x, t) =
    (1 - t / T) * \1_I t *
    (cos (t * y0) * cf_re mu t + sin (t * y0) * cf_im mu t).
  have icos : mu.-integrable [set: measurableTypeR R]
      (EFin \o (fun x : measurableTypeR R => cos (t * (x - y0)))).
    exact: (integrable_cos_comp mu (measurable_funM (measurable_cst t)
      (measurable_funB (@measurable_idR R) (measurable_cst y0)))).
  rewrite /F (RintegralZl ((1 - t / T) * \1_I t) measurableT icos).
  congr (_ * _); rewrite /cf_re /cf_im -Rintegral_cos_sin.
    exact: mulrl_measurable.
  by apply: eq_Rintegral => x _; rewrite mulrBr cosB mulrC [sin _ * _]mulrC.
have mcf : measurable_fun [set: measurableTypeR R] (cf_norm mu).
  have h : measurable_fun [set: R] (cf_norm mu).
    exact: continuous_measurable_fun (@continuous_cf_norm R mu).
  exact: h.
have iG : leb.-integrable [set: measurableTypeR R]
    (EFin \o (fun t => \1_I t * cf_norm mu t)).
  apply: (le_integrable measurableT _ _ ig).
    by apply/measurable_EFinP; apply: measurable_funM => //;
      exact: measurable_indic.
  move=> t _; rewrite /comp !abse_EFin lee_fin normrM.
  rewrite [`|cf_norm _ _|]ger0_norm ?cf_norm_ge0//.
  by rewrite ler_piMr// ?cf_norm_le1// normr_id.
apply: (@le_trans _ _ (\int[leb]_t (\1_I t * cf_norm mu t))).
  apply: le_Rintegral => //.
  - apply: (le_integrable measurableT _ _ ig).
      by apply/measurable_EFinP; exact: (measurable_Rintegral2 mu mF ig Fg).
    move=> t _; rewrite /comp !abse_EFin lee_fin [`|\1_I t|]ger0_norm//.
    apply: Rintegral_bounded => [|x]; last exact: Fg.
    exact: measurableT_comp.
  move=> t _; rewrite inner indicE; case: (t \in I) / boolP => tI; last first.
    by rewrite /= !mulr0 !mul0r.
  move: tI; rewrite /I inE /= in_itv /= => /andP[t0 tT].
  have h1 : 0 <= 1 - t / T by rewrite subr_ge0 ler_pdivrMr// mul1r.
  have h2 : 1 - t / T <= 1 by rewrite gerBl divr_ge0// ltW.
  have h3 : cos (t * y0) * cf_re mu t + sin (t * y0) * cf_im mu t <=
      cf_norm mu t.
    apply: le_trans (ler_norm _) _; rewrite cf_normE /cf mulrC [sin _ * _]mulrC.
    by apply: cmod_ge_dot; rewrite cos2Dsin2.
  have h4 := cf_norm_ge0 mu t.
  rewrite /= mulr1 mul1r; nra.
rewrite [X in _ <= X]Rintegral_mkcond le_eqVlt; apply/orP; left; apply/eqP.
apply: eq_Rintegral => t _; rewrite /patch indicE.
by case: (t \in _) => /=; rewrite ?mul1r ?mul0r.
Qed.

(* The integral over [- T, T] of an even continuous function. *)
Lemma Rintegral_even (f : R -> R) (T : R) : 0 < T -> continuous f ->
  (forall t, f (- t) = f t) ->
  \int[leb]_(t in `[- T, T]) f t = 2 * \int[leb]_(t in `[0, T]) f t.
Proof.
move=> T0 cf ef.
have U : `[- T, T]%classic = `[- T, 0[%classic `|` `[0, T]%classic.
  by apply: itv_bndbnd_setU; rewrite bnd_simp ?oppr_le0 ltW.
have iT : leb.-integrable (`[- T, 0[%classic `|` `[0, T]%classic) (EFin \o f).
  rewrite -U; apply: continuous_compact_integrable.
    exact: segment_compact.
  by apply: continuous_subspaceT.
have disj : [disjoint `[- T, 0[%classic & `[0, T]%classic].
  apply/disj_setPS => x [/=]; rewrite !in_itv /= => /andP[_ h1] /andP[h2 _].
  lra.
rewrite U Rintegral_setU//; try exact: measurable_itv.
rewrite Rintegral_itv_bndo_bndc.
  apply: (integrableS _ _ _ iT); last exact: subsetUl.
    by apply: measurableU; exact: measurable_itv.
  exact: measurable_itv.
have h := @integration_by_substitution_oppr R f 0 T (ltW T0)
  (continuous_subspaceT cf).
rewrite oppr0 in h.
have ev x : ((f \o -%R) x)%:E = (f x)%:E by rewrite /comp ef.
rewrite /Rintegral h.
under [X in fine X + _ = _]eq_integral => x _ do rewrite ev.
by rewrite -/(Rintegral _ _ _) mulr2n mulrDl mul1r.
Qed.

(* Esseen's inequality: for every law mu and T > 0,
   Q(mu, 2 pi / T) <= pi^2 / (4 T) \int_{-T}^{T} |cf mu t| dt. *)
Theorem esseen mu (T : R) : 0 < T ->
  conc_fun mu (2 * pi / T) <=
  pi ^+ 2 / (4 * T) * \int[leb]_(t in `[- T, T]) cf_norm mu t.
Proof.
move=> T0; have ev t : cf_norm mu (- t) = cf_norm mu t by exact: cf_normN.
rewrite (Rintegral_even T0 (@continuous_cf_norm R mu) ev).
apply: le_trans (esseen0 mu T0) _; rewrite le_eqVlt; apply/orP; left.
apply/eqP; have Tn0 : T != 0 by rewrite gt_eqF.
by move: (pi) => p; field.
Qed.

End esseen.

(* The symmetrization X - X' of a law mu, on the product space mu \x mu. *)
Section symmetrization.
Context {R : realType} (mu : probability (measurableTypeR R) R).
Local Notation PP := (mu \x mu)%E.

Let mdiff : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => p.1 - p.2 : R).
Proof.
apply: measurable_funB.
  exact: measurableT_comp (@measurable_idR R) measurable_fst.
exact: measurableT_comp (@measurable_idR R) measurable_snd.
Qed.

(* P(|X - X'| < lambda / 2) <= Q(mu, lambda). *)
Lemma sym_small_ball (lambda : R) :
  (PP [set p | (`|p.1 - p.2| < lambda / 2)%R] <= (conc_fun mu lambda)%:E)%E.
Proof.
set S := [set p | _].
have mS : measurable S.
  have -> : S = (fun p => p.1 - p.2 : R) @^-1`
      `](- (lambda / 2))%R, (lambda / 2)%R[%classic.
    by apply/seteqP; split => p; rewrite /S /= in_itv /= ltr_norml.
  rewrite -[X in measurable X]setTI.
  by apply: mdiff => //; exact: measurable_itv.
rewrite /product_measure1 /=.
apply: (@le_trans _ _ (\int[mu]_x (conc_fun mu lambda)%:E)%E); last first.
  by rewrite integral_cst// [X in (_ * X)%E]probability_setT mule1.
apply: ge0_le_integral => //.
- exact: (measurable_fun_xsection mu mS).
- move=> x _; apply: le_trans (conc_fun_ubE mu lambda (x - lambda / 2)).
  apply: le_measure; rewrite ?inE.
  + exact: measurable_xsection.
  + exact: measurable_itv.
  move=> y; rewrite /xsection /S /= inE /= in_itv /= => h.
  by rewrite ltr_norml in h; apply/andP; split; lra.
Qed.

(* The second moment of X - X' is at most 4 v. *)
(* E[(X - X')^2] <= 4 E[(X - a)^2] for every a. *)
Lemma sym_second_moment_center (a v : R) :
  (\int[mu]_x ((((x : R) - a) ^+ 2)%R)%:E <= v%:E)%E ->
  (\int[PP]_p (((p.1 - p.2) ^+ 2)%R)%:E <= (4 * v)%:E)%E.
Proof.
move=> mu2.
have m1 : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => ((((p.1 : R) - a) ^+ 2)%R)%:E).
  apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB.
    exact: measurableT_comp (@measurable_idR R) measurable_fst.
  exact: measurable_cst.
have m2 : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => ((((p.2 : R) - a) ^+ 2)%R)%:E).
  apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB.
    exact: measurableT_comp (@measurable_idR R) measurable_snd.
  exact: measurable_cst.
have mx2 : measurable_fun [set: measurableTypeR R]
    (fun x => ((((x : R) - a) ^+ 2)%R)%:E).
  apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB.
    exact: measurable_idR.
  exact: measurable_cst.
have E1 : (\int[PP]_p ((((p.1 : R) - a) ^+ 2)%R)%:E =
    \int[mu]_x ((((x : R) - a) ^+ 2)%R)%:E)%E.
  rewrite fubini_tonelli1//=; first by move=> p; rewrite lee_fin sqr_ge0.
  apply: eq_integral => x _; rewrite /fubini_F /= integral_cst//.
  by rewrite [X in (_ * X)%E]probability_setT mule1.
have E2 : (\int[PP]_p ((((p.2 : R) - a) ^+ 2)%R)%:E =
    \int[mu]_x ((((x : R) - a) ^+ 2)%R)%:E)%E.
  rewrite fubini_tonelli1//=; first by move=> p; rewrite lee_fin sqr_ge0.
  rewrite /fubini_F /= integral_cst//= [X in (_ * X)%E]probability_setT mule1.
  by [].
apply: (@le_trans _ _ (\int[PP]_p (2%:E * ((((p.1 : R) - a) ^+ 2)%R)%:E +
    2%:E * ((((p.2 : R) - a) ^+ 2)%R)%:E))%E).
  apply: ge0_le_integral => //.
  - by move=> p _; rewrite lee_fin sqr_ge0.
  - apply/measurable_EFinP; apply: measurable_funX; exact: mdiff.
  - by apply: emeasurable_funD; apply: emeasurable_funM.
  - move=> p _; rewrite -!EFinM -EFinD lee_fin.
    by have := sqr_ge0 ((p.1 : R) - a + ((p.2 : R) - a)); nra.
rewrite ge0_integralD//.
- by move=> p _; rewrite mule_ge0// lee_fin sqr_ge0.
- exact: emeasurable_funM.
- by move=> p _; rewrite mule_ge0// lee_fin sqr_ge0.
- exact: emeasurable_funM.
rewrite ge0_integralZl//; first by move=> p _; rewrite lee_fin sqr_ge0.
rewrite ge0_integralZl//; first by move=> p _; rewrite lee_fin sqr_ge0.
rewrite E1 E2.
apply: (@le_trans _ _ (2%:E * v%:E + 2%:E * v%:E)%E).
  by apply: leeD; apply: lee_wpmul2l => //; rewrite lee_fin.
by rewrite -!EFinM -EFinD lee_fin; lra.
Qed.

Lemma sym_second_moment (v : R) :
  (\int[mu]_x ((x ^+ 2)%R)%:E <= v%:E)%E ->
  (\int[PP]_p (((p.1 - p.2) ^+ 2)%R)%:E <= (4 * v)%:E)%E.
Proof.
move=> mu2; apply: (@sym_second_moment_center 0).
by under eq_integral do rewrite subr0.
Qed.

(* Markov's inequality for X - X'. *)
Lemma sym_tail (v r : R) : 0 < r ->
  (\int[mu]_x ((x ^+ 2)%R)%:E <= v%:E)%E ->
  (PP [set p | (r < `|p.1 - p.2|)%R] <= (4 * v / r ^+ 2)%:E)%E.
Proof.
move=> r0 mu2; set S := [set p | _].
have mS : measurable S.
  have -> : S = (fun p => p.1 - p.2 : R) @^-1`
      (`]-oo, (- r)%R[ `|` `]r, +oo[)%classic.
    apply/seteqP; split => p; rewrite /S /= !in_itv /= ltr_normr.
      by case/orP => h; [right|left]; lra.
    by case => h; apply/orP; [right|left]; lra.
  rewrite -[X in measurable X]setTI; apply: mdiff => //.
  by apply: measurableU; exact: measurable_itv.
have md2 : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => (((p.1 - p.2) ^+ 2)%R)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: mdiff.
apply: (@le_trans _ _ (\int[PP]_p (\1_S p)%:E)%E).
  by rewrite integral_indic// setIT.
apply: (@le_trans _ _
  (\int[PP]_p ((r ^+ 2)^-1%:E * (((p.1 - p.2) ^+ 2)%R)%:E))%E).
  apply: ge0_le_integral => //.
  - exact/measurable_EFinP/measurable_indic.
  - exact: emeasurable_funM.
  - move=> p _; rewrite indicE -EFinM lee_fin.
    case: (p \in S) / boolP => pS; last by rewrite mulr_ge0 ?invr_ge0 ?sqr_ge0.
    move: pS; rewrite inE /S /= => h.
    rewrite mulrC ler_pdivlMr ?exprn_gt0// mul1r -[X in _ <= X]real_normK.
      exact: num_real.
    by have := normr_ge0 (p.1 - p.2); nra.
rewrite ge0_integralZl//; first by move=> p _; rewrite lee_fin sqr_ge0.
  by rewrite lee_fin invr_ge0 sqr_ge0.
apply: (@le_trans _ _ ((r ^+ 2)^-1%:E * (4 * v)%:E)%E).
  apply: lee_wpmul2l; first by rewrite lee_fin invr_ge0 sqr_ge0.
  exact: sym_second_moment.
by rewrite -EFinM lee_fin mulrC.
Qed.

Let msmall (a : R) :
  measurable [set p : measurableTypeR R * measurableTypeR R |
    (`|p.1 - p.2| < a)%R].
Proof.
have -> : [set p : measurableTypeR R * measurableTypeR R | (`|p.1 - p.2| < a)%R]
    = (fun p => p.1 - p.2 : R) @^-1` `](- a)%R, a[%classic.
  by apply/seteqP; split => p; rewrite /= in_itv /= ltr_norml.
by rewrite -[X in measurable X]setTI; apply: mdiff => //; exact: measurable_itv.
Qed.

Let mlarge (a : R) :
  measurable [set p : measurableTypeR R * measurableTypeR R |
    (a < `|p.1 - p.2|)%R].
Proof.
have -> : [set p : measurableTypeR R * measurableTypeR R | (a < `|p.1 - p.2|)%R]
    = (fun p => p.1 - p.2 : R) @^-1` (`]-oo, (- a)%R[ `|` `]a, +oo[)%classic.
  apply/seteqP; split => p; rewrite /= !in_itv /= ltr_normr.
    by case/orP => h; [right|left]; lra.
  by case => h; apply/orP; [right|left]; lra.
rewrite -[X in measurable X]setTI; apply: mdiff => //.
by apply: measurableU; exact: measurable_itv.
Qed.

Let PPfin (A : set (measurableTypeR R * measurableTypeR R)) :
  measurable A -> PP A = (fine (PP A))%:E.
Proof.
move=> mA; rewrite fineK// ge0_fin_numE ?measure_ge0//.
by rewrite (le_lt_trans (probability_le1 _ mA)) ?ltry.
Qed.

(* |cf mu t|^2 is the characteristic function of X - X' at t. *)
Lemma cf_norm_sqr_sym (t : R) :
  cf_norm mu t ^+ 2 = \int[PP]_p cos (t * (p.1 - p.2)).
Proof.
have mN : measurable_fun [set: measurableTypeR R] (fun y => - y : R).
  exact: measurable_funN.
have E1 : \int[mu]_y cos (t * - y) = cf_re mu t.
  by apply: eq_Rintegral => y _; rewrite mulrN cosN.
have E2 : \int[mu]_y sin (t * - y) = - cf_im mu t.
  rewrite /cf_im -RintegralN; first exact: integrable_sin_mul.
  by apply: eq_Rintegral => y _; rewrite mulrN sinN.
have := cf_prod_integral mu mu (@measurable_idR R) mN t.
rewrite /= E1 E2 cmulE => -[-> _].
by rewrite /cf_norm sqr_sqrtr ?addr_ge0 ?sqr_ge0// /cf_re /cf_im; ring.
Qed.

(* The bound behind the inequality for sums: if Q(mu, lambda) <= 1 - eps
   and E[X^2] <= v, then 1 - |cf mu t|^2 >= lambda^2 eps t^2 / (4 pi^2) for
   |t| <= pi / r, as soon as 8 v <= eps r^2. *)
Lemma sym_cf_bound (v lambda eps r t : R) :
  0 < lambda -> 0 < eps -> 0 < r ->
  conc_fun mu lambda <= 1 - eps ->
  (\int[mu]_x ((x ^+ 2)%R)%:E <= v%:E)%E -> 8 * v <= eps * r ^+ 2 ->
  `|t| <= pi / r ->
  cf_norm mu t ^+ 2 <= 1 - lambda ^+ 2 * eps / (4 * pi ^+ 2) * t ^+ 2.
Proof.
move=> l0 e0 r0 Q mu2 vr tr; have pi0 : 0 < pi :> R := pi_gt0 R.
have pin0 : pi != 0 :> R by rewrite gt_eqF.
set A1 := [set p : measurableTypeR R * measurableTypeR R |
  (`|p.1 - p.2| < lambda / 2)%R].
set A2 := [set p : measurableTypeR R * measurableTypeR R |
  (r < `|p.1 - p.2|)%R].
set E := ~` (A1 `|` A2).
have mA1 : measurable A1 by exact: msmall.
have mA2 : measurable A2 by exact: mlarge.
have mA12 : measurable (A1 `|` A2) by exact: measurableU.
have mE : measurable E by exact: measurableC.
(* P(E) >= eps / 2 *)
have PE : eps / 2 <= fine (PP E).
  have h1 : fine (PP A1) <= 1 - eps.
    rewrite -lee_fin -PPfin//; apply: le_trans (sym_small_ball lambda) _.
    by rewrite lee_fin.
  have h2 : fine (PP A2) <= eps / 2.
    rewrite -lee_fin -PPfin//; apply: le_trans (sym_tail r0 mu2) _.
    rewrite lee_fin ler_pdivrMr ?exprn_gt0//; lra.
  have h12 : fine (PP (A1 `|` A2)) <= fine (PP A1) + fine (PP A2).
    by rewrite -lee_fin EFinD -!PPfin//; exact: measureU2.
  have hE : fine (PP E) = 1 - fine (PP (A1 `|` A2)).
    by apply/EFin_inj; rewrite EFinB -!PPfin// probability_setC.
  lra.
(* the integral of 1 - cos (t (X - X')) *)
have mc : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => cos (t * (p.1 - p.2))).
  exact: measurable_cos_mul mdiff.
have ic : PP.-integrable [set: _] (EFin \o (fun p => cos (t * (p.1 - p.2)))).
  exact: integrable_cos_mul.
have i1 : PP.-integrable [set: measurableTypeR R * measurableTypeR R]
    (EFin \o cst (1 : R)).
  by apply: (bounded_integrable PP (C := 1)) => // p; rewrite normr1.
have H1 : 1 - cf_norm mu t ^+ 2 = \int[PP]_p (1 - cos (t * (p.1 - p.2))).
  rewrite cf_norm_sqr_sym RintegralB//.
  by rewrite Rintegral_cst// [X in _ * fine X]probability_setT mul1r.
set c := 2 / pi ^+ 2 * t ^+ 2 * (lambda / 2) ^+ 2.
have c0 : 0 <= c.
  rewrite /c; apply: mulr_ge0; last exact: sqr_ge0.
  by apply: mulr_ge0; [rewrite divr_ge0// sqr_ge0|exact: sqr_ge0].
have pw p : c * \1_E p <= 1 - cos (t * (p.1 - p.2)).
  rewrite indicE; case: (p \in E) / boolP => pE; last first.
    by rewrite /= mulr0 subr_ge0 cos_le1.
  move: pE; rewrite inE /E /A1 /A2 /= => /not_orP[/negP h1 /negP h2].
  rewrite -leNgt in h1; rewrite -leNgt in h2.
  have hd : `|t * (p.1 - p.2)| <= pi.
    rewrite normrM; apply: le_trans (ler_wpM2l (normr_ge0 t) h2) _.
    by rewrite -ler_pdivlMr.
  have hd2 : (lambda / 2) ^+ 2 <= (p.1 - p.2) ^+ 2.
    rewrite -[X in _ <= X]real_normK; first exact: num_real.
    have : 0 <= lambda / 2 by rewrite divr_ge0// ltW.
    nra.
  have k0 : 0 <= 2 / pi ^+ 2 * t ^+ 2.
    by apply: mulr_ge0; [rewrite divr_ge0// sqr_ge0|exact: sqr_ge0].
  have e : 2 / pi ^+ 2 * (t * (p.1 - p.2)) ^+ 2 =
      2 / pi ^+ 2 * t ^+ 2 * (p.1 - p.2) ^+ 2 by rewrite exprMn mulrA.
  apply: le_trans (jordan_cos hd); rewrite /= mulr1 /c e.
  by apply: ler_wpM2l.
have iE : PP.-integrable [set: _] (EFin \o (fun p => c * \1_E p)).
  apply: (bounded_integrable PP (C := c)).
    by apply: measurable_funM => //; exact: measurable_indic.
  move=> p; rewrite normrM ger0_norm// indicE.
  by case: (p \in E); rewrite /= ?normr1 ?normr0 ?mulr1 ?mulr0.
have i2 : PP.-integrable [set: _]
    (EFin \o (fun p => 1 - cos (t * (p.1 - p.2)))).
  apply: (bounded_integrable PP (C := 2)).
    by apply: measurable_funB => //.
  move=> p; apply: le_trans (ler_normB _ _) _.
  by rewrite normr1; have := cos_max (t * (p.1 - p.2)); lra.
have := le_Rintegral measurableT iE i2 (fun p _ => pw p).
rewrite -H1 RintegralZl//.
  by apply: (bounded_integrable PP (C := 1)) => [|p];
    [exact: measurable_indic|rewrite indicE; case: (p \in E);
     rewrite /= ?normr1 ?normr0].
have -> : \int[PP]_p \1_E p = fine (PP E).
  by rewrite /Rintegral integral_indic// setIT.
move=> h; have : c * (eps / 2) <= 1 - cf_norm mu t ^+ 2.
  by apply: le_trans h; apply: ler_wpM2l.
have -> : c * (eps / 2) = lambda ^+ 2 * eps / (4 * pi ^+ 2) * t ^+ 2.
  have q0 : pi ^+ 2 != 0 :> R by rewrite expf_neq0.
  by rewrite /c; move: (pi ^+ 2) q0 => q q0; field.
lra.
Qed.

Lemma sym_cf_bound_expR (v lambda eps r t : R) :
  0 < lambda -> 0 < eps -> 0 < r ->
  conc_fun mu lambda <= 1 - eps ->
  (\int[mu]_x ((x ^+ 2)%R)%:E <= v%:E)%E -> 8 * v <= eps * r ^+ 2 ->
  `|t| <= pi / r ->
  cf_norm mu t <= expR (- (lambda ^+ 2 * eps / (8 * pi ^+ 2)) * t ^+ 2).
Proof.
move=> l0 e0 r0 Q mu2 vr tr.
have h := sym_cf_bound l0 e0 r0 Q mu2 vr tr.
set b := lambda ^+ 2 * eps / (8 * pi ^+ 2).
have hb : lambda ^+ 2 * eps / (4 * pi ^+ 2) = 2 * b.
  have q0 : pi ^+ 2 != 0 :> R by rewrite expf_neq0// gt_eqF// pi_gt0.
  by rewrite /b; move: (pi ^+ 2) q0 => q q0; field.
have e2 : expR (- b * t ^+ 2) ^+ 2 = expR (- (2 * b) * t ^+ 2).
  by rewrite expr2 -expRD; congr expR; ring.
have h2 : cf_norm mu t ^+ 2 <= expR (- b * t ^+ 2) ^+ 2.
  rewrite e2; apply: le_trans h _; rewrite hb.
  by have := expR_ge1Dx (- (2 * b) * t ^+ 2); lra.
have := cf_norm_ge0 mu t; have := expR_ge0 (- b * t ^+ 2); nra.
Qed.

End symmetrization.

Section gauss_half_line.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).

(* The integral of exp (- (c t)^2) over [0, T] is at most sqrt pi / (2 c). *)
Lemma integral_gauss_half_le (c T : R) : 0 < c -> 0 < T ->
  \int[leb]_(t in `[0, T]) expR (- (c * t) ^+ 2) <= Num.sqrt pi / (2 * c).
Proof.
move=> c0 T0.
pose h (u : R) := (gauss_fun u * \1_(`[0, +oo[%classic : set R) u)%:E.
have mh : measurable_fun [set: R] h.
  apply/measurable_EFinP; apply: measurable_funM.
    exact: measurable_gauss_fun.
  exact: measurable_indic.
have h0 u : (0 <= h u)%E.
  by rewrite lee_fin mulr_ge0// ?gauss_fun_ge0// indicE; case: (u \in _).
have I0 : (\int[leb]_u h u = (Num.sqrt pi / 2)%:E)%E.
  rewrite -integral0y_gauss [RHS]integral_mkcond; apply: eq_integral => u _.
  rewrite /h /patch indicE; case: (u \in _) => /=.
    by rewrite mulr1.
  by rewrite mulr0.
have cn0 : c != 0 by rewrite gt_eqF.
have aff := @ge0_integral_lebesgue_affine R c 0 h cn0 mh h0.
have E : (\int[leb]_(t in `[0%R, +oo[%classic) (expR (- (c * t) ^+ 2))%:E =
    (`|c|^-1)%:E * \int[leb]_x h x)%E.
  rewrite -aff integral_mkcond; apply: eq_integral => t _.
  rewrite /h /patch addr0 !indicE /gauss_fun.
  have -> : (c * t \in `[0, +oo[%classic) = (t \in `[0, +oo[%classic).
    apply/idP/idP; rewrite !in_setE /= !in_itv /= !andbT.
      by rewrite pmulr_rge0.
    by move=> ht; rewrite mulr_ge0// ltW.
  by case: (t \in _) => /=; rewrite ?mulr1 ?mulr0.
rewrite I0 gtr0_norm// -EFinM in E.
have le : (\int[leb]_(t in `[0%R, T]%classic) (expR (- (c * t) ^+ 2))%:E <=
    \int[leb]_(t in `[0%R, +oo[%classic) (expR (- (c * t) ^+ 2))%:E)%E.
  have mg : measurable_fun [set: R] (fun t : R => gauss_fun (c * t)).
    apply: continuous_measurable_fun => t.
    apply: (@continuous_comp _ _ _ ( *%R c) gauss_fun).
      exact: mulrl_continuous.
    exact: continuous_gauss_fun.
  apply: ge0_subset_integral.
  - exact: measurable_itv.
  - exact: measurable_itv.
  - by apply/measurable_EFinP/measurable_funTS.
  - by move=> t _; rewrite lee_fin expR_ge0.
  - by move=> t /=; rewrite !in_itv /= => /andP[-> _].
rewrite /Rintegral; apply: le_trans (fine_le _ _ le) _.
- rewrite ge0_fin_numE.
    by apply: integral_ge0 => t _; rewrite lee_fin expR_ge0.
  by rewrite (le_lt_trans le)// E ltry.
- by rewrite E.
rewrite E /= le_eqVlt; apply/orP; left; apply/eqP.
by rewrite invfM; ring.
Qed.

End gauss_half_line.

(* The inequality for sums of independent variables under a second moment
   condition (Kolmogorov-Rogozin type). *)
Section conc_fun_sum.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).

Theorem conc_fun_sum (mu : nat -> probability (measurableTypeR R) R) (n : nat)
    (nu : probability (measurableTypeR R) R) (v lambda eps L : R) :
  (0 < n)%N -> 0 < v -> 0 < lambda -> 0 < eps -> 0 <= L ->
  (forall k, (k < n)%N -> (\int[mu k]_x ((x ^+ 2)%R)%:E <= v%:E)%E) ->
  (forall k, (k < n)%N -> conc_fun (mu k) lambda <= 1 - eps) ->
  (forall A : set (measurableTypeR R), measurable A ->
     tuple_prod mu n ((fun x => \sum_(k < n) tnth x k) @^-1` A) = nu A) ->
  conc_fun nu L <= 2 * pi ^+ 2 * Num.sqrt pi * (L + Num.sqrt (v / eps)) /
    (lambda * Num.sqrt (eps * n%:R)).
Proof.
move=> n0 v0 l0 e0 L0 mu2 Q numu.
have pi0 : 0 < pi :> R := pi_gt0 R.
set s := Num.sqrt (v / eps).
have s0 : 0 < s by rewrite sqrtr_gt0 divr_gt0.
set q := Num.sqrt (2 : R).
have q0 : 0 < q by rewrite sqrtr_gt0.
have q2 : q ^+ 2 = 2 by rewrite sqr_sqrtr// ler0n.
set r := 2 * q * s.
have r0 : 0 < r by rewrite !mulr_gt0.
have vr : 8 * v <= eps * r ^+ 2.
  have ve : 0 <= v / eps by rewrite divr_ge0// ltW.
  rewrite /r !exprMn q2 (sqr_sqrtr ve).
  have en0 : eps != 0 by rewrite gt_eqF.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
set T := pi / r.
have T0 : 0 < T by rewrite divr_gt0.
have TE : 2 * pi / T = 2 * r.
  have rn0 : r != 0 by rewrite gt_eqF.
  rewrite /T; move: pi0; move: (pi) => p p0.
  have pn0 : p != 0 by rewrite gt_eqF.
  by field.
have numu1 (A : set (measurableTypeR R)) : measurable A ->
    tuple_prod mu n ((fun x => \sum_(k < n) (fun=> 1) k * tnth x k) @^-1` A)
    = nu A.
  move=> mA; rewrite -numu//; congr (tuple_prod mu n (_ @^-1` A)).
  by apply/funext => x; apply: eq_bigr => k _; rewrite mul1r.
set b := lambda ^+ 2 * eps / (8 * pi ^+ 2).
have b0 : 0 < b by rewrite divr_gt0 ?mulr_gt0 ?exprn_gt0.
set c := Num.sqrt (n%:R * b).
have c0 : 0 < c by rewrite sqrtr_gt0 mulr_gt0// ltr0n.
have bound t : 0 <= t <= T -> cf_norm nu t <= expR (- (c * t) ^+ 2).
  move=> /andP[t0 tT].
  rewrite (@cf_norm_tuple_prod R mu n (fun=> 1) nu numu1 t).
  have nb0 : 0 <= n%:R * b by rewrite mulr_ge0// ?ler0n// ltW.
  have -> : - (c * t) ^+ 2 = n%:R * (- b * t ^+ 2).
    by rewrite exprMn /c (sqr_sqrtr nb0); ring.
  rewrite expRM_natl -[X in _ ^+ X]card_ord -prodr_const.
  apply: ler_prod => k _; rewrite cf_norm_ge0 /= mul1r.
  apply: (@sym_cf_bound_expR _ _ v lambda eps r) => //.
  - exact: Q.
  - exact: mu2.
  - by rewrite ger0_norm.
have cnt : continuous (fun t : R => expR (- (c * t) ^+ 2)).
  move=> t; apply: (@continuous_comp _ _ _ ( *%R c) gauss_fun).
    exact: mulrl_continuous.
  exact: continuous_gauss_fun.
have int_le : \int[leb]_(t in `[0, T]) cf_norm nu t <= Num.sqrt pi / (2 * c).
  apply: le_trans (integral_gauss_half_le c0 T0).
  apply: le_Rintegral.
  - exact: measurable_itv.
  - apply: continuous_compact_integrable; first exact: segment_compact.
    by apply: continuous_subspaceT; exact: (@continuous_cf_norm R nu).
  - apply: continuous_compact_integrable; first exact: segment_compact.
    by apply: continuous_subspaceT => t; exact: cnt.
  - by move=> t; rewrite /= in_itv /=; exact: bound.
have es := esseen0 nu T0; rewrite TE in es.
have r2 : 0 < 2 * r by rewrite mulr_gt0.
apply: le_trans (conc_fun_cover nu L0 r2) _.
apply: le_trans (ler_wpM2l _ (le_trans es (ler_wpM2l _ int_le))) _.
- by rewrite addr_ge0// divr_ge0// ltW.
- by rewrite divr_ge0// ?sqr_ge0// mulr_ge0// ltW.
set w := Num.sqrt (eps * n%:R).
have w0 : 0 < w by rewrite sqrtr_gt0 mulr_gt0// ltr0n.
have en0 : 0 <= eps * n%:R by rewrite mulr_ge0 ?ler0n// ltW.
have nb0 : 0 <= n%:R * b by rewrite mulr_ge0 ?ler0n// ltW.
have h2qp : 0 < 2 * q * pi by rewrite !mulr_gt0.
have cE0 : c * (2 * q * pi) = lambda * w.
  have x0 : 0 <= c * (2 * q * pi) by rewrite mulr_ge0// ltW.
  have y0 : 0 <= lambda * w by rewrite mulr_ge0// ltW.
  apply/eqP; rewrite -(@eqrXn2 _ 2 _ _ erefl x0 y0).
  rewrite !exprMn q2 /c (sqr_sqrtr nb0) (sqr_sqrtr en0) /b.
  apply/eqP; move: pi0; move: (pi) => p p0.
  have pn0 : p != 0 by rewrite gt_eqF.
  by field.
have cE : c = lambda * w / (2 * q * pi).
  by rewrite -cE0 mulfK// gt_eqF.
set K := pi ^+ 2 * Num.sqrt pi / (lambda * w).
have K0 : 0 <= K.
  by rewrite divr_ge0 ?mulr_ge0 ?sqrtr_ge0 ?sqr_ge0// ltW// mulr_gt0.
have LE : (L / (2 * r) + 1) * (pi ^+ 2 / (2 * T) * (Num.sqrt pi / (2 * c))) =
    K * ((L + 2 * r) * q / 4).
  rewrite cE /T /K; move: (Num.sqrt pi) => sp; move: pi0; move: (pi) => p p0.
  have pn0 : p != 0 by rewrite gt_eqF.
  have qn0 : q != 0 by rewrite gt_eqF.
  have rn0 : r != 0 by rewrite gt_eqF.
  have ln0 : lambda != 0 by rewrite gt_eqF.
  have wn0 : w != 0 by rewrite gt_eqF.
  by field.
have RE : 2 * pi ^+ 2 * Num.sqrt pi * (L + s) / (lambda * w) =
    K * (2 * (L + s)).
  rewrite /K; move: (Num.sqrt pi) => sp.
  have ln0 : lambda != 0 by rewrite gt_eqF.
  have wn0 : w != 0 by rewrite gt_eqF.
  by field.
rewrite LE RE; apply: ler_wpM2l => //.
have q2' : q <= 2 by have := q0; nra.
rewrite /r; nra.
Qed.

End conc_fun_sum.

