From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences derive realfun exp.
From mathcomp Require Import measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.comparison Require Import gauss_linear gauss_smoothing.
From GaussianAnalysis.comparison Require Import gauss_law ornstein_uhlenbeck.

(**md**************************************************************************)
(* # The Gaussian Brascamp-Lieb inequality for bounded functions              *)
(*                                                                            *)
(* Ball's geometric form of the Brascamp-Lieb inequality, for the standard    *)
(* Gaussian measure and bounded functions. Let u_1, ..., u_n be unit vectors  *)
(* of 'rV[R]_m and c_1, ..., c_n positive weights such that                   *)
(* sum_i c_i u_i^T u_i is the identity matrix of size m: the vectors          *)
(* sqrt (c_i) u_i form a tight frame. For measurable f_1, ..., f_n with       *)
(* values in [delta, K], 0 < delta (gauss_brascamp_lieb_bounded),             *)
(*                                                                            *)
(*   int prod_i f_i(<x, u_i>)^{c_i} dgauss_m(x)                               *)
(*     <= prod_i (int f_i d(normal_prob 0 1))^{c_i},                          *)
(*                                                                            *)
(* with real integrals and powR. The extension to f_i with values in [0, K]   *)
(* (gauss_brascamp_lieb_ge0) and to measurable F_i : R -> [0, +oo]            *)
(* (gauss_brascamp_lieb), and the form with Lebesgue measures                 *)
(* (brascamp_lieb), are derived from this theorem in                          *)
(* brascamp_lieb_lebesgue.v.                                                  *)
(*                                                                            *)
(* The proof uses the Mehler transform of ornstein_uhlenbeck.v. For           *)
(* 0 <= r <= 1 let                                                            *)
(*                                                                            *)
(*   Lambda(r) = int G_r(x) dgauss_m(x),                                      *)
(*   G_r(x) = exp (sum_i c_i ln (mehler r f_i)(<x, u_i>)).                    *)
(*                                                                            *)
(* Since mehler 1 f = f and mehler 0 f is the mean of f, Lambda(1) is the     *)
(* left side and Lambda(0) the right side. For 0 < r < 1, Lambda is           *)
(* differentiable under the integral. The generator identity                  *)
(* r d/dr mehler r f = x (mehler r f)' - (mehler r f)'' and Gaussian          *)
(* integration by parts along each u_i (gauss_ibp_unit) give                  *)
(*                                                                            *)
(*   r Lambda'(r) = int (|V(x)|^2 - sum_i c_i a_i(x)^2) G_r(x) dgauss_m(x),   *)
(*                                                                            *)
(* where a_i(x) is the derivative of ln (mehler r f_i) at <x, u_i> and        *)
(* V(x) = sum_i c_i a_i(x) u_i. This is nonpositive by a weighted             *)
(* Cauchy-Schwarz inequality for tight frames (tight_frame_cauchy_schwarz).   *)
(* Lambda is continuous at 1 from the left, since mehler r f_i tends to f_i   *)
(* in L^1 of the standard normal law (mehler_cvg_L1), and the mean value      *)
(* theorem gives Lambda(1) <= Lambda(0).                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section tight_frame.
Context {R : realType} (m n : nat) (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R).
Hypothesis u1 : forall i, mxdot (u i) (u i) = 1.
Hypothesis frame : \sum_i c i *: ((u i)^T *m u i) = 1%:M.

Let mxdot_tr_mul (v w : 'rV[R]_m) i :
  \tr (v *m ((u i)^T *m u i) *m w^T) = mxdot v (u i) * mxdot (u i) w.
Proof.
rewrite !mulmxA -mulmxA [v *m _]mx11_scalar [u i *m _]mx11_scalar.
by rewrite -scalar_mxM mxtrace_scalar mulr1n -!mxdot_rowE.
Qed.

(* The frame condition, in the form sum_i c_i <v, u_i> <u_i, w> = <v, w>. *)
Lemma tight_frame_mxdot (v w : 'rV[R]_m) :
  \sum_i c i * (mxdot v (u i) * mxdot (u i) w) = mxdot v w.
Proof.
rewrite mxdot_trace -[v in RHS]mulmx1 -frame mulmx_sumr mulmx_suml raddf_sum /=.
apply: eq_bigr => i _.
by rewrite -scalemxAr -scalemxAl mxtraceZ mxdot_tr_mul.
Qed.

Lemma tight_frame_mxdot_sqr (v : 'rV[R]_m) :
  \sum_i c i * mxdot v (u i) ^+ 2 = mxdot v v.
Proof.
rewrite -tight_frame_mxdot; apply: eq_bigr => i _.
by rewrite expr2 (mxdotC (u i) v).
Qed.

(* Taking the trace of the frame condition: sum_i c_i = m. *)
Lemma tight_frame_sum : \sum_i c i = m%:R.
Proof.
rewrite -mxtrace1 -frame raddf_sum /=; apply: eq_bigr => i _.
by rewrite mxtraceZ mxtrace_mulC -mxdot_trace u1 mulr1.
Qed.

(* A weighted Cauchy-Schwarz inequality: for the vector
   V = sum_i c_i a_i u_i, |V|^2 <= sum_i c_i a_i^2. *)
Lemma tight_frame_cauchy_schwarz (a : 'I_n -> R) : (forall i, 0 <= c i) ->
  mxdot (\sum_i (c i * a i) *: u i) (\sum_i (c i * a i) *: u i) <=
  \sum_i c i * a i ^+ 2.
Proof.
move=> c0; set V := \sum_i (c i * a i) *: u i.
have A0 : 0 <= \sum_i c i * a i ^+ 2.
  by apply: sumr_ge0 => i _; rewrite mulr_ge0// sqr_ge0.
have VV : mxdot V V = \sum_i (Num.sqrt (c i) * a i) *
    (Num.sqrt (c i) * mxdot (u i) V).
  rewrite {1}/V mxdot_suml; apply: eq_bigr => i _.
  by rewrite mxdotZl mulrACA -expr2 sqr_sqrtr// mulrA.
have VV2 : mxdot V V = \sum_i (Num.sqrt (c i) * mxdot (u i) V) *
    (Num.sqrt (c i) * mxdot (u i) V).
  rewrite -[LHS]tight_frame_mxdot_sqr; apply: eq_bigr => i _.
  by rewrite mulrACA -expr2 sqr_sqrtr// (mxdotC (u i)) expr2.
have AA : \sum_i c i * a i ^+ 2 =
    \sum_i (Num.sqrt (c i) * a i) * (Num.sqrt (c i) * a i).
  by apply: eq_bigr => i _; rewrite mulrACA -!expr2 sqr_sqrtr.
have cs := sum_cauchy_schwarz (fun i => Num.sqrt (c i) * a i)
  (fun i => Num.sqrt (c i) * mxdot (u i) V).
rewrite -VV -AA -VV2 in cs.
have [V0|V0] := eqVneq (mxdot V V) 0; first by rewrite V0.
have Vp : 0 < mxdot V V by rewrite lt_def V0 mxdot_ge0.
by rewrite -(ler_pM2r Vp) -expr2.
Qed.

End tight_frame.

Section gauss_ibp_unit.
Context {R : realType}.

(* Gaussian integration by parts along a unit vector u:
   E[<x, u> F(x)] = E[d_u F(x)] for x of law gauss m, F and its derivative
   along u bounded and measurable, the derivative continuous along the lines
   parallel to u. The proof moves u to the first basis vector with a
   Householder reflection. *)
Theorem gauss_ibp_unit m (u : 'rV[R]_m) (F dF : 'rV[R]_m -> R) (C : R) :
  mxdot u u = 1 -> (forall x, is_derive x u F (dF x)) ->
  measurable_fun [set: 'rV[R]_m] F -> measurable_fun [set: 'rV[R]_m] dF ->
  (forall x, continuous (fun t : R => dF (t *: u + x))) ->
  (forall x, `|F x| <= C) -> (forall x, `|dF x| <= C) ->
  (\int[gauss m]_x (mxdot x u * F x)%:E = \int[gauss m]_x (dF x)%:E)%E.
Proof.
case: m u F dF => [|m] u F dF u1 dF_ mF mdF cdF FC dFC.
  have u0 : u = 0 by apply/rowP => -[].
  by move: u1; rewrite u0 mxdot0l => /eqP; rewrite eq_sym oner_eq0.
have C0 : 0 <= C := le_trans (normr_ge0 _) (FC 0).
pose e : 'rV[R]_m.+1 := delta_mx 0 0.
have e1 : mxdot e e = 1 by rewrite mxdot_delta mxE !eqxx.
pose Q := householder (e^T - u^T).
have QT : Q^T = Q := householder_tr _.
have Qo : Q \is orthogonalmx := householder_orthogonal _.
have Qe : Q *m e^T = u^T.
  by apply: householder_swap; rewrite !mxdot_trmx e1 u1.
have eQ : e *m Q = u by rewrite -[e *m Q]trmxK trmx_mul QT Qe trmxK.
have QQ : Q^T *m Q = 1%:M := orthogonalmxT Qo.
have mQ : measurable_fun [set: 'rV[R]_m.+1] (fun y : 'rV[R]_m.+1 => y *m Q).
  by apply: measurable_mulmx => //; exact: measurable_cst.
have xu x : `|mxdot x u| <= ((1 * m.+1)%:R) * `|x|.
  rewrite (le_trans (mxdot_le _ _))// /frobenius u1 sqrtr1 mulr1.
  exact: frobenius_le_mx_norm.
have iF1 : (gauss m.+1).-integrable [set: 'rV[R]_m.+1]
    (EFin \o (fun x => mxdot x u * F x)).
  apply: (@integrable_gauss_poly _ _ _ (C * (1 * m.+1)%:R) 1).
    by apply: measurable_funM => //; exact: measurable_mxdot.
  move=> x; rewrite normrM expr1 mulrC (le_trans (ler_pM _ _ (FC x) (xu x)))//.
  by rewrite mulrA ler_wpM2l ?mulr_ge0// lerDr.
have iF2 : (gauss m.+1).-integrable [set: 'rV[R]_m.+1] (EFin \o dF).
  exact: integrable_gauss_bounded mdF dFC.
rewrite -(integral_gauss_orthogonal QQ iF1) -(integral_gauss_orthogonal QQ iF2).
transitivity (\int[gauss m.+1]_y (y 0 0 * F (y *m Q))%:E)%E.
  apply: eq_integral => y _; congr ((_ * _)%:E).
  by rewrite -eQ mxdot_orthogonalmxr// mxdot_delta.
apply: (@gauss_ibp_line _ m.+1 0 (fun y => F (y *m Q)) (fun y => dF (y *m Q))
  C 0).
- move=> y; apply: (is_derive_transfer (G := F) (b := y *m Q) (w := u)) => // h.
  by rewrite mulmxDl -scalemxAl eQ.
- exact: measurableT_comp mF mQ.
- exact: measurableT_comp mdF mQ.
- move=> y; have -> : (fun t : R => dF ((t *: e + y) *m Q)) =
      (fun t => dF (t *: u + y *m Q)).
    by apply/funext => t; rewrite mulmxDl -scalemxAl eQ.
  exact: cdF.
- by move=> y; rewrite expr0 (le_trans (FC _))// ler_peMr// lerDl.
- by move=> y; rewrite expr0 (le_trans (dFC _))// ler_peMr// lerDl.
Qed.

End gauss_ibp_unit.

Section directional.
Context {R : realType} {V : normedModType R}.

(* The chain rule along a direction v, for a real function of a function
   on V. *)
Lemma is_derive_comp_dir (phi : R -> R) (S : V -> R) (x v : V) (dphi dS : R) :
  is_derive (S x) 1 phi dphi -> is_derive x v S dS ->
  is_derive x v (fun y => phi (S y)) (dphi * dS).
Proof.
move=> hphi hS.
have hS1 : is_derive (0 : R) (1 : R) (fun t : R => S (t *: v + x)) dS.
  apply: (is_derive_transfer (G := S) (b := x) (w := v)) => // t.
  by rewrite addr0 [t *: 1]mulr1.
have hphi' : is_derive ((fun t : R => S (t *: v + x)) 0) (1 : R) phi dphi.
  by rewrite /= scale0r add0r.
have h := is_derive1_comp hphi' hS1.
apply: (is_derive_transfer (G := phi \o (fun t : R => S (t *: v + x)))
  (b := 0) (w := 1)) => // t.
by rewrite /= addr0 [t *: 1]mulr1.
Qed.

End directional.

Section mxdot_derive.
Context {R : realType} (k : nat).
Implicit Types x v w : 'rV[R]_k.

Lemma is_derive_mxdot x v w : is_derive x v (fun y => mxdot y w) (mxdot v w).
Proof.
have h : is_derive (0 : R) (1 : R) (fun t : R => mxdot x w + t * mxdot v w)
    (mxdot v w).
  apply: (@is_derive_cubicE _ _ (mxdot x w) (mxdot v w) 0 0) => [t|]; ring.
apply: (is_derive_transfer (G := fun t : R => mxdot x w + t * mxdot v w)
  (b := 0) (w := 1)) => // t.
by rewrite mxdotDl mxdotZl addr0 [t *: 1]mulr1 addrC.
Qed.

Lemma is_derive_mxdot_comp (phi : R -> R) (dphi : R) x v w :
  is_derive (mxdot x w) 1 phi dphi ->
  is_derive x v (fun y => phi (mxdot y w)) (dphi * mxdot v w).
Proof.
move=> h; have h2 := @is_derive_comp_dir R _ phi (fun y => mxdot y w) x v dphi
  (mxdot v w) h (is_derive_mxdot x v w).
exact: h2.
Qed.

Lemma continuous_mxdot_line (phi : R -> R) x v w : continuous phi ->
  continuous (fun t : R => phi (mxdot (t *: v + x) w)).
Proof.
move=> cphi t; have -> : (fun t : R => phi (mxdot (t *: v + x) w)) =
    phi \o (fun t => t * mxdot v w + mxdot x w).
  by apply/funext => s; rewrite /= mxdotDl mxdotZl.
apply: continuous_comp; last exact: cphi.
apply: cvgD; last exact: cvg_cst.
by apply: cvgM; [exact: cvg_id|exact: cvg_cst].
Qed.

Lemma mxdot_unit_le1 (v w : 'rV[R]_k) : mxdot v v = 1 -> mxdot w w = 1 ->
  `|mxdot v w| <= 1.
Proof.
move=> v1 w1; rewrite (le_trans (mxdot_le _ _))//.
by rewrite /frobenius v1 w1 sqrtr1 mulr1.
Qed.

Lemma mxdot_le_mx_norm (x w : 'rV[R]_k) : mxdot w w = 1 ->
  `|mxdot x w| <= (1 * k)%:R * `|x|.
Proof.
move=> w1; rewrite (le_trans (mxdot_le _ _))// /frobenius w1 sqrtr1 mulr1.
exact: frobenius_le_mx_norm.
Qed.

End mxdot_derive.

Section integrable_Rsum.
Context d {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}).

Lemma integrable_Rsum (I : Type) (s : seq I) (h : I -> T -> R) :
  (forall i, mu.-integrable [set: T] (EFin \o h i)) ->
  mu.-integrable [set: T] (EFin \o (fun x => \sum_(i <- s) h i x)).
Proof.
move=> hi.
have := @integrable_sum _ _ _ mu _ measurableT _ s xpredT _ (fun j _ => hi j).
by apply: (eq_integrable measurableT) => x _; rewrite /= sumEFin.
Qed.

End integrable_Rsum.

Section gauss_brascamp_lieb_bounded.
Context {R : realType} (m n : nat) (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R).
Hypothesis u1 : forall i, mxdot (u i) (u i) = 1.
Hypothesis c0 : forall i, 0 < c i.
Hypothesis frame : \sum_i c i *: ((u i)^T *m u i) = 1%:M.
Variables (f : 'I_n -> R -> R) (delta K : R).
Hypothesis delta0 : 0 < delta.
Hypothesis deltaK : delta <= K.
Hypothesis mf : forall i, measurable_fun [set: R] (f i).
Hypothesis fb : forall i y, delta <= f i y <= K.
Local Notation N := (@normal_prob R 0 1).

Let K0 : 0 < K := lt_le_trans delta0 deltaK.

Let fK i y : `|f i y| <= K.
Proof.
by have /andP[h1 h2] := fb i y; rewrite ger0_norm// (le_trans _ h1) ?ltW.
Qed.

Let g r i := mehler r (f i).

Let gb r i y : delta <= g r i y <= K.
Proof.
apply/andP; split; last by have := mehler_le r y (mf i) (fK i);
  rewrite ler_norml => /andP[].
by apply: (mehler_ge r y (mf i) (fK i)) => z; case/andP: (fb i z).
Qed.

Let g_gt0 r i y : 0 < g r i y.
Proof. by have /andP[h _] := gb r i y; exact: lt_le_trans delta0 h. Qed.

(* The integrand of Lambda, prod_i (mehler r f_i)(<x, u_i>)^{c_i}. *)
Let G r (x : 'rV[R]_m) := expR (\sum_i c i * ln (g r i (mxdot x (u i)))).

Let GK := expR ((\sum_i c i) * ln K).

Let G_gt0 r x : 0 < G r x := expR_gt0 _.

Let G_le r x : G r x <= GK.
Proof.
rewrite /G /GK ler_expR mulr_suml; apply: ler_sum => i _.
apply: ler_wpM2l; first exact: ltW.
by rewrite ler_ln ?posrE//; case/andP: (gb r i (mxdot x (u i))).
Qed.

Let G_norm r x : `|G r x| <= GK.
Proof. by rewrite gtr0_norm. Qed.

Let measurable_G r : `|r| < 1 \/ r = 1 -> measurable_fun [set: 'rV[R]_m] (G r).
Proof.
move=> r1; apply: measurableT_comp => //; apply: measurable_sum => i.
apply: measurable_funM => //; apply: measurableT_comp => //.
apply: measurableT_comp; last exact: measurable_mxdot.
case: r1 => [r1|->]; first exact: measurable_mehler (mf i) (fK i) r1.
by have -> : g 1 i = f i by apply/funext => y; rewrite /g mehler1.
Qed.

Let integrable_G r : `|r| < 1 \/ r = 1 ->
  (gauss m).-integrable [set: 'rV[R]_m] (EFin \o G r).
Proof.
by move=> r1; exact: integrable_gauss_bounded (measurable_G r1) (G_norm r).
Qed.

Let Lambda r := \int[gauss m]_x G r x.

Let Lambda1 :
  Lambda 1 = \int[gauss m]_x expR (\sum_i c i * ln (f i (mxdot x (u i)))).
Proof.
by apply: eq_Rintegral => x _; rewrite /G /g;
  under eq_bigr do rewrite mehler1.
Qed.

Let Lambda0 : Lambda 0 = expR (\sum_i c i * ln (\int[N]_y f i y)).
Proof.
rewrite /Lambda /G /g; under eq_Rintegral do under eq_bigr do rewrite mehler0.
by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
Qed.

Let sumc0 : 0 <= \sum_i c i := sumr_ge0 _ (fun i _ => ltW (c0 i)).

(* The derivative of r |-> G r x. *)
Let dG r x := G r x * \sum_i c i *
  (mehler_dr r (f i) (mxdot x (u i)) / g r i (mxdot x (u i))).

Let is_derive_G r x : `|r| < 1 -> is_derive r (1 : R) (G ^~ x) (dG r x).
Proof.
move=> r1.
have hS : is_derive r (1 : R)
    (fun r => \sum_i c i * ln (g r i (mxdot x (u i))))
    (\sum_i c i * ((g r i (mxdot x (u i)))^-1 *
       mehler_dr r (f i) (mxdot x (u i)))).
  have -> : (fun r => \sum_i c i * ln (g r i (mxdot x (u i)))) =
      \sum_i (fun r => c i * ln (g r i (mxdot x (u i)))).
    by apply/funext => t; rewrite fct_sumE.
  apply: is_derive_sum => i.
  have h := is_derive1_comp (g := fun r => g r i (mxdot x (u i))) (x := r)
    (is_derive1_ln (g_gt0 r i (mxdot x (u i))))
    (is_derive_mehler_r (mxdot x (u i)) (mf i) (fK i) r1).
  exact: (is_deriveZ (c i) h).
have h := is_derive1_comp (is_derive_expR _) hS.
apply: (is_derive_eq h); rewrite /dG /G; congr (_ * _).
by under eq_bigr do rewrite [_^-1 * _]mulrC.
Qed.

Let m1 : R := \int[N]_z `|z : R|.
Let m2 : R := \int[N]_z `|(z : R) ^+ 2 - 1|.
Let m10 : 0 <= m1. Proof. by apply: Rintegral_ge0 => z _. Qed.
Let m20 : 0 <= m2. Proof. by apply: Rintegral_ge0 => z _. Qed.

Let is_derive_Lambda r : `|r| < 1 ->
  is_derive r (1 : R) Lambda (\int[gauss m]_x dG r x).
Proof.
move=> r1.
pose e := (1 - `|r|) / 2; pose r2 := (1 + `|r|) / 2.
have e0 : 0 < e by rewrite /e divr_gt0// subr_gt0.
have r20 : 0 <= r2 by rewrite /r2 divr_ge0// addr_ge0.
have r21 : r2 < 1 by rewrite /r2 ltr_pdivrMr// mul1r; lra.
have w2 : 0 < 1 - r2 ^+ 2 by nra.
have b2 : 0 < Num.sqrt (1 - r2 ^+ 2) by rewrite sqrtr_gt0.
have rI : r \in `]r - e, r + e[ by rewrite in_itv /=; apply/andP; split; lra.
have Ib r' : r' \in `]r - e, r + e[ -> `|r'| <= r2.
  rewrite in_itv /= => /andP[h1 h2].
  have h : `|r' - r| <= e by rewrite ler_norml; apply/andP; split; lra.
  have := ler_normD (r' - r) r; rewrite subrK => hn.
  by move: h; rewrite /r2 /e; lra.
have I1 r' : r' \in `]r - e, r + e[ -> `|r'| < 1.
  by move=> /Ib h; exact: le_lt_trans h r21.
pose A := GK / delta * ((\sum_i c i) * (K * m2 / (1 - r2 ^+ 2))).
pose B := GK / delta * ((\sum_i c i) * ((1 * m)%:R * (K * m1) /
  Num.sqrt (1 - r2 ^+ 2))).
have GKd : 0 <= GK / delta by rewrite divr_ge0 ?expR_ge0// ltW.
have A0 : 0 <= A.
  apply: mulr_ge0 => //; apply: mulr_ge0 => //;
    apply: divr_ge0; last exact: ltW.
  by apply: mulr_ge0; [exact: ltW|exact: m20].
have B0 : 0 <= B.
  apply: mulr_ge0 => //; apply: mulr_ge0 => //;
    apply: divr_ge0; last exact: ltW.
  by apply: mulr_ge0 => //; apply: mulr_ge0; [exact: ltW|exact: m10].
pose D (x : 'rV[R]_m) := A + B * `|x|.
have D0 x : 0 <= D x by rewrite /D addr_ge0// mulr_ge0.
have mD : measurable_fun [set: 'rV[R]_m] D.
  apply: measurable_funD => //; apply: measurable_funM => //.
  exact: continuous_measurable_mx norm_continuous.
have Di : (gauss m).-integrable [set: 'rV[R]_m] (EFin \o D).
  apply: (@integrable_gauss_poly _ _ _ (A + B) 1) => // x.
  rewrite ger0_norm// /D expr1 mulrDr mulr1; apply: lerD;
    first by rewrite lerDl.
  by rewrite ler_wpM2r// lerDr.
pose P := (1 * m)%:R * (K * m1) / Num.sqrt (1 - r2 ^+ 2).
pose Q := K * m2 / (1 - r2 ^+ 2).
have P0 : 0 <= P.
  by apply: divr_ge0; [apply: mulr_ge0 => //; apply: mulr_ge0; [exact: ltW|]|
    exact: ltW].
have Q0 : 0 <= Q.
  by apply: divr_ge0; [apply: mulr_ge0; [exact: ltW|]|exact: ltW].
have hdr r' x i : r' \in `]r - e, r + e[ ->
    `|mehler_dr r' (f i) (mxdot x (u i))| <= P * `|x| + Q.
  move=> r'I; have r'1 := I1 _ r'I; have r'2 := Ib _ r'I.
  have w' : 1 - r2 ^+ 2 <= 1 - r' ^+ 2.
    have : r' ^+ 2 <= r2 ^+ 2.
      by rewrite -[r' ^+ 2]real_normK ?num_real// lerXn2r// ?nnegrE.
    lra.
  have w'0 : 0 < 1 - r' ^+ 2 := lt_le_trans w2 w'.
  have b' : Num.sqrt (1 - r2 ^+ 2) <= Num.sqrt (1 - r' ^+ 2).
    by rewrite ler_sqrt// ltW.
  have hs : `|mxdot x (u i)| <= (1 * m)%:R * `|x| := mxdot_le_mx_norm x (u1 i).
  have hb : (Num.sqrt (1 - r' ^+ 2))^-1 <= (Num.sqrt (1 - r2 ^+ 2))^-1.
    by rewrite lef_pV2 ?posrE ?sqrtr_gt0.
  have hw : (1 - r' ^+ 2)^-1 <= (1 - r2 ^+ 2)^-1 by rewrite lef_pV2 ?posrE.
  have Km1 : 0 <= K * m1 by rewrite mulr_ge0// ltW.
  have Km2 : 0 <= K * m2 by rewrite mulr_ge0// ltW.
  apply: (le_trans (mehler_dr_le _ (mf i) (fK i) r'1)); apply: lerD.
    apply: (@le_trans _ _ ((1 * m)%:R * `|x| / Num.sqrt (1 - r2 ^+ 2) *
        (K * m1))).
      by rewrite ler_wpM2r//; apply: ler_pM.
    by rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite /P; ring.
  apply: (@le_trans _ _ ((1 - r2 ^+ 2)^-1 * (K * m2))); last first.
    by rewrite /Q mulrC.
  rewrite ler_wpM2r// -[X in _ <= X]mul1r; apply: ler_pM => //.
    by rewrite invr_ge0 ltW.
  by rewrite (le_trans r'2) ?ltW.
apply: (@is_derive_Rintegral _ _ _ (gauss m) G dG D (r - e) (r + e) r rI).
- by move=> r' r'I; apply: integrable_G; left; exact: I1.
- by move=> r' x r'I; exact: is_derive_G (I1 _ r'I).
- exact: D0.
- exact: Di.
- move=> r' x r'I; rewrite /dG normrM (gtr0_norm (G_gt0 _ _)).
  apply: (le_trans (ler_pM (ltW (G_gt0 _ _)) (normr_ge0 _) (G_le r' x)
    (ler_norm_sum _ _ _))).
  apply: (@le_trans _ _ (GK * ((\sum_i c i) * (P * `|x| + Q) / delta))).
    apply: ler_wpM2l; first exact: expR_ge0.
    have -> : (\sum_i c i) * (P * `|x| + Q) / delta =
        \sum_i c i * ((P * `|x| + Q) / delta) by rewrite -mulrA mulr_suml.
    apply: ler_sum => i _.
    rewrite normrM (gtr0_norm (c0 i)) ler_wpM2l ?(ltW (c0 i))//.
    rewrite normf_div (gtr0_norm (g_gt0 _ _ _)).
    have gi : delta <= g r' i (mxdot x (u i)).
      by case/andP: (gb r' i (mxdot x (u i))).
    apply: ler_pM => //; first by rewrite invr_ge0 ltW// g_gt0.
      exact: (hdr _ _ _ r'I).
    by rewrite lef_pV2 ?posrE// g_gt0.
  have d0 : delta != 0 := lt0r_neq0 delta0.
  have b20 : Num.sqrt (1 - r2 ^+ 2) != 0 := lt0r_neq0 b2.
  have w20 : 1 - r2 ^+ 2 != 0 := lt0r_neq0 w2.
  have -> : D x = GK * ((\sum_i c i) * (P * `|x| + Q) / delta).
    by rewrite /D /A /B /P /Q; field.
  exact: lexx.
Qed.

Section derivative_sign.
Variable r : R.
Hypothesis r0 : 0 < r.
Hypothesis r1 : r < 1.

Let r1' : `|r| < 1. Proof. by rewrite gtr0_norm. Qed.
Let w0 : 0 < 1 - r ^+ 2 := onem_sqr_gt0 r1'.
Let b0 : 0 < Num.sqrt (1 - r ^+ 2). Proof. by rewrite sqrtr_gt0. Qed.

Let g1 i := mehler_d1 r (f i).
Let g2 i := mehler_d2 r (f i).
Let a i y := g1 i y / g r i y.
Let a' i y := g2 i y / g r i y - a i y ^+ 2.

Let C1 := `|r| / Num.sqrt (1 - r ^+ 2) * (K * m1).
Let C2 := r ^+ 2 / (1 - r ^+ 2) * (K * m2).
Let C10 : 0 <= C1.
Proof. by apply: mulr_ge0; [rewrite divr_ge0// ltW|rewrite mulr_ge0// ltW]. Qed.
Let C20 : 0 <= C2.
Proof.
by apply: mulr_ge0; [rewrite divr_ge0 ?sqr_ge0// ltW|rewrite mulr_ge0// ltW].
Qed.

Let g_ge i y : delta <= g r i y. Proof. by case/andP: (gb r i y). Qed.

Let invg_le i y : `|(g r i y)^-1| <= delta^-1.
Proof.
have gp := g_gt0 r i y.
rewrite ger0_norm; first by rewrite invr_ge0 ltW.
by rewrite lef_pV2 ?posrE.
Qed.

Let a_le i y : `|a i y| <= C1 / delta.
Proof.
rewrite /a normrM; apply: ler_pM => //.
exact: (mehler_d1_le y (mf i) (fK i) r1').
Qed.

Let a'_le i y : `|a' i y| <= C2 / delta + (C1 / delta) ^+ 2.
Proof.
rewrite /a' (le_trans (ler_normB _ _))//; apply: lerD.
  rewrite normrM; apply: ler_pM => //.
  exact: (mehler_d2_le y (mf i) (fK i) r1').
by rewrite normrX lerXn2r// ?nnegrE ?divr_ge0// ltW.
Qed.

Let is_derive_g i (y : R) : is_derive y 1 (g r i) (g1 i y) :=
  is_derive_mehler y (mf i) (fK i) r1'.

Let is_derive_g1 i (y : R) : is_derive y 1 (g1 i) (g2 i y) :=
  is_derive_mehler_d1 y (mf i) (fK i) r1'.

Let is_derive_a i (y : R) : is_derive y 1 (a i) (a' i y).
Proof.
have gn : g r i y != 0 := lt0r_neq0 (g_gt0 r i y).
have h := is_deriveM (is_derive_g1 i y)
  (is_deriveV (f := g r i) gn (is_derive_g i y)).
apply: (is_derive_eq h); rewrite /a' /a /GRing.scale /=.
by field.
Qed.

Let is_derive_lng i (y : R) : is_derive y 1 (fun y => ln (g r i y)) (a i y).
Proof.
have h := is_derive1_comp (g := g r i) (x := y)
  (is_derive1_ln (g_gt0 r i y)) (is_derive_g i y).
by apply: (is_derive_eq h); rewrite /a mulrC.
Qed.

Let derive_cont (h dh : R -> R) : (forall y : R, is_derive y 1 h (dh y)) ->
  continuous h.
Proof.
move=> dh_ y; apply: differentiable_continuous; apply/derivable1_diffP.
exact: (@ex_derive _ _ _ _ _ _ _ (dh_ y)).
Qed.

Let cg i : continuous (g r i) := derive_cont (is_derive_g i).
Let cg1 i : continuous (g1 i) := derive_cont (is_derive_g1 i).
Let cg2 i : continuous (g2 i) := continuous_mehler_d2 (mf i) (fK i) r1'.
Let ca i : continuous (a i) := derive_cont (is_derive_a i).
Let clng i : continuous (fun y => ln (g r i y)) :=
  derive_cont (is_derive_lng i).
Let ca' i : continuous (a' i).
Proof.
move=> y; apply: cvgB; last by apply: cvgM; [exact: ca|exact: ca].
apply: cvgM; first exact: cg2.
by apply: cvgV; [exact: lt0r_neq0 (g_gt0 r i y)|exact: cg].
Qed.

Let F i (x : 'rV[R]_m) := a i (mxdot x (u i)) * G r x.
Let Sd i (x : 'rV[R]_m) :=
  \sum_j c j * (a j (mxdot x (u j)) * mxdot (u i) (u j)).
Let dF i (x : 'rV[R]_m) :=
  (a' i (mxdot x (u i)) + a i (mxdot x (u i)) * Sd i x) * G r x.

Let is_derive_G_dir i (x : 'rV[R]_m) :
  is_derive x (u i) (G r) (G r x * Sd i x).
Proof.
have hS : is_derive x (u i)
    (fun x => \sum_j c j * ln (g r j (mxdot x (u j)))) (Sd i x).
  have -> : (fun x => \sum_j c j * ln (g r j (mxdot x (u j)))) =
      \sum_j (fun x => c j * ln (g r j (mxdot x (u j)))).
    by apply/funext => y; rewrite fct_sumE.
  rewrite /Sd; apply: is_derive_sum => j.
  have h := @is_derive_mxdot_comp _ _ (fun y => ln (g r j y)) _ x (u i) (u j)
    (is_derive_lng j (mxdot x (u j))).
  exact: (is_deriveZ (c j) h).
have h := @is_derive_comp_dir _ _ expR
  (fun x => \sum_j c j * ln (g r j (mxdot x (u j)))) x (u i) _ _
  (is_derive_expR _) hS.
by apply: (is_derive_eq h); rewrite mulrC.
Qed.

Let is_derive_F i (x : 'rV[R]_m) : is_derive x (u i) (F i) (dF i x).
Proof.
have ha := @is_derive_mxdot_comp _ _ (a i) _ x (u i) (u i)
  (is_derive_a i (mxdot x (u i))).
have h := is_deriveM ha (is_derive_G_dir i x).
by apply: (is_derive_eq h); rewrite /dF /GRing.scale /= (u1 i); ring.
Qed.

Let mline (phi : R -> R) j : continuous phi ->
  measurable_fun [set: 'rV[R]_m] (fun x => phi (mxdot x (u j))).
Proof.
move=> cphi.
exact: measurableT_comp (continuous_measurable_fun cphi)
  (measurable_mxdot (u j)).
Qed.

Let mG : measurable_fun [set: 'rV[R]_m] (G r) := measurable_G (or_introl r1').

Let mF i : measurable_fun [set: 'rV[R]_m] (F i).
Proof. by apply: measurable_funM => //; exact: (@mline (a i) i (@ca i)). Qed.

Let mSd i : measurable_fun [set: 'rV[R]_m] (Sd i).
Proof.
apply: measurable_sum => j; apply: measurable_funM => //.
by apply: measurable_funM => //; exact: (@mline (a j) j (@ca j)).
Qed.

Let mdF i : measurable_fun [set: 'rV[R]_m] (dF i).
Proof.
apply: measurable_funM => //; apply: measurable_funD.
  exact: (@mline (a' i) i (@ca' i)).
by apply: measurable_funM => //; exact: (@mline (a i) i (@ca i)).
Qed.

Let cdF i (x : 'rV[R]_m) : continuous (fun t : R => dF i (t *: u i + x)).
Proof.
have cSd : continuous (fun t : R => Sd i (t *: u i + x)).
  rewrite /Sd; apply: continuous_sum => j t'.
  apply: cvgM; first exact: cvg_cst.
  apply: cvgM; last exact: cvg_cst.
  exact: (continuous_mxdot_line (@ca j)).
have cG : continuous (fun t : R => G r (t *: u i + x)).
  apply: (@derive_cont _ (fun t => G r (t *: u i + x) * Sd i (t *: u i + x)))
    => t.
  apply: (is_derive_transfer (G := G r) (b := t *: u i + x) (w := u i)).
    by move=> h; rewrite [h *: 1]mulr1 scalerDl addrA.
  exact: is_derive_G_dir.
move=> t; apply: cvgM; last exact: cG.
apply: cvgD; first exact: (continuous_mxdot_line (@ca' i)).
apply: cvgM; last exact: cSd.
exact: (continuous_mxdot_line (@ca i)).
Qed.

Let Sd_le i x : `|Sd i x| <= (\sum_j c j) * (C1 / delta).
Proof.
rewrite /Sd (le_trans (ler_norm_sum _ _ _))// mulr_suml; apply: ler_sum => j _.
rewrite normrM (gtr0_norm (c0 j)) ler_wpM2l ?(ltW (c0 j))// normrM.
rewrite -[X in _ <= X]mulr1; apply: ler_pM => //.
exact: mxdot_unit_le1 (u1 i) (u1 j).
Qed.

Let Ca := C1 / delta.
Let Ca0 : 0 <= Ca. Proof. by rewrite divr_ge0// ltW. Qed.
Let CF := (C2 / delta + Ca ^+ 2 + Ca * ((\sum_j c j) * Ca) + Ca) * GK.

Let F_le i x : `|F i x| <= CF.
Proof.
rewrite /F /CF normrM (gtr0_norm (G_gt0 _ _)).
apply: ler_pM => //; first exact: ltW (G_gt0 _ _).
apply: (le_trans (a_le _ _)); rewrite -/Ca lerDr.
have C2d : 0 <= C2 / delta by rewrite divr_ge0// ltW.
apply: addr_ge0; first by apply: addr_ge0 => //; exact: sqr_ge0.
by apply: mulr_ge0 => //; apply: mulr_ge0.
Qed.

Let dF_le i x : `|dF i x| <= CF.
Proof.
rewrite /dF /CF normrM (gtr0_norm (G_gt0 _ _)).
apply: ler_pM => //; first exact: ltW (G_gt0 _ _).
apply: (le_trans (ler_normD _ _)).
apply: (@le_trans _ _ (C2 / delta + Ca ^+ 2 + Ca * ((\sum_j c j) * Ca)));
  last by rewrite lerDl.
apply: lerD; first exact: a'_le.
by rewrite normrM; apply: ler_pM.
Qed.

Let ibp i : \int[gauss m]_x (mxdot x (u i) * F i x) = \int[gauss m]_x dF i x.
Proof.
rewrite /Rintegral; apply: congr1.
exact: (gauss_ibp_unit (u1 i) (@is_derive_F i) (@mF i) (@mdF i) (@cdF i)
  (@F_le i) (@dF_le i)).
Qed.

Let Gg i (x : 'rV[R]_m) :=
  G r x * (g2 i (mxdot x (u i)) / g r i (mxdot x (u i))).

(* The generator identity, integrated against prod_j g_j^c_j. *)
Let rdG x : r * dG r x =
  \sum_i c i * (mxdot x (u i) * F i x - Gg i x).
Proof.
rewrite /dG mulrCA mulr_sumr mulr_sumr; apply: eq_bigr => i _.
set y := mxdot x (u i).
have gen := mehler_generator y (mf i) (fK i) r1'.
have gn : g r i y != 0 := lt0r_neq0 (g_gt0 r i y).
transitivity (G r x * (c i * ((r * mehler_dr r (f i) y) / g r i y))).
  by rewrite /g; field.
by rewrite gen /F /Gg /a /g1 /g2 /g; field.
Qed.

(* The sign: sum_i c_i (dF_i - G g2_i / g_i) = G (|V|^2 - sum_i c_i a_i^2)
   <= 0 for V = sum_i c_i a_i u_i. *)
Let key x : \sum_i c i * (dF i x - Gg i x) <= 0.
Proof.
pose V := \sum_i (c i * a i (mxdot x (u i))) *: u i.
have VV : mxdot V V = \sum_i c i * a i (mxdot x (u i)) * Sd i x.
  rewrite /V mxdot_suml; apply: eq_bigr => i _.
  rewrite mxdotZl; congr (_ * _).
  rewrite mxdot_sumr /Sd; apply: eq_bigr => j _.
  by rewrite mxdotZr; ring.
have E : \sum_i c i * (dF i x - Gg i x) =
    G r x * (mxdot V V - \sum_i c i * a i (mxdot x (u i)) ^+ 2).
  rewrite VV -sumrB mulr_sumr; apply: eq_bigr => i _.
  have gn : g r i (mxdot x (u i)) != 0 := lt0r_neq0 (g_gt0 r i _).
  by rewrite /dF /Gg /a' /a; field.
rewrite E pmulr_rle0 ?G_gt0// subr_le0.
exact: (tight_frame_cauchy_schwarz frame (fun i => a i (mxdot x (u i)))
  (fun i => ltW (c0 i))).
Qed.

Local Lemma dLambda_le0 : \int[gauss m]_x dG r x <= 0.
Proof.
have C2d : 0 <= C2 / delta by rewrite divr_ge0// ltW.
have CF0 : 0 <= CF.
  apply: mulr_ge0; last exact: expR_ge0.
  apply: addr_ge0 => //; apply: addr_ge0.
    by apply: addr_ge0 => //; exact: sqr_ge0.
  by apply: mulr_ge0 => //; apply: mulr_ge0.
have cq i : continuous (fun y => g2 i y / g r i y).
  move=> y; apply: cvgM; first exact: cg2.
  by apply: cvgV; [exact: lt0r_neq0 (g_gt0 r i y)|exact: cg].
have mGg i : measurable_fun [set: 'rV[R]_m] (Gg i).
  apply: measurable_funM => //.
  exact: (@mline (fun y => g2 i y / g r i y) i (cq i)).
have iSF i : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => mxdot x (u i) * F i x)).
  apply: (@integrable_gauss_poly _ _ _ (CF * (1 * m)%:R) 1).
    by apply: measurable_funM => //; exact: measurable_mxdot.
  move=> x; rewrite normrM expr1 mulrC.
  apply: (le_trans (ler_pM _ _ (F_le i x) (mxdot_le_mx_norm x (u1 i)))) => //.
  rewrite mulrA; apply: ler_wpM2l; first exact: mulr_ge0.
  by rewrite lerDr.
have iGg i : (gauss m).-integrable [set: 'rV[R]_m] (EFin \o Gg i).
  apply: (integrable_gauss_bounded (C := GK * (C2 / delta))) => // x.
  rewrite /Gg normrM (gtr0_norm (G_gt0 _ _)).
  apply: ler_pM => //; first exact: ltW (G_gt0 _ _).
  rewrite normrM; apply: ler_pM => //.
  exact: (mehler_d2_le _ (mf i) (fK i) r1').
have idF i : (gauss m).-integrable [set: 'rV[R]_m] (EFin \o dF i).
  exact: integrable_gauss_bounded (@mdF i) (@dF_le i).
have ih1 i : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => c i * (mxdot x (u i) * F i x - Gg i x))).
  have := integrableZl measurableT (c i)
    (integrableB measurableT (iSF i) (iGg i)).
  by apply: (eq_integrable measurableT) => x _; rewrite /= -EFinB -EFinM.
have ih2 i : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => c i * (dF i x - Gg i x))).
  have := integrableZl measurableT (c i)
    (integrableB measurableT (idF i) (iGg i)).
  by apply: (eq_integrable measurableT) => x _; rewrite /= -EFinB -EFinM.
have E1 : \int[gauss m]_x dG r x =
    r^-1 * \int[gauss m]_x (\sum_i c i * (mxdot x (u i) * F i x - Gg i x)).
  have iS : (gauss m).-integrable [set: 'rV[R]_m]
      (EFin \o (fun x => \sum_i c i * (mxdot x (u i) * F i x - Gg i x))).
    exact: integrable_Rsum.
  rewrite -(RintegralZl _ measurableT iS).
  by apply: eq_Rintegral => x _; rewrite -rdG mulKf// gt_eqF.
have iD1 i : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => mxdot x (u i) * F i x - Gg i x)).
  have := integrableB measurableT (iSF i) (iGg i).
  by apply: (eq_integrable measurableT) => x _; rewrite /= EFinB.
have iD2 i : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => dF i x - Gg i x)).
  have := integrableB measurableT (idF i) (iGg i).
  by apply: (eq_integrable measurableT) => x _; rewrite /= EFinB.
have E2 : \int[gauss m]_x (\sum_i c i * (mxdot x (u i) * F i x - Gg i x)) =
    \int[gauss m]_x (\sum_i c i * (dF i x - Gg i x)).
  rewrite !Rintegral_sum//; apply: eq_bigr => i _.
  rewrite (RintegralZl _ measurableT (iD1 i))
    (RintegralZl _ measurableT (iD2 i)).
  congr (_ * _).
  by rewrite (RintegralB measurableT (iSF i) (iGg i))
    (RintegralB measurableT (idF i) (iGg i)) ibp.
rewrite E1 E2 pmulr_rle0 ?invr_gt0//.
apply: (@le_trans _ _ (\int[gauss m]_x (0 : R))).
  have iS : (gauss m).-integrable [set: 'rV[R]_m]
      (EFin \o (fun x => \sum_i c i * (dF i x - Gg i x))).
    exact: integrable_Rsum.
  have i0 : (gauss m).-integrable [set: 'rV[R]_m] (EFin \o (fun=> (0 : R))).
    by apply: (integrable_gauss_bounded (C := 0)) => // x; rewrite normr0.
  by apply: le_Rintegral => // x _; exact: key.
by rewrite Rintegral_cst// mul0r.
Qed.

End derivative_sign.

Let cvg_sum0 (F : set_system R) {FF : Filter F} (s : seq 'I_n)
    (h : 'I_n -> R -> R) :
  (forall i, h i x @[x --> F] --> 0) -> \sum_(i <- s) h i x @[x --> F] --> 0.
Proof.
move=> hc; elim: s => [|i s IH].
  by under eq_fun do rewrite big_nil; exact: cvg_cst.
under eq_fun do rewrite big_cons.
have := cvgD (hc i) IH; rewrite addr0; apply.
Qed.

Let expR_lip (A B M : R) : A <= M -> B <= M ->
  `|expR A - expR B| <= expR M * `|A - B|.
Proof.
wlog AB : A B / B <= A.
  move=> H AM BM; have [BA|AB] := leP B A; first exact: H.
  by rewrite distrC [`|A - B|]distrC; apply: H => //; exact: ltW.
move=> AM BM.
rewrite ger0_norm ?subr_ge0 ?ler_expR// ger0_norm ?subr_ge0//.
have h1 : expR A - expR B <= expR A * (A - B).
  have e : expR B = expR A * expR (B - A) by rewrite -expRD addrC subrK.
  have := expR_ge1Dx (B - A); have := expR_gt0 A; rewrite e; nra.
apply: (le_trans h1); rewrite ler_wpM2r ?subr_ge0//.
by rewrite ler_expR.
Qed.

Let ln_lip (a b d : R) : 0 < d -> d <= a -> d <= b ->
  `|ln a - ln b| <= `|a - b| / d.
Proof.
wlog ab : a b / b <= a.
  move=> H d0 da db; have [ba|ab] := leP b a; first exact: H.
  by rewrite distrC [`|a - b|]distrC; apply: H => //; exact: ltW.
move=> d0 da db; have a0 : 0 < a := lt_le_trans d0 da.
have b0 : 0 < b := lt_le_trans d0 db.
rewrite ger0_norm ?subr_ge0 ?ler_ln ?posrE// ger0_norm ?subr_ge0//.
have h : ln a - ln b <= (a - b) / b.
  have e : ln a - ln b = ln (a / b).
    by rewrite lnM ?posrE ?invr_gt0// lnV ?posrE.
  have := expR_ge1Dx (ln (a / b)); rewrite lnK ?posrE ?divr_gt0// e.
  have bn0 : b != 0 := lt0r_neq0 b0.
  have -> : (a - b) / b = a / b - 1 by field.
  lra.
apply: (le_trans h); rewrite ler_wpM2l ?subr_ge0//.
by rewrite lef_pV2 ?posrE.
Qed.

Let G1 x : G 1 x = expR (\sum_i c i * ln (f i (mxdot x (u i)))).
Proof. by rewrite /G /g; under eq_bigr do rewrite mehler1. Qed.

Let G_lip r x : `|G r x - G 1 x| <=
  GK / delta * \sum_i c i * `|g r i (mxdot x (u i)) - f i (mxdot x (u i))|.
Proof.
have Sle (h : 'I_n -> R -> R) : (forall i y, delta <= h i y <= K) ->
    \sum_i c i * ln (h i (mxdot x (u i))) <= (\sum_i c i) * ln K.
  move=> hb; rewrite mulr_suml; apply: ler_sum => i _.
  apply: ler_wpM2l; first exact: ltW.
  have /andP[h1 h2] := hb i (mxdot x (u i)).
  by rewrite ler_ln ?posrE// (lt_le_trans delta0).
rewrite G1 /G.
apply: (le_trans (expR_lip (Sle _ (gb r)) (Sle _ fb))).
rewrite -/GK -mulrA ler_wpM2l ?expR_ge0// -sumrB.
apply: (le_trans (ler_norm_sum _ _ _)); rewrite mulr_sumr;
  apply: ler_sum => i _.
rewrite -mulrBr normrM (gtr0_norm (c0 i)) mulrCA ler_wpM2l ?(ltW (c0 i))//.
rewrite mulrC; apply: ln_lip => //;
  first by case/andP: (gb r i (mxdot x (u i))).
by case/andP: (fb i (mxdot x (u i))).
Qed.

Let Lambda_lip r : `|r| < 1 -> `|Lambda r - Lambda 1| <=
  GK / delta * \sum_i c i * \int[N]_y `|mehler r (f i) y - f i y|.
Proof.
move=> r1.
have iG := integrable_G (or_introl r1).
have iG1 := integrable_G (or_intror erefl).
have iD := integrableB measurableT iG iG1.
have iD' : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => G r x - G 1 x)).
  by move: iD; apply: (eq_integrable measurableT) => x _; rewrite /= EFinB.
have mh i : measurable_fun [set: R] (fun y => `|mehler r (f i) y - f i y|).
  apply: measurableT_comp => //; apply: measurable_funB => //.
  exact: measurable_mehler (mf i) (fK i) r1.
have ih i : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => `|g r i (mxdot x (u i)) - f i (mxdot x (u i))|)).
  apply: (integrable_gauss_bounded (C := K + K)).
    by apply: measurableT_comp (mh i) (measurable_mxdot (u i)).
  move=> x; rewrite normr_id (le_trans (ler_normB _ _))//.
  apply: lerD; first exact: mehler_le (mf i) (fK i).
  exact: fK.
have ic i : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun x => c i * `|g r i (mxdot x (u i)) - f i (mxdot x (u i))|)).
  have := integrableZl measurableT (c i) (ih i).
  by apply: (eq_integrable measurableT) => x _; rewrite /= EFinM.
have iS : (gauss m).-integrable [set: 'rV[R]_m] (EFin \o (fun x =>
    \sum_i c i * `|g r i (mxdot x (u i)) - f i (mxdot x (u i))|)).
  exact: integrable_Rsum.
rewrite /Lambda -(RintegralB measurableT iG iG1).
apply: (le_trans (le_normr_Rintegral measurableT iD')).
apply: (@le_trans _ _ (\int[gauss m]_x (GK / delta * \sum_i c i *
    `|g r i (mxdot x (u i)) - f i (mxdot x (u i))|))).
  apply: le_Rintegral; first exact: measurableT.
  - apply: (integrable_gauss_bounded (C := GK + GK)).
      apply: measurableT_comp => //; apply: measurable_funB.
        exact: measurable_G (or_introl r1).
      exact: measurable_G (or_intror erefl).
    move=> x; rewrite normr_id (le_trans (ler_normB _ _))//.
    by apply: lerD; exact: G_norm.
  - have := integrableZl measurableT (GK / delta) iS.
    by apply: (eq_integrable measurableT) => x _; rewrite /= EFinM.
  - by move=> x _; exact: G_lip.
rewrite (RintegralZl _ measurableT iS).
rewrite ler_wpM2l ?divr_ge0 ?expR_ge0 ?(ltW delta0)//.
rewrite Rintegral_sum// le_eqVlt; apply/orP; left; apply/eqP.
apply: eq_bigr => i _; rewrite (RintegralZl _ measurableT (ih i));
  congr (_ * _).
have u0 : u i != 0 by apply/eqP => u0; move: (u1 i); rewrite u0 mxdot0l;
  apply/eqP; rewrite eq_sym oner_neq0.
rewrite /Rintegral; apply: congr1.
have mF : measurable_fun [set: R] (fun y => (`|mehler r (f i) y - f i y|)%:E).
  by apply/measurable_EFinP; exact: mh.
have F0 y : (0 <= (`|mehler r (f i) y - f i y|)%:E)%E by rewrite lee_fin.
have E := ge0_integral_gauss_mxdot u0 mF F0.
by rewrite /frobenius u1 sqrtr1 in E; exact: E.
Qed.

Let Lambda_cvg1 : Lambda r @[r --> (1 : R)^'-] --> Lambda 1.
Proof.
pose psi r := GK / delta * \sum_i c i * \int[N]_y `|mehler r (f i) y - f i y|.
have hpsi : psi r @[r --> (1 : R)^'-] --> 0.
  rewrite -[X in _ --> X](mulr0 (GK / delta));
    apply: cvgM; first exact: cvg_cst.
  apply: cvg_sum0 => i.
  rewrite -[X in _ --> X](mulr0 (c i)); apply: cvgM; first exact: cvg_cst.
  exact: mehler_cvg_L1 (mf i) (fK i).
apply/cvgrPdist_le => eps e0.
have := hpsi; move=> /cvgrPdist_le /(_ eps e0) hp.
near=> r.
have r0 : 0 < r by near: r; exact: nbhs_left_gt.
have r1 : r < 1 by near: r; exact: nbhs_left_lt.
have hr : `|0 - psi r| <= eps by near: r; exact: hp.
rewrite distrC (le_trans (Lambda_lip _)) ?gtr0_norm//.
by move: hr; rewrite sub0r normrN; apply: le_trans; exact: ler_norm.
Unshelve. all: by end_near.
Qed.

Local Lemma Lambda_le : Lambda 1 <= Lambda 0.
Proof.
have dL (r : R) : r \in `]0, 1[ ->
    is_derive r (1 : R) Lambda (\int[gauss m]_x dG r x).
  by rewrite in_itv /= => /andP[r0 r1]; apply: is_derive_Lambda;
    rewrite gtr0_norm.
have cont (r : R) : `|r| < 1 -> {for r, continuous Lambda}.
  move=> r1; apply: differentiable_continuous; apply/derivable1_diffP.
  exact: (@ex_derive _ _ _ _ _ _ _ (@is_derive_Lambda r r1)).
have cL : {within `[0, 1], continuous Lambda}.
  apply/(continuous_within_itvP _ ltr01); split.
  - move=> r; rewrite in_itv /= => /andP[r0 r1]; apply: cont.
    by rewrite gtr0_norm.
  - by apply: cvg_at_right_filter; apply: cont; rewrite normr0.
  - exact: Lambda_cvg1.
have [xi xiI E] := MVT ltr01 dL cL.
move: xiI; rewrite in_itv /= => /andP[x0 x1].
have := @dLambda_le0 xi x0 x1.
by move: E; rewrite subr0 mulr1 => E h; rewrite -subr_le0 E.
Qed.

Local Lemma gauss_brascamp_lieb_bounded_sec :
  \int[gauss m]_x (\prod_i (f i (mxdot x (u i))) `^ (c i)) <=
  \prod_i (\int[N]_y f i y) `^ (c i).
Proof.
have fp i y : 0 < f i y.
  by have /andP[h _] := fb i y; exact: lt_le_trans delta0 h.
have E1 x : \prod_i (f i (mxdot x (u i))) `^ (c i) =
    expR (\sum_i c i * ln (f i (mxdot x (u i)))).
  by rewrite expR_sum; apply: eq_bigr => i _; rewrite /powR gt_eqF.
have ip i : 0 < \int[N]_y f i y.
  apply: (lt_le_trans delta0); apply: (@Rintegral_normal_ge _ _ delta K) => //.
  by move=> y; case/andP: (fb i y).
have E0 : \prod_i (\int[N]_y f i y) `^ (c i) =
    expR (\sum_i c i * ln (\int[N]_y f i y)).
  by rewrite expR_sum; apply: eq_bigr => i _; rewrite /powR gt_eqF.
rewrite E0 (eq_Rintegral _ (fun x _ => E1 x)) -Lambda1 -Lambda0.
exact: Lambda_le.
Qed.

End gauss_brascamp_lieb_bounded.

Theorem gauss_brascamp_lieb_bounded {R : realType} m n (u : 'I_n -> 'rV[R]_m)
    (c : 'I_n -> R) (f : 'I_n -> R -> R) (delta K : R) :
  (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M -> 0 < delta -> delta <= K ->
  (forall i, measurable_fun [set: R] (f i)) ->
  (forall i y, delta <= f i y <= K) ->
  \int[gauss m]_x (\prod_i (f i (mxdot x (u i))) `^ (c i)) <=
  \prod_i (\int[normal_prob 0 1]_y f i y) `^ (c i).
Proof.
move=> u1 c0 frame d0 dK mf fb.
by apply: gauss_brascamp_lieb_bounded_sec; eassumption.
Qed.
