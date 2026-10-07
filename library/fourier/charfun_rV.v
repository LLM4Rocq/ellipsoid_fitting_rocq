From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix interval archimedean.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal interval_inference topology.
From mathcomp Require Import normedtype sequences derive realfun exp numfun.
From mathcomp Require Import measure trigo.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral.
From GaussianAnalysis.gaussian Require Import gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import parameter_integral.
From GaussianAnalysis.gaussian Require Import gauss_moments lebesgue_rV.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import normal_linear gauss_linear.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.fourier Require Import charfun.

(**md**************************************************************************)
(* # Characteristic functions of laws on row vectors                          *)
(*                                                                            *)
(* For a law nu on 'rV[R]_m, cf_rV nu theta is the characteristic function of *)
(* nu at theta, given by its real and imaginary parts, the integrals of       *)
(* cos <x, theta> and sin <x, theta> against nu; it is the characteristic     *)
(* function at 1 of the law of <x, theta> (cf_rV_law). It is continuous in    *)
(* theta and of modulus at most one. The characteristic function of gauss m   *)
(* is exp (- |theta|^2 / 2) (cf_rV_gauss). The law of the sum of independent  *)
(* vectors has the complex product of their characteristic functions          *)
(* (cf_rV_add), and the law of \sum_k x_k w_k, for independent real x_k, has  *)
(* the complex product of those of the x_k at <w_k, theta>                    *)
(* (cf_rV_tuple_prod).                                                        *)
(*                                                                            *)
(* Gaussian regularization, as in the method of Ball and Nazarov: for Y of    *)
(* law nu and an independent G of law gauss m,                                *)
(* E[exp (- |z - Y|^2 / (2 s^2))] is a Gaussian average of cf nu             *)
(* (cf_rV_regularization), hence at most (s / sqrt (2 pi))^m times the        *)
(* integral of |cf nu| exp (- s^2 |theta|^2 / 2)                              *)
(* (cf_rV_regularization_le), and P(Y + s G in B) is at most (2 pi)^-m times  *)
(* that integral times the Lebesgue measure of B (prod_gauss_le_cf_rV). No    *)
(* Fourier inversion is needed. The law of y + s G has the density           *)
(* w |-> s^-m gauss_pdf ((w - y) / s) (ge0_integral_gauss_affine). Letting s  *)
(* tend to 0: if |cf nu| is integrable, a closed ball has probability at most *)
(* (2 pi)^-m (\int |cf nu|) times its Lebesgue measure (ball_le_cf_rV).       *)
(*                                                                            *)
(* Here <x, theta> = mxdot x theta and |x|^2 = mxdot x x.                     *)
(*                                                                            *)
(* ```                                                                        *)
(*      cf_rV_re nu theta == \int[nu]_x cos (mxdot x theta)                   *)
(*      cf_rV_im nu theta == \int[nu]_x sin (mxdot x theta)                   *)
(*         cf_rV nu theta == the pair (cf_rV_re nu theta, cf_rV_im nu theta)  *)
(*    cf_rV_norm nu theta == its modulus cmod (cf_rV nu theta)                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section cf_rV.
Context {R : realType} {m : nat}.
Implicit Types (nu : probability 'rV[R]_m R) (theta : 'rV[R]_m).

Definition cf_rV_re nu theta := \int[nu]_x cos (mxdot x theta).

Definition cf_rV_im nu theta := \int[nu]_x sin (mxdot x theta).

Definition cf_rV nu theta : R * R := (cf_rV_re nu theta, cf_rV_im nu theta).

Definition cf_rV_norm nu theta := cmod (cf_rV nu theta).

Lemma cf_rV_norm_ge0 nu theta : 0 <= cf_rV_norm nu theta.
Proof. exact: cmod_ge0. Qed.

(* If mu is the law of <x, theta> for x of law nu, then cf_rV nu theta is
   the characteristic function of mu at 1. *)
Lemma cf_rV_law nu theta (mu : probability (measurableTypeR R) R) :
  (forall A : set (measurableTypeR R), measurable A ->
     nu ((fun x => mxdot x theta) @^-1` A) = mu A) ->
  cf_rV nu theta = cf mu 1.
Proof.
move=> numu; rewrite (cf_image (measurable_mxdot theta) numu).
by rewrite /cf_rV /cf_rV_re /cf_rV_im; congr pair; apply: eq_Rintegral => x _;
  rewrite mul1r.
Qed.

Lemma cf_rV_norm_le1 nu theta : cf_rV_norm nu theta <= 1.
Proof.
have mT : measurable_fun [set: 'rV[R]_m]
    (fun x => (mxdot x theta : measurableTypeR R)).
  by move=> _ Y mY; exact: (measurable_mxdot theta measurableT mY).
pose g : {mfun 'rV[R]_m >-> measurableTypeR R} :=
  HB.pack (fun x : 'rV[R]_m => (mxdot x theta : measurableTypeR R))
    (isMeasurableFun.Build _ _ _ _ _ mT).
have E := @cf_rV_law nu theta (distribution nu g) (fun A mA => erefl).
by rewrite /cf_rV_norm E -cf_normE; exact: cf_norm_le1.
Qed.

Lemma cf_rV_re_le1 nu theta : `|cf_rV_re nu theta| <= 1.
Proof.
apply: Rintegral_bounded => [|x]; last exact: cos_max.
exact: measurable_cos_comp (measurable_mxdot theta).
Qed.

Lemma cf_rV_im_le1 nu theta : `|cf_rV_im nu theta| <= 1.
Proof.
apply: Rintegral_bounded => [|x]; last exact: sin_max.
exact: measurable_sin_comp (measurable_mxdot theta).
Qed.

Let continuous_mxdotr x : continuous (fun theta : 'rV[R]_m => mxdot x theta).
Proof.
apply: continuous_sum => i; apply: continuous_sum => j t.
apply: (continuousM (s := fun=> x i j) (t := fun v : 'rV[R]_m => v i j)).
  exact: cst_continuous.
exact: coord_continuous.
Qed.

Lemma continuous_cf_rV_re nu : continuous (cf_rV_re nu).
Proof.
move=> t0; apply: (@continuity_under_integral_at _ _ _ _ nu
  (fun t x => cos (mxdot x t)) setT t0 setT (fun=> 1)) => //.
- exact: filterT.
- by move=> t _; exact: integrable_cos_comp (measurable_mxdot t).
- move=> x _; apply: (@continuous_comp _ _ _ (fun t => mxdot x t) cos).
    exact: continuous_mxdotr.
  exact: continuous_cos.
- exact: finite_measure_integrable_cst.
- by move=> t _ x _; exact: cos_max.
Qed.

Lemma continuous_cf_rV_im nu : continuous (cf_rV_im nu).
Proof.
move=> t0; apply: (@continuity_under_integral_at _ _ _ _ nu
  (fun t x => sin (mxdot x t)) setT t0 setT (fun=> 1)) => //.
- exact: filterT.
- by move=> t _; exact: integrable_sin_comp (measurable_mxdot t).
- move=> x _; apply: (@continuous_comp _ _ _ (fun t => mxdot x t) sin).
    exact: continuous_mxdotr.
  exact: continuous_sin.
- exact: finite_measure_integrable_cst.
- by move=> t _ x _; exact: sin_max.
Qed.

Lemma continuous_cf_rV_norm nu : continuous (cf_rV_norm nu).
Proof.
move=> t; apply: (@continuous_comp _ _ _
  (fun t => cf_rV_re nu t ^+ 2 + cf_rV_im nu t ^+ 2) Num.sqrt).
  apply: continuousD.
    apply: (@continuous_comp _ _ _ (cf_rV_re nu) (fun x => x ^+ 2)).
      exact: continuous_cf_rV_re.
    exact: exprn_continuous.
  apply: (@continuous_comp _ _ _ (cf_rV_im nu) (fun x => x ^+ 2)).
    exact: continuous_cf_rV_im.
  exact: exprn_continuous.
exact: sqrt_continuous.
Qed.

Lemma measurable_cf_rV_norm nu : measurable_fun [set: 'rV[R]_m] (cf_rV_norm nu).
Proof. by apply: continuous_measurable_mx; exact: continuous_cf_rV_norm. Qed.

Lemma measurable_cf_rV_re nu : measurable_fun [set: 'rV[R]_m] (cf_rV_re nu).
Proof. by apply: continuous_measurable_mx; exact: continuous_cf_rV_re. Qed.

Lemma measurable_cf_rV_im nu : measurable_fun [set: 'rV[R]_m] (cf_rV_im nu).
Proof. by apply: continuous_measurable_mx; exact: continuous_cf_rV_im. Qed.

(* The characteristic function of the standard Gaussian measure. *)
Lemma cf_rV_gauss theta :
  cf_rV (gauss m) theta = (expR (- mxdot theta theta / 2), 0).
Proof.
have [->|t0] := eqVneq theta 0.
  rewrite /cf_rV /cf_rV_re /cf_rV_im mxdot0l oppr0 mul0r expR0.
  under eq_Rintegral do rewrite mxdot0r cos0.
  under [X in (_, X)]eq_Rintegral do rewrite mxdot0r sin0.
  rewrite Rintegral_cst// [X in fine X]probability_setT mul1r.
  by rewrite Rintegral_cst// mul0r.
rewrite (@cf_rV_law _ theta (normal_prob 0 (frobenius theta))).
  by move=> A mA; exact: gauss_mxdot.
rewrite cf_normal ?frobenius_eq0// mulr1 mul0r cos0 sin0 mulr1 mulr0.
by rewrite frobenius_sqr.
Qed.

Lemma cf_rV_norm_gauss theta :
  cf_rV_norm (gauss m) theta = expR (- mxdot theta theta / 2).
Proof.
rewrite /cf_rV_norm cf_rV_gauss /cmod /= expr0n addr0 sqrtr_sqr.
by rewrite ger0_norm// expR_ge0.
Qed.

End cf_rV.

(* If nu is the law of g under P, the characteristic function of nu is
   computed under P. *)
Section cf_rV_image.
Context {R : realType} {m : nat} d (T : measurableType d) (P : probability T R).
Variables (nu : probability 'rV[R]_m R) (g : T -> 'rV[R]_m).
Hypothesis mg : measurable_fun [set: T] g.
Hypothesis gnu : forall A : set 'rV[R]_m, measurable A ->
  P (g @^-1` A) = nu A.

Lemma cf_rV_image theta :
  cf_rV nu theta =
  (\int[P]_x cos (mxdot (g x) theta), \int[P]_x sin (mxdot (g x) theta)).
Proof.
have mgt : measurable_fun [set: T] (fun x => mxdot (g x) theta).
  exact: measurableT_comp (measurable_mxdot theta) mg.
rewrite /cf_rV /cf_rV_re /cf_rV_im /Rintegral; congr pair.
  rewrite -(@integral_image _ _ T 'rV[R]_m R P nu g mg gnu)//.
  exact: integrable_cos_comp (measurable_mxdot theta).
rewrite -(@integral_image _ _ T 'rV[R]_m R P nu g mg gnu)//.
exact: integrable_sin_comp (measurable_mxdot theta).
Qed.

Lemma cf_rV_norm_image theta :
  cf_rV_norm nu theta =
  cmod (\int[P]_x cos (mxdot (g x) theta), \int[P]_x sin (mxdot (g x) theta)).
Proof. by rewrite /cf_rV_norm cf_rV_image. Qed.

End cf_rV_image.

Section cf_rV_independent.
Context {R : realType} {m : nat}.

(* For independent Y and Z of laws nu1 and nu2, the characteristic function
   of the law of Y + Z is the complex product of those of nu1 and nu2. *)
Lemma cf_rV_add (nu1 nu2 nu : probability 'rV[R]_m R) :
  (forall A : set 'rV[R]_m, measurable A ->
     (nu1 \x nu2)%E ((fun p => p.1 + p.2) @^-1` A) = nu A) ->
  forall theta, cf_rV nu theta = cmul (cf_rV nu1 theta) (cf_rV nu2 theta).
Proof.
move=> numu theta.
have mg : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] (fun p => p.1 + p.2).
  exact: measurable_addmx measurable_fst measurable_snd.
rewrite (cf_rV_image mg numu).
have := cf_prod_integral nu1 nu2 (measurable_mxdot theta)
  (measurable_mxdot theta) 1.
rewrite /cf_rV /cf_rV_re /cf_rV_im.
under [X in (X, _) = _]eq_Rintegral do rewrite mul1r.
under [X in (_, X) = _]eq_Rintegral do rewrite mul1r.
under [X in _ = cmul (X, _) _]eq_Rintegral do rewrite mul1r.
under [X in _ = cmul (_, X) _]eq_Rintegral do rewrite mul1r.
under [X in _ = cmul _ (X, _)]eq_Rintegral do rewrite mul1r.
under [X in _ = cmul _ (_, X)]eq_Rintegral do rewrite mul1r.
by move=> <-; congr pair; apply: eq_Rintegral => p _; rewrite mxdotDl.
Qed.

Lemma cf_rV_norm_add (nu1 nu2 nu : probability 'rV[R]_m R) :
  (forall A : set 'rV[R]_m, measurable A ->
     (nu1 \x nu2)%E ((fun p => p.1 + p.2) @^-1` A) = nu A) ->
  forall theta,
    cf_rV_norm nu theta = cf_rV_norm nu1 theta * cf_rV_norm nu2 theta.
Proof. by move=> numu theta; rewrite /cf_rV_norm (cf_rV_add numu) cmodM. Qed.

(* Independent coordinates: for x of law tuple_prod mu n and vectors w k, the
   characteristic function of the law of \sum_k x_k w_k at theta is the
   complex product of the characteristic functions of the mu k at
   <w k, theta>. *)
Lemma cf_rV_tuple_prod (mu : nat -> probability (measurableTypeR R) R) n
    (w : nat -> 'rV[R]_m) (nu : probability 'rV[R]_m R) :
  (forall A : set 'rV[R]_m, measurable A ->
     tuple_prod mu n ((fun x => \sum_(k < n) tnth x k *: w k) @^-1` A) =
     nu A) ->
  forall theta,
    cf_rV nu theta = \big[cmul/(1, 0)]_(k < n) cf (mu k) (mxdot (w k) theta).
Proof.
move=> numu theta.
have mg : measurable_fun [set: n.-tuple (measurableTypeR R)]
    (fun x => \sum_(k < n) tnth x k *: w k).
  apply/measurable_fun_mxP => i j.
  rewrite (_ : (fun x => _) = (fun x => \sum_(k < n) tnth x k * w k i j)).
    by apply/funext => x; rewrite summxE; apply: eq_bigr => k _; rewrite mxE.
  apply: measurable_sum => k; apply: measurable_funM => //.
  exact: measurable_tnth.
rewrite (cf_rV_image mg numu).
have E x : mxdot (\sum_(k < n) tnth x k *: w k) theta =
    1 * \sum_(k < n) mxdot (w k) theta * tnth x k.
  rewrite mul1r mxdot_suml; apply: eq_bigr => k _.
  by rewrite mxdotZl mulrC.
under eq_Rintegral do rewrite E.
under [X in (_, X)]eq_Rintegral do rewrite E.
rewrite (cf_tuple_prod_integral mu n (fun k => mxdot (w k) theta) 1).
by under eq_bigr do rewrite mulr1.
Qed.

Lemma cf_rV_norm_tuple_prod (mu : nat -> probability (measurableTypeR R) R) n
    (w : nat -> 'rV[R]_m) (nu : probability 'rV[R]_m R) :
  (forall A : set 'rV[R]_m, measurable A ->
     tuple_prod mu n ((fun x => \sum_(k < n) tnth x k *: w k) @^-1` A) =
     nu A) ->
  forall theta,
    cf_rV_norm nu theta = \prod_(k < n) cf_norm (mu k) (mxdot (w k) theta).
Proof.
move=> numu theta; rewrite /cf_rV_norm (cf_rV_tuple_prod numu) cmod_prod.
by apply: eq_bigr => k _; rewrite cf_normE.
Qed.

End cf_rV_independent.

Section bounded_swap.
Context {R : realType}.

(* Fubini for a bounded measurable function on a product of probabilities,
   as an exchange of the iterated integrals. *)
Lemma Rintegral_swap_bounded d1 d2 (T1 : measurableType d1)
    (T2 : measurableType d2) (P1 : probability T1 R) (P2 : probability T2 R)
    (F : T1 * T2 -> R) (C : R) :
  measurable_fun [set: T1 * T2] F -> (forall p, `|F p| <= C) ->
  \int[P1]_x \int[P2]_y F (x, y) = \int[P2]_y \int[P1]_x F (x, y).
Proof.
move=> mF FC.
have iF := bounded_integrable (P1 \x P2)%E mF FC.
have m1 x : measurable_fun [set: T2] (fun y => F (x, y)).
  exact: measurable_fun_pair2.
have m2 y : measurable_fun [set: T1] (fun x => F (x, y)).
  exact: measurable_fun_pair1.
rewrite /Rintegral; congr fine.
transitivity (\int[P1]_x \int[P2]_y (F (x, y))%:E)%E.
  apply: eq_integral => x _.
  by rewrite (EFin_Rintegral_bounded P2 (C := C)).
transitivity (\int[P2]_y \int[P1]_x (F (x, y))%:E)%E.
  exact: (Fubini iF).
apply: eq_integral => y _.
by rewrite (EFin_Rintegral_bounded P1 (C := C)).
Qed.

End bounded_swap.

Section gauss_regularization.
Context {R : realType} {m : nat}.

(* The Gaussian regularization identity: for Y of law nu and G of law
   gauss m, independent, E[exp (- |z - Y|^2 / (2 s^2))] is the Gaussian
   average of cos <G/s, z> cf_re (G/s) + sin <G/s, z> cf_im (G/s). *)
Lemma cf_rV_regularization (nu : probability 'rV[R]_m R) (s : R)
    (z : 'rV[R]_m) : 0 < s ->
  \int[nu]_y expR (- mxdot (z - y) (z - y) / (2 * s ^+ 2)) =
  \int[gauss m]_g (cos (mxdot (s^-1 *: g) z) * cf_rV_re nu (s^-1 *: g) +
                   sin (mxdot (s^-1 *: g) z) * cf_rV_im nu (s^-1 *: g)).
Proof.
move=> s0; have sn0 : s != 0 by rewrite gt_eqF.
have E y : expR (- mxdot (z - y) (z - y) / (2 * s ^+ 2)) =
    \int[gauss m]_g cos (mxdot g (s^-1 *: (z - y))).
  transitivity (cf_rV_re (gauss m) (s^-1 *: (z - y))); last by [].
  have := cf_rV_gauss (s^-1 *: (z - y)); rewrite /cf_rV => -[-> _].
  by congr expR; rewrite mxdotZl mxdotZr; field.
under eq_Rintegral do rewrite E.
have mF : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
    (fun p : 'rV[R]_m * 'rV[R]_m => cos (mxdot p.2 (s^-1 *: (z - p.1)))).
  apply: measurable_cos_comp; apply: measurable_sum => i.
  apply: measurable_sum => j; apply: measurable_funM.
    exact: measurableT_comp (measurable_mxentry i j) measurable_snd.
  rewrite (_ : (fun p => _) =
      (fun p : 'rV[R]_m * 'rV[R]_m => s^-1 * (z i j - p.1 i j))).
    by apply/funext => p; rewrite !mxE.
  apply: measurable_funM => //; apply: measurable_funB => //.
  exact: measurableT_comp (measurable_mxentry i j) measurable_fst.
rewrite (Rintegral_swap_bounded nu (gauss m) mF (C := 1)).
  by move=> p; exact: cos_max.
apply: eq_Rintegral => g _.
transitivity (\int[nu]_y
    (cos (mxdot (s^-1 *: g) z) * cos (mxdot y (s^-1 *: g)) +
    sin (mxdot (s^-1 *: g) z) * sin (mxdot y (s^-1 *: g)))).
  apply: eq_Rintegral => y _.
  rewrite -cosB; congr cos.
  by rewrite /= !mxdotZl !mxdotZr mxdotBr mulrBr (mxdotC g y).
by rewrite Rintegral_cos_sin//; exact: measurable_mxdot.
Qed.


Lemma gauss_pdf_scale (s : R) (v : 'rV[R]_m) : 0 < s ->
  gauss_pdf (s^-1 *: v) =
  Num.sqrt (2 * pi) ^- m * expR (- mxdot v v / (2 * s ^+ 2)).
Proof.
move=> s0; have sn0 : s != 0 by rewrite gt_eqF.
by rewrite /gauss_pdf mxdotZl mxdotZr; congr (_ * expR _); field.
Qed.

Local Open Scope ereal_scope.

(* The law of y + s G, for G of law gauss m and s > 0, has the density
   w |-> s^-m gauss_pdf ((w - y) / s). *)
Lemma ge0_integral_gauss_affine (y : 'rV[R]_m) (s : R)
    (f : 'rV[R]_m -> \bar R) :
  (0 < s)%R -> measurable_fun [set: 'rV[R]_m] f -> (forall x, 0 <= f x) ->
  \int[gauss m]_g f (y + s *: g)%R =
  (s ^- m)%:E * \int[lebesgue_rV m]_w (f w * (gauss_pdf (s^-1 *: (w - y)))%:E).
Proof.
move=> s0 mf f0; have sn0 : s != 0%R by rewrite gt_eqF.
have mpdf := @measurable_gauss_pdf R m.
pose G (v : 'rV[R]_m) := f (y + v)%R * (gauss_pdf (s^-1 *: v))%:E.
have mG : measurable_fun [set: 'rV[R]_m] G.
  apply: emeasurable_funM.
    apply: measurableT_comp => //.
    change (measurable_fun setT (fun v : 'rV[R]_m => (y + v)%R)).
    by apply: measurable_addmx => //; exact: measurable_cst.
  apply/measurable_EFinP; apply: measurableT_comp => //.
  exact: measurable_rV_scale.
have G0 v : 0 <= G v by rewrite mule_ge0// lee_fin gauss_pdf_ge0.
rewrite ge0_integral_gauss_pdf.
- apply: measurableT_comp => //.
  change (measurable_fun setT (fun g : 'rV[R]_m => (y + s *: g)%R)).
  apply: measurable_addmx; first exact: measurable_cst.
  exact: measurable_rV_scale.
- by move=> x; exact: f0.
transitivity (\int[lebesgue_rV m]_u G (s *: u)).
  by apply: eq_integral => u _; rewrite /G scalerA mulVf// scale1r.
have E := (ge0_integral_lebesgue_rV_scale (n := m) (a := s) (f := G) sn0 mG
  (fun v => G0 v)).
rewrite [LHS]E (gtr0_norm s0).
apply: (congr1 (fun X => (s ^- m)%:E * X)).
rewrite -[LHS](ge0_integral_lebesgue_rV_shift (- y) mG G0).
apply: eq_integral => w _; rewrite /G addrCA subrr addr0.
by [].
Qed.

(* The bound behind the inequality of Ball and Nazarov: the Gaussian average
   of exp (- |z - Y|^2 / (2 s^2)) is at most (s / sqrt (2 pi))^m times the
   integral of |cf nu| exp (- s^2 |theta|^2 / 2). *)
Lemma cf_rV_regularization_le (nu : probability 'rV[R]_m R) (s : R)
    (z : 'rV[R]_m) : (0 < s)%R ->
  (\int[nu]_y expR (- mxdot (z - y) (z - y) / (2 * s ^+ 2)))%:E <=
  ((s / Num.sqrt (2 * pi)) ^+ m)%:E *
  \int[lebesgue_rV m]_th
    (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E.
Proof.
move=> s0; have sn0 : s != 0%R by rewrite gt_eqF.
have si0 : (0 < s^-1)%R by rewrite invr_gt0.
rewrite (cf_rV_regularization nu z s0).
have mcf := measurable_cf_rV_norm nu.
have mre := measurable_cf_rV_re nu; have mim := measurable_cf_rV_im nu.
have msc := measurable_rV_scale (n := m) s^-1.
have mH : measurable_fun [set: 'rV[R]_m] (fun g : 'rV[R]_m =>
    cos (mxdot (s^-1 *: g) z) * cf_rV_re nu (s^-1 *: g) +
    sin (mxdot (s^-1 *: g) z) * cf_rV_im nu (s^-1 *: g))%R.
  apply: measurable_funD; apply: measurable_funM.
  - apply: measurable_cos_comp.
    exact: measurableT_comp (measurable_mxdot z) msc.
  - exact: measurableT_comp mre msc.
  - apply: measurable_sin_comp.
    exact: measurableT_comp (measurable_mxdot z) msc.
  - exact: measurableT_comp mim msc.
have Hle g : (`|cos (mxdot (s^-1 *: g) z) * cf_rV_re nu (s^-1 *: g) +
    sin (mxdot (s^-1 *: g) z) * cf_rV_im nu (s^-1 *: g)| <=
    cf_rV_norm nu (s^-1 *: g))%R.
  rewrite mulrC [(sin _ * _)%R]mulrC; apply: cmod_ge_dot.
  by rewrite addrC sin2cos2 subrK.
have H1 g := le_trans (Hle g) (cf_rV_norm_le1 nu (s^-1 *: g)).
rewrite (EFin_Rintegral_bounded (gauss m) mH H1).
have mN : measurable_fun [set: 'rV[R]_m] (fun g => cf_rV_norm nu (s^-1 *: g)).
  exact: measurableT_comp mcf msc.
have N1 g : (`|cf_rV_norm nu (s^-1 *: g)| <= 1)%R.
  by rewrite ger0_norm ?cf_rV_norm_ge0//; exact: cf_rV_norm_le1.
apply: (@le_trans _ _ (\int[gauss m]_g (cf_rV_norm nu (s^-1 *: g))%:E)).
  apply: le_integral => //.
  - exact: (bounded_integrable (gauss m) mH H1).
  - exact: (bounded_integrable (gauss m) mN N1).
  by move=> g _; rewrite lee_fin; exact: le_trans (ler_norm _) (Hle g).
have mF : measurable_fun [set: 'rV[R]_m] (fun w => (cf_rV_norm nu w)%:E).
  exact/measurable_EFinP.
have F0 w : 0 <= (cf_rV_norm nu w)%:E by rewrite lee_fin cf_rV_norm_ge0.
have E2 := ge0_integral_gauss_affine 0 si0 mF F0.
have E3 : \int[gauss m]_g (cf_rV_norm nu (s^-1 *: g))%:E =
    \int[gauss m]_g (cf_rV_norm nu (0 + s^-1 *: g))%:E.
  by apply: eq_integral => g _; rewrite add0r.
rewrite E3 E2 invrK.
have E4 : \int[lebesgue_rV m]_w
      ((cf_rV_norm nu w)%:E * (gauss_pdf (s *: (w - 0)))%:E) =
    (Num.sqrt (2 * pi) ^- m)%:E * \int[lebesgue_rV m]_th
      (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E.
  have mxx : measurable_fun [set: 'rV[R]_m] (fun x => mxdot x x).
    apply: measurable_sum => i; apply: measurable_sum => j.
    by apply: measurable_funM; exact: measurable_mxentry.
  have mE : measurable_fun [set: 'rV[R]_m]
      (fun x => expR (- s ^+ 2 * mxdot x x / 2)).
    apply: measurableT_comp; first exact: measurable_expR.
    apply: measurable_funM; last exact: measurable_cst.
    apply: measurable_funM; first exact: measurable_cst.
    exact: mxx.
  have mEc : measurable_fun [set: 'rV[R]_m]
      (fun x => (expR (- s ^+ 2 * mxdot x x / 2) * cf_rV_norm nu x)%:E).
    by apply/measurable_EFinP; exact: (measurable_funM mE mcf).
  rewrite -ge0_integralZl_EFin.
  - exact: measurableT.
  - by move=> th _; rewrite lee_fin mulr_ge0 ?expR_ge0 ?cf_rV_norm_ge0.
  - exact: mEc.
  - by rewrite invr_ge0 exprn_ge0// sqrtr_ge0.
  apply: eq_integral => th _; rewrite subr0 -!EFinM; apply: congr1.
  rewrite /gauss_pdf mxdotZl mxdotZr.
  have -> : (- (s * (s * mxdot th th)) / 2 = - s ^+ 2 * mxdot th th / 2 :> R)%R.
    by ring.
  by rewrite mulrCA [(cf_rV_norm nu th * _)%R]mulrC.
rewrite E4 muleA -EFinM.
have -> : (s^-1 ^- m * Num.sqrt (2 * pi) ^- m =
    (s / Num.sqrt (2 * pi)) ^+ m)%R.
  by rewrite exprMn exprVn invrK exprVn.
exact: lexx.
Qed.


(* Gaussian regularization: for Y of law nu and G of law gauss m,
   independent, P(Y + s G in B) is at most (2 pi)^-m times the integral of
   |cf nu| exp (- s^2 |theta|^2 / 2), times the Lebesgue measure of B. *)
Lemma prod_gauss_le_cf_rV (nu : probability 'rV[R]_m R) (s : R)
    (B : set 'rV[R]_m) : (0 < s)%R -> measurable B ->
  (nu \x gauss m) [set p | B (p.1 + s *: p.2)%R] <=
  ((2 * pi) ^- m)%:E *
  \int[lebesgue_rV m]_th
    (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E *
  lebesgue_rV m B.
Proof.
move=> s0 mB; have sn0 : s != 0%R by rewrite gt_eqF.
set Kx := \int[lebesgue_rV m]_th _.
pose c : R := (Num.sqrt (2 * pi) ^- m)%R.
have c0 : (0 <= c)%R by rewrite invr_ge0 exprn_ge0// sqrtr_ge0.
pose ker (y w : 'rV[R]_m) := expR (- mxdot (w - y) (w - y) / (2 * s ^+ 2)).
have mE (y : 'rV[R]_m) :
    measurable_fun [set: 'rV[R]_m] (fun g => (y + s *: g)%R).
  apply: measurable_addmx; first exact: measurable_cst.
  exact: measurable_rV_scale.
have sec y : gauss m (xsection [set p | B (p.1 + s *: p.2)%R] y) =
    (s ^- m)%:E * \int[lebesgue_rV m]_w ((\1_B w)%:E * (c * ker y w)%:E).
  have mX : measurable [set g : 'rV[R]_m | B (y + s *: g)%R].
    by rewrite -[X in measurable X]setTI; exact: (mE y).
  have -> : xsection [set p | B (p.1 + s *: p.2)%R] y =
      [set g | B (y + s *: g)%R].
    by apply/seteqP; split => g; rewrite /xsection /= inE.
  transitivity (\int[gauss m]_g (\1_[set g | B (y + s *: g)%R] g)%:E).
    by rewrite integral_indic// setIT.
  transitivity (\int[gauss m]_g (\1_B (y + s *: g)%R)%:E).
    apply: eq_integral => g _; rewrite !indicE.
    by congr ((_ : bool)%:R%:E); apply/idP/idP => /set_mem H; apply/mem_set.
  rewrite (@ge0_integral_gauss_affine y s (fun w => (\1_B w)%:E) s0).
  - exact/measurable_EFinP/measurable_indic.
  - by move=> w; rewrite lee_fin indicE.
  apply: (congr1 (fun X => (s ^- m)%:E * X)); apply: eq_integral => w _.
  by rewrite gauss_pdf_scale.
have mker : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
    (fun p : 'rV[R]_m * 'rV[R]_m => ker p.1 p.2).
  apply: measurableT_comp; first exact: measurable_expR.
  apply: measurable_funM; last exact: measurable_cst.
  apply: measurable_funN.
  apply: measurable_sum => i; apply: measurable_sum => j.
  have mD : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
      (fun p : 'rV[R]_m * 'rV[R]_m => (p.2 - p.1)%R i j).
    rewrite (_ : (fun p => _) =
        (fun p : 'rV[R]_m * 'rV[R]_m => (p.2 i j - p.1 i j)%R)).
      by apply/funext => p; rewrite !mxE.
    apply: measurable_funB.
      exact: measurableT_comp (measurable_mxentry i j) measurable_snd.
    exact: measurableT_comp (measurable_mxentry i j) measurable_fst.
  exact: (measurable_funM mD mD).
pose F (p : 'rV[R]_m * 'rV[R]_m) := (\1_B p.2)%:E * (c * ker p.1 p.2)%:E.
have mF : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] F.
  apply: emeasurable_funM.
    apply/measurable_EFinP; apply: measurableT_comp; last exact: measurable_snd.
    exact: measurable_indic.
  apply/measurable_EFinP; apply: measurable_funM; first exact: measurable_cst.
  exact: mker.
have F0 p : 0 <= F p.
  by rewrite /F mule_ge0// lee_fin ?indicE// mulr_ge0// expR_ge0.
have -> : (nu \x gauss m)%E [set p | B (p.1 + s *: p.2)%R] =
    \int[nu]_y ((s ^- m)%:E * \int[lebesgue_rV m]_w F (y, w)).
  by apply: eq_integral => y _; exact: sec.
have sm0 : (0 <= s ^- m :> R)%R by rewrite invr_ge0 exprn_ge0// ltW.
rewrite ge0_integralZl_EFin.
- exact: measurableT.
- by move=> y _; apply: integral_ge0 => w _; exact: F0.
- exact: (measurable_fun_fubini_tonelli_F F mF F0).
- exact: sm0.
rewrite (fubini_tonelli F mF F0).
pose k : R := ((s / Num.sqrt (2 * pi)) ^+ m)%R.
have Kx0 : 0 <= Kx.
  apply: integral_ge0 => th _.
  by rewrite lee_fin mulr_ge0 ?expR_ge0// cf_rV_norm_ge0.
have kK0 : 0 <= k%:E * Kx.
  by rewrite mule_ge0// lee_fin exprn_ge0// divr_ge0 ?sqrtr_ge0// ltW.
have inner w : \int[nu]_y F (y, w) <= (\1_B w * c)%:E * (k%:E * Kx).
  have ker1 y : (`|ker y w| <= 1)%R.
    rewrite ger0_norm ?expR_ge0// -[X in (_ <= X)%R]expR0 ler_expR.
    have q0 : (0 <= mxdot (w - y) (w - y))%R by exact: mxdot_ge0.
    have d0 : (0 < 2 * s ^+ 2)%R by rewrite mulr_gt0// exprn_gt0.
    by rewrite mulNr oppr_le0 divr_ge0// ltW.
  have mk : measurable_fun [set: 'rV[R]_m] (fun y => ker y w).
    exact: (measurable_fun_pair1 w mker).
  have -> : \int[nu]_y F (y, w) = \int[nu]_y ((\1_B w * c)%:E * (ker y w)%:E).
    by apply: eq_integral => y _; rewrite /F /= -EFinM mulrA.
  rewrite ge0_integralZl_EFin.
  - exact: measurableT.
  - by move=> y _; rewrite lee_fin expR_ge0.
  - exact/measurable_EFinP.
  - by rewrite mulr_ge0// indicE.
  rewrite -(EFin_Rintegral_bounded nu mk ker1).
  apply: lee_wpmul2l; first by rewrite lee_fin mulr_ge0// indicE.
  exact: (cf_rV_regularization_le nu w s0).
have mIc : measurable_fun [set: 'rV[R]_m] (fun w => (\1_B w * c)%:E).
  apply/measurable_EFinP; apply: measurable_funM; last exact: measurable_cst.
  exact: measurable_indic.
apply: (@le_trans _ _ ((s ^- m)%:E *
    \int[lebesgue_rV m]_w ((\1_B w * c)%:E * (k%:E * Kx)))).
  apply: lee_wpmul2l; first by rewrite lee_fin.
  apply: ge0_le_integral.
  - exact: measurableT.
  - by move=> w _; apply: integral_ge0 => y _; exact: F0.
  - exact: (measurable_fun_fubini_tonelli_G F mF F0).
  - by apply: emeasurable_funM; [exact: mIc|exact: measurable_cst].
  - by move=> w _; exact: inner.
rewrite ge0_integralZr.
- exact: measurableT.
- exact: mIc.
- by move=> w _; rewrite lee_fin mulr_ge0// indicE.
- exact: kK0.
have IB : \int[lebesgue_rV m]_w (\1_B w * c)%:E = c%:E * lebesgue_rV m B.
  have -> : \int[lebesgue_rV m]_w (\1_B w * c)%:E =
      \int[lebesgue_rV m]_w (c%:E * (\1_B w)%:E).
    by apply: eq_integral => w _; rewrite -EFinM mulrC.
  rewrite ge0_integralZl_EFin.
  - exact: measurableT.
  - by move=> w _; rewrite lee_fin indicE.
  - exact/measurable_EFinP/measurable_indic.
  - exact: c0.
  by rewrite integral_indic// setIT.
rewrite IB.
have Ec : (s ^- m * (c * k) = (2 * pi) ^- m :> R)%R.
  rewrite /c /k -!exprVn -!exprMn; congr (_ ^+ _)%R.
  have sq0 : (Num.sqrt (2 * pi) != 0 :> R)%R.
    by rewrite sqrtr_eq0 -ltNge mulr_gt0// pi_gt0.
  have sq2 : (Num.sqrt (2 * pi) ^+ 2 = 2 * pi :> R)%R.
    by rewrite sqr_sqrtr// mulr_ge0// pi_ge0.
  transitivity ((Num.sqrt (2 * pi) ^+ 2)^-1 : R)%R; last by rewrite sq2.
  by field.
have -> : (s ^- m)%:E * (c%:E * lebesgue_rV m B * (k%:E * Kx)) =
    ((2 * pi) ^- m)%:E * Kx * lebesgue_rV m B.
  rewrite muleACA [LHS]muleA -!EFinM Ec [RHS]muleAC -[RHS]muleA.
  by [].
exact: lexx.
Qed.

End gauss_regularization.

Section ball_cf_rV.
Context {R : realType} {m : nat}.

Let measurable_mxdot_self :
  measurable_fun [set: 'rV[R]_m] (fun x => mxdot x x).
Proof.
apply: measurable_sum => i; apply: measurable_sum => j.
by apply: measurable_funM; exact: measurable_mxentry.
Qed.

Lemma measurable_ball_rV (z : 'rV[R]_m) (r : R) :
  measurable [set y : 'rV[R]_m | frobenius (y - z) <= r].
Proof.
have [r0|r0] := leP 0 r; last first.
  rewrite (_ : [set _ | _] = set0)// predeqE => y; split => // /= yr.
  by have := frobenius_ge0 (y - z); lra.
have mD : measurable_fun [set: 'rV[R]_m] (fun y => mxdot (y - z) (y - z)).
  have -> : (fun y => mxdot (y - z) (y - z)) =
      (fun x => mxdot x x) \o (fun y => (y - z)%R) by [].
  apply: measurableT_comp; first exact: measurable_mxdot_self.
  by apply: measurable_addmx; [exact: measurable_id|exact: measurable_cst].
have -> : [set y : 'rV[R]_m | frobenius (y - z) <= r] =
    (fun y => mxdot (y - z) (y - z)) @^-1` `]-oo, r ^+ 2]%classic.
  apply/seteqP; split => y /=; rewrite in_itv /= -frobenius_sqr;
    by rewrite ler_sqr ?nnegrE ?frobenius_ge0.
by rewrite -[X in measurable X]setTI; apply: mD => //; exact: measurable_itv.
Qed.

(* Scaling the radius of a ball by a > 0 multiplies its measure by a^m. *)
Lemma lebesgue_rV_ball_scale (z : 'rV[R]_m) (r a : R) : 0 <= r -> 0 < a ->
  lebesgue_rV m [set y | frobenius (y - z) <= a * r] =
  ((a ^+ m)%:E * lebesgue_rV m [set y | (frobenius (y - z) <= r)%R])%E.
Proof.
move=> r0 a0; have an0 : a != 0 by rewrite gt_eqF.
have mB0 (rho : R) : measurable [set y : 'rV[R]_m | frobenius y <= rho].
  rewrite (_ : [set y | _] = [set y : 'rV[R]_m | frobenius (y - 0) <= rho]).
    by apply/seteqP; split => y /=; rewrite subr0.
  exact: measurable_ball_rV.
have shift (rho : R) : lebesgue_rV m [set y | frobenius (y - z) <= rho] =
    lebesgue_rV m [set y | frobenius y <= rho].
  rewrite -(lebesgue_rV_shift (- z) (mB0 rho)).
  by congr (lebesgue_rV m _); apply/seteqP; split => y.
rewrite !shift.
have -> : [set y : 'rV[R]_m | frobenius y <= r] =
    (fun x => a *: x) @^-1` [set y | frobenius y <= a * r].
  apply/seteqP; split => y /=; rewrite frobeniusZ gtr0_norm//;
    by rewrite ler_pM2l.
rewrite (lebesgue_rV_scale an0 (mB0 (a * r))) muleA -EFinM.
by rewrite gtr0_norm// mulfV ?mul1e// expf_neq0.
Qed.


Lemma integral_gauss_mxdot_self :
  (\int[@gauss R m]_g (mxdot g g)%:E = m%:R%:E)%E.
Proof.
have mc (j : 'I_m) : measurable_fun [set: 'rV[R]_m]
    (fun g : 'rV[R]_m => (g 0 j * g 0 j)%:E).
  by apply/measurable_EFinP; apply: measurable_funM;
    exact: measurable_mxentry.
transitivity (\int[@gauss R m]_g (\sum_(j < m) (g 0 j * g 0 j)%:E))%E.
  by apply: eq_integral => g _; rewrite /mxdot big_ord1 sumEFin.
rewrite ge0_integral_sum.
- exact: measurableT.
- by move=> j; exact: mc.
- by move=> j g _; rewrite lee_fin -expr2 sqr_ge0.
under eq_bigr do rewrite gauss_cov eqxx.
by rewrite sumEFin sumr_const card_ord.
Qed.

(* Markov's inequality for |G|^2, G of law gauss m. *)
Lemma gauss_frobenius_ge (t : R) : 0 < t ->
  ((1 - m%:R / t ^+ 2)%:E <=
   @gauss R m [set g : 'rV[R]_m | (frobenius g <= t)%R])%E.
Proof.
move=> t0; have t20 : 0 < t ^+ 2 by rewrite exprn_gt0.
set A := [set g : 'rV[R]_m | t ^+ 2 <= mxdot g g].
have mA : measurable A.
  rewrite (_ : A = (fun g => mxdot g g) @^-1` `[t ^+ 2, +oo[%classic).
    by apply/seteqP; split => g; rewrite /A /= in_itv /= andbT.
  rewrite -[X in measurable X]setTI.
  by apply: measurable_mxdot_self => //; exact: measurable_itv.
have hA : ((t ^+ 2)%:E * gauss m A <= m%:R%:E)%E.
  rewrite -integral_gauss_mxdot_self.
  have -> : gauss m A = (\int[gauss m]_g (\1_A g)%:E)%E.
    by rewrite integral_indic// setIT.
  rewrite -ge0_integralZl_EFin.
  - exact: measurableT.
  - by move=> g _; rewrite lee_fin indicE.
  - exact/measurable_EFinP/measurable_indic.
  - exact: ltW.
  apply: ge0_le_integral.
  - exact: measurableT.
  - move=> g _; rewrite -EFinM lee_fin mulr_ge0 ?indicE//.
    exact: ltW.
  - apply: emeasurable_funM; first exact: measurable_cst.
    exact/measurable_EFinP/measurable_indic.
  - by apply/measurable_EFinP; exact: measurable_mxdot_self.
  move=> g _; rewrite -EFinM lee_fin indicE.
  have [gA|gA] := boolP (g \in A).
    by rewrite mulr1; move: gA; rewrite inE.
  by rewrite mulr0 mxdot_ge0.
have [a aE] : exists a : R, gauss m A = a%:E.
  exists (fine (gauss m A)); rewrite fineK// ge0_fin_numE//.
  by apply: le_lt_trans (probability_le1 _ mA) _; rewrite ltry.
have a_le : a <= m%:R / t ^+ 2.
  by move: hA; rewrite aE -EFinM lee_fin -ler_pdivlMl// mulrC.
apply: (@le_trans _ _ (gauss m (~` A))).
  by rewrite probability_setC// aE -EFinB lee_fin lerD2l lerN2.
apply: le_measure.
- by rewrite inE; exact: measurableC.
- rewrite inE (_ : [set g | _] = [set g : 'rV[R]_m | frobenius (g - 0) <= t]).
    by apply/seteqP; split => g /=; rewrite subr0.
  exact: measurable_ball_rV.
move=> g /= nA.
have gt : mxdot g g < t ^+ 2 by rewrite ltNge; apply/negP.
have t0' : 0 <= t by exact: ltW.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0// frobenius_sqr.
exact: (ltW gt).
Qed.


Let pow1D_le (e : R) n : 0 <= e -> e <= 1 ->
  (1 + e) ^+ n <= 1 + e * (n%:R * 2 ^+ n).
Proof.
move=> e0 e1; elim: n => [|n IH]; first by rewrite expr0 mul0r mulr0 addr0.
have P1 : 1 <= 2 ^+ n :> R by rewrite exprn_ege1// ler1n.
have n0 : 0 <= n%:R :> R by rewrite ler0n.
rewrite exprS (le_trans (ler_wpM2l (addr_ge0 ler01 e0) IH))//.
have h1 : 0 <= e * (n%:R * 2 ^+ n) * (1 - e).
  by rewrite !mulr_ge0// ?exprn_ge0// subr_ge0.
have h2 : 0 <= e * (2 * 2 ^+ n - 1) by rewrite mulr_ge0//; lra.
rewrite -natr1 exprS; nra.
Qed.

Let le_of_le_mul (x c : R) n : 0 <= x -> 0 <= c ->
  (forall e, 0 < e -> e <= 2^-1 -> x * (1 - e) <= c * (1 + e) ^+ n) ->
  x <= c.
Proof.
move=> x0 c0 H; apply/ler_addgt0Pr => eta eta0.
pose M : R := n%:R * 2 ^+ n.
have M0 : 0 <= M by rewrite mulr_ge0// ?ler0n// exprn_ge0.
have D0 : 0 < c * M + x + 1 by rewrite ltr_wpDl// addr_ge0// mulr_ge0.
pose e := Num.min 2^-1 (eta / (c * M + x + 1)).
have e0 : 0 < e by rewrite lt_min invr_gt0 ltr0n divr_gt0.
have e2 : e <= 2^-1 by rewrite ge_min lexx.
have e1 : e <= 1 by apply: le_trans e2 _; rewrite invf_le1// ler1n.
have ee : e <= eta / (c * M + x + 1) by rewrite ge_min lexx orbT.
have eeta : e * (c * M + x) <= eta.
  apply: (le_trans (ler_wpM2r (addr_ge0 (mulr_ge0 c0 M0) x0) ee)).
  rewrite mulrAC ler_pdivrMr// [X in _ <= X]mulrDr mulr1 lerDl.
  exact: ltW.
have := H e e0 e2.
have := pow1D_le n (ltW e0) e1.
rewrite -/M => hP h; have := ler_wpM2l c0 hP; nra.
Qed.

(* If |cf nu| is integrable, a closed ball has probability at most
   (2 pi)^-m (\int |cf nu|) times its Lebesgue measure. *)
Lemma ball_le_cf_rV (nu : probability 'rV[R]_m R) (z : 'rV[R]_m) (r : R) :
  0 < r ->
  (\int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E < +oo)%E ->
  (nu [set y | (frobenius (y - z) <= r)%R] <=
   ((2 * pi) ^- m)%:E * \int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E *
   lebesgue_rV m [set y | (frobenius (y - z) <= r)%R])%E.
Proof.
move=> r0 Kfin.
set B := [set y | _]; set K := (\int[lebesgue_rV m]_th _)%E.
have mB : measurable B := measurable_ball_rV z r.
have K0 : (0 <= K)%E.
  by apply: integral_ge0 => th _; rewrite lee_fin cf_rV_norm_ge0.
have [k Kk] : exists k : R, K = k%:E.
  by exists (fine K); rewrite fineK// ge0_fin_numE.
have Lfin : (lebesgue_rV m B < +oo)%E.
  exact: le_lt_trans (lebesgue_rV_ball_le z r0) (ltry _).
have [l Ll] : exists l : R, lebesgue_rV m B = l%:E.
  by exists (fine (lebesgue_rV m B)); rewrite fineK// ge0_fin_numE.
have [x Px] : exists x : R, nu B = x%:E.
  exists (fine (nu B)); rewrite fineK// ge0_fin_numE//.
  by apply: le_lt_trans (probability_le1 _ mB) _; rewrite ltry.
have k0 : 0 <= k by rewrite -lee_fin -Kk.
have l0 : 0 <= l by rewrite -lee_fin -Ll measure_ge0.
have x0 : 0 <= x by rewrite -lee_fin -Px measure_ge0.
rewrite Kk Ll Px -!EFinM lee_fin.
apply: (le_of_le_mul (n := m)) => //; first by rewrite !mulr_ge0// invr_ge0
  exprn_ge0// mulr_ge0// pi_ge0.
move=> e e0 e2.
have e1 : e <= 1 by apply: le_trans e2 _; rewrite invf_le1// ler1n.
pose t : R := Num.sqrt (m.+1%:R / e).
have t0 : 0 < t by rewrite sqrtr_gt0 divr_gt0// ltr0n.
have t2 : t ^+ 2 = m.+1%:R / e by rewrite sqr_sqrtr// divr_ge0// ?ler0n ltW.
pose s : R := e * r / t.
have s0 : 0 < s by rewrite divr_gt0// mulr_gt0.
pose S := [set g : 'rV[R]_m | frobenius g <= t].
have mS : measurable S.
  rewrite /S (_ : [set g | _] = [set g : 'rV[R]_m | frobenius (g - 0) <= t]).
    by apply/seteqP; split => g /=; rewrite subr0.
  exact: measurable_ball_rV.
pose B' := [set y : 'rV[R]_m | frobenius (y - z) <= (1 + e) * r].
have mB' : measurable B' := measurable_ball_rV z ((1 + e) * r).
pose E := [set p : 'rV[R]_m * 'rV[R]_m | B' (p.1 + s *: p.2)].
have mE : measurable E.
  have mF : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
      (fun p : 'rV[R]_m * 'rV[R]_m => p.1 + s *: p.2).
    apply: measurable_addmx; first exact: measurable_fst.
    apply: measurable_scalemx; first exact: measurable_cst.
    exact: measurable_snd.
  by rewrite -[X in measurable X]setTI; exact: (mF measurableT B' mB').
have h1 : (x%:E * gauss m S = (nu \x gauss m) (B `*` S))%E.
  rewrite product_measure1E//; apply: (congr1 (fun X => X * gauss m S)%E).
  by rewrite -Px.
have h2 : ((nu \x gauss m) (B `*` S) <= (nu \x gauss m) E)%E.
  apply: le_measure; rewrite ?inE//; first exact: measurableX.
  move=> [y g] [/= yB gS]; rewrite /E /B' /=.
  have -> : y + s *: g - z = (y - z) + s *: g by rewrite addrAC.
  apply: (le_trans (frobeniusD _ _)).
  rewrite frobeniusZ gtr0_norm// mulrDl mul1r; apply: lerD; first exact: yB.
  apply: (le_trans (ler_wpM2l (ltW s0) gS)).
  by rewrite /s divfK// lt0r_neq0.
have h3 := prod_gauss_le_cf_rV nu s0 mB'.
have mxx : measurable_fun [set: 'rV[R]_m] (fun th => mxdot th th).
  exact: measurable_mxdot_self.
have h4 : (\int[lebesgue_rV m]_th
    (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E <= K)%E.
  apply: ge0_le_integral.
  - exact: measurableT.
  - by move=> th _; rewrite lee_fin mulr_ge0 ?expR_ge0 ?cf_rV_norm_ge0.
  - apply/measurable_EFinP; apply: measurable_funM.
      apply: measurableT_comp; first exact: measurable_expR.
      apply: measurable_funM; last exact: measurable_cst.
      by apply: measurable_funM; [exact: measurable_cst|exact: mxx].
    exact: measurable_cf_rV_norm.
  - by apply/measurable_EFinP; exact: measurable_cf_rV_norm.
  move=> th _; rewrite lee_fin ler_piMl ?cf_rV_norm_ge0//.
  rewrite -[X in _ <= X]expR0 ler_expR !mulNr oppr_le0.
  by rewrite divr_ge0// mulr_ge0 ?sqr_ge0// mxdot_ge0.
have h5 : lebesgue_rV m B' = (((1 + e) ^+ m)%:E * lebesgue_rV m B)%E.
  by apply: lebesgue_rV_ball_scale; [exact: ltW|rewrite ltr_wpDr// ltW].
have h6 : ((1 - e)%:E <= gauss m S)%E.
  apply: le_trans (gauss_frobenius_ge t0).
  rewrite lee_fin lerD2l lerN2 t2 invf_div mulrA ler_pdivrMr ?ltr0n//.
  by rewrite mulrC ler_pM2l// ler_nat leqnSn.
have key : (x%:E * (1 - e)%:E <=
    ((2 * pi) ^- m)%:E * K * (((1 + e) ^+ m)%:E * l%:E))%E.
  apply: (le_trans (lee_wpmul2l _ h6)); first by rewrite lee_fin.
  rewrite h1; apply: (le_trans h2); apply: (le_trans h3).
  rewrite h5 -Ll; apply: lee_wpmul2r.
    by rewrite mule_ge0// lee_fin exprn_ge0// addr_ge0// ltW.
  apply: lee_wpmul2l; last exact: h4.
  by rewrite lee_fin invr_ge0 exprn_ge0// mulr_ge0// pi_ge0.
move: key; rewrite Kk -!EFinM lee_fin [((1 + e) ^+ m * l)%R]mulrC mulrA.
by [].
Qed.

End ball_cf_rV.
