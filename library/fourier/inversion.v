From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix interval archimedean.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal interval_inference topology.
From mathcomp Require Import normedtype sequences derive realfun exp numfun.
From mathcomp Require Import measure trigo.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral charge.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import parameter_integral lebesgue_rV.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import gauss_linear gauss_smoothing.
From GaussianAnalysis.comparison Require Import gauss_law.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.fourier Require Import charfun esseen charfun_rV.

(**md**************************************************************************)
(* # The Fourier inversion theorem on row vectors                             *)
(*                                                                            *)
(* Let nu be a law on 'rV[R]_m whose characteristic function is integrable:   *)
(* \int |cf nu theta| dtheta < +oo against lebesgue_rV m. Then nu has the     *)
(* density cf_rV_density nu with respect to lebesgue_rV m (cf_rV_inversion):  *)
(*                                                                            *)
(*   cf_rV_density nu w = (2 pi)^-m \int (cos <theta, w> cf_rV_re nu theta    *)
(*                           + sin <theta, w> cf_rV_im nu theta) dtheta.      *)
(*                                                                            *)
(* This density is continuous (continuous_cf_rV_density), nonnegative         *)
(* (cf_rV_density_ge0), of integral one (integral_cf_rV_density), and bounded *)
(* by (2 pi)^-m \int |cf nu| (cf_rV_density_le).                              *)
(*                                                                            *)
(* The proof uses no complex numbers and no Fourier transform of functions.   *)
(* For s > 0 the regularized density, the same integral with the factor       *)
(* exp (- s^2 |theta|^2 / 2), is the density s^-m E[gauss_pdf ((w - Y) / s)]  *)
(* of Y + s G, for Y of law nu and G of law gauss m independent               *)
(* (cf_rV_density_regE, integral_add_gauss), and it is also the average of    *)
(* cf_rV_density over w + s G (integral_cf_rV_density_gauss). It tends to     *)
(* cf_rV_density as s tends to 0 (cvg_cf_rV_density_reg), which gives the     *)
(* nonnegativity; the average gives the total mass. Hence Y + s G has the     *)
(* same law for Y of law nu and for Y of law cf_rV_inv_prob h, the            *)
(* probability with density cf_rV_density nu (integral_gauss_pdf_inv_prob).   *)
(* For a Lipschitz test function with values in [0, 1], the expectation       *)
(* under either law is within |L| s (1 + m) / 2 of the expectation of the     *)
(* smoothed variable (lipschitz_add_gauss), and measure_lipschitz_unique      *)
(* concludes.                                                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*   cf_rV_kernel nu w theta == cos <theta, w> cf_rV_re nu theta              *)
(*                              + sin <theta, w> cf_rV_im nu theta            *)
(*        cf_rV_density nu w == (2 pi)^-m \int cf_rV_kernel nu w theta dtheta *)
(*  cf_rV_density_reg nu s w == the same, with the factor                     *)
(*                              exp (- s^2 |theta|^2 / 2)                     *)
(*          cf_rV_inv_prob h == for h : \int |cf nu| < +oo, the probability   *)
(*                              with density cf_rV_density nu                 *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section cf_rV_density.
Context {R : realType} {m : nat}.
Variable nu : probability 'rV[R]_m R.

(* The integrand of the inversion formula at w: the real part of
   exp (- i <theta, w>) cf nu theta. *)
Definition cf_rV_kernel (w th : 'rV[R]_m) : R :=
  cos (mxdot th w) * cf_rV_re nu th + sin (mxdot th w) * cf_rV_im nu th.

(* It is bounded by |cf nu theta|. *)
Lemma cf_rV_kernel_le w th : `|cf_rV_kernel w th| <= cf_rV_norm nu th.
Proof.
rewrite /cf_rV_kernel mulrC [sin _ * _]mulrC; apply: cmod_ge_dot.
by rewrite addrC sin2cos2 subrK.
Qed.

Lemma measurable_cf_rV_kernel w :
  measurable_fun [set: 'rV[R]_m] (cf_rV_kernel w).
Proof.
apply: measurable_funD; apply: measurable_funM.
- by apply: measurable_cos_comp; exact: measurable_mxdot.
- exact: measurable_cf_rV_re.
- by apply: measurable_sin_comp; exact: measurable_mxdot.
- exact: measurable_cf_rV_im.
Qed.

(* From here on, |cf nu| is integrable. *)
Hypothesis int_cf :
  (\int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E < +oo)%E.

Lemma integrable_cf_rV_norm :
  (lebesgue_rV m).-integrable [set: 'rV[R]_m] (EFin \o cf_rV_norm nu).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_cf_rV_norm.
have -> : (\int[lebesgue_rV m]_x `|(EFin \o cf_rV_norm nu) x| =
    \int[lebesgue_rV m]_x (cf_rV_norm nu x)%:E)%E.
  apply: eq_integral => x _.
  change (`|(cf_rV_norm nu x)%:E|%E = (cf_rV_norm nu x)%:E).
  by rewrite abse_EFin ger0_norm// cf_rV_norm_ge0.
exact: int_cf.
Qed.

Lemma integrable_cf_rV_kernel w :
  (lebesgue_rV m).-integrable [set: 'rV[R]_m] (EFin \o cf_rV_kernel w).
Proof.
apply: (le_integrable measurableT _ _ integrable_cf_rV_norm).
  by apply/measurable_EFinP; exact: measurable_cf_rV_kernel.
move=> th _; rewrite /comp !abse_EFin lee_fin.
by rewrite (ger0_norm (cf_rV_norm_ge0 nu th)); exact: cf_rV_kernel_le.
Qed.

(* The density given by the inversion formula. *)
Definition cf_rV_density (w : 'rV[R]_m) : R :=
  (2 * pi) ^- m * \int[lebesgue_rV m]_th cf_rV_kernel w th.

(* The density is bounded by (2 pi)^-m \int |cf nu|. *)
Lemma cf_rV_density_le w :
  `|cf_rV_density w| <=
  (2 * pi) ^- m * \int[lebesgue_rV m]_th cf_rV_norm nu th.
Proof.
have c0 : 0 <= (2 * pi) ^- m :> R.
  by rewrite invr_ge0 exprn_ge0// mulr_ge0// pi_ge0.
rewrite /cf_rV_density normrM ger0_norm//; apply: ler_wpM2l => //.
apply: le_trans (le_normr_Rintegral _ (integrable_cf_rV_kernel w)) _.
  exact: measurableT.
apply: le_Rintegral => //.
- apply: (le_integrable measurableT _ _ integrable_cf_rV_norm).
    apply/measurable_EFinP; apply: measurableT_comp => //.
    exact: measurable_cf_rV_kernel.
  move=> th _; rewrite /comp !abse_EFin normr_id lee_fin.
  by rewrite (ger0_norm (cf_rV_norm_ge0 nu th)); exact: cf_rV_kernel_le.
- exact: integrable_cf_rV_norm.
by move=> th _; exact: cf_rV_kernel_le.
Qed.

Let measurable_mxdot_self :
  measurable_fun [set: 'rV[R]_m] (fun x => mxdot x x).
Proof.
apply: measurable_sum => i; apply: measurable_sum => j.
by apply: measurable_funM; exact: measurable_mxentry.
Qed.

Let continuous_mxdotr (x : 'rV[R]_m) :
  continuous (fun theta : 'rV[R]_m => mxdot x theta).
Proof.
apply: continuous_sum => i; apply: continuous_sum => j t.
apply: (continuousM (s := fun=> x i j) (t := fun v : 'rV[R]_m => v i j)).
  exact: cst_continuous.
exact: coord_continuous.
Qed.

(* The density is continuous, by dominated convergence. *)
Lemma continuous_cf_rV_density : continuous cf_rV_density.
Proof.
move=> w0; apply: (continuousM (s := fun=> (2 * pi) ^- m)
  (t := fun w => \int[lebesgue_rV m]_th cf_rV_kernel w th)).
  exact: cst_continuous.
apply: (@continuity_under_integral_at _ _ _ _ (lebesgue_rV m)
  (fun w th => cf_rV_kernel w th) setT w0 setT (cf_rV_norm nu)) => //.
- exact: filterT.
- by move=> w _; exact: integrable_cf_rV_kernel.
- move=> th _.
  have c1 : {for w0, continuous (fun w => cos (mxdot th w))}.
    apply: (@continuous_comp _ _ _ (fun w => mxdot th w) cos).
      exact: continuous_mxdotr.
    exact: continuous_cos.
  have s1 : {for w0, continuous (fun w => sin (mxdot th w))}.
    apply: (@continuous_comp _ _ _ (fun w => mxdot th w) sin).
      exact: continuous_mxdotr.
    exact: continuous_sin.
  apply: (continuousD (f := fun w => cos (mxdot th w) * cf_rV_re nu th)
    (g := fun w => sin (mxdot th w) * cf_rV_im nu th)).
    apply: (continuousM (s := fun w => cos (mxdot th w))
      (t := fun=> cf_rV_re nu th)) => //; exact: cst_continuous.
  apply: (continuousM (s := fun w => sin (mxdot th w))
    (t := fun=> cf_rV_im nu th)) => //; exact: cst_continuous.
- exact: integrable_cf_rV_norm.
- by move=> w _ th _; exact: cf_rV_kernel_le.
Qed.

(* The regularized density: (2 pi)^-m times the integral of
   exp (- s^2 |theta|^2 / 2) times the kernel. *)
Definition cf_rV_density_reg (s : R) (w : 'rV[R]_m) : R :=
  (2 * pi) ^- m * \int[lebesgue_rV m]_th
    (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_kernel w th).

Lemma cf_rV_density_reg0 w : cf_rV_density_reg 0 w = cf_rV_density w.
Proof.
rewrite /cf_rV_density_reg /cf_rV_density; congr (_ * _).
by apply: eq_Rintegral => th _; rewrite expr0n /= oppr0 !mul0r expR0 mul1r.
Qed.

(* The regularized density tends to the density as s tends to 0. *)
Lemma cvg_cf_rV_density_reg w :
  cf_rV_density_reg s w @[s --> 0] --> cf_rV_density w.
Proof.
rewrite -cf_rV_density_reg0.
have Hle (s : R) th :
    `|expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_kernel w th| <=
    cf_rV_norm nu th.
  rewrite normrM ger0_norm ?expR_ge0//.
  apply: le_trans (cf_rV_kernel_le w th); rewrite -[leRHS]mul1r.
  apply: ler_wpM2r => //; rewrite -[leRHS]expR0 ler_expR !mulNr oppr_le0.
  by rewrite divr_ge0// mulr_ge0 ?sqr_ge0// mxdot_ge0.
have H : {for 0, continuous (fun s : R =>
    \int[lebesgue_rV m]_th (expR (- s ^+ 2 * mxdot th th / 2) *
      cf_rV_kernel w th))}.
  apply: (@continuity_under_integral_at _ _ _ _ (lebesgue_rV m)
    (fun (s : R) (th : 'rV[R]_m) =>
      expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_kernel w th)
    setT 0 setT (cf_rV_norm nu)) => //.
  - exact: filterT.
  - move=> s _; apply: (le_integrable measurableT _ _ integrable_cf_rV_norm).
      apply/measurable_EFinP; apply: measurable_funM.
        apply: measurableT_comp; first exact: measurable_expR.
        apply: measurable_funM; last exact: measurable_cst.
        apply: measurable_funM; first exact: measurable_cst.
        exact: measurable_mxdot_self.
      exact: measurable_cf_rV_kernel.
    move=> th _; rewrite /comp !abse_EFin lee_fin.
    by rewrite (ger0_norm (cf_rV_norm_ge0 nu th)); exact: Hle.
  - move=> th _.
    apply: (continuousM (s := fun s : R => expR (- s ^+ 2 * mxdot th th / 2))
      (t := fun=> cf_rV_kernel w th)); last exact: cst_continuous.
    apply: (@continuous_comp _ _ _
      (fun s : R => - s ^+ 2 * mxdot th th / 2) expR); last first.
      exact: continuous_expR.
    apply: (continuousM (s := fun s : R => - s ^+ 2 * mxdot th th)
      (t := fun=> 2^-1)); last exact: cst_continuous.
    apply: (continuousM (s := fun s : R => - s ^+ 2)
      (t := fun=> mxdot th th)); last exact: cst_continuous.
    apply: (@continuous_comp _ _ _ (fun s : R => s ^+ 2) -%R).
      exact: exprn_continuous.
    exact: opp_continuous.
  - exact: integrable_cf_rV_norm.
by rewrite /cf_rV_density_reg; apply: cvgMl_tmp; exact: H.
Qed.



Let measurable_rV_subl (w : 'rV[R]_m) :
  measurable_fun [set: 'rV[R]_m] (fun y : 'rV[R]_m => w - y).
Proof.
apply/measurable_fun_mxP => i j.
rewrite (_ : (fun y : 'rV[R]_m => (w - y) i j) =
    (fun y : 'rV[R]_m => w i j - y i j)).
  by apply/funext => y; rewrite !mxE.
by apply: measurable_funB; [exact: measurable_cst|exact: measurable_mxentry].
Qed.

Let measurable_mxdot2 d (T : measurableType d) (f g : T -> 'rV[R]_m) :
  measurable_fun [set: T] f -> measurable_fun [set: T] g ->
  measurable_fun [set: T] (fun x => mxdot (f x) (g x)).
Proof.
move=> mf mg; apply: measurable_sum => i; apply: measurable_sum => j.
apply: measurable_funM.
- exact: measurableT_comp (measurable_mxentry i j) mf.
- exact: measurableT_comp (measurable_mxentry i j) mg.
Qed.

Let reg_le (s : R) w th :
  `|expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_kernel w th| <=
  cf_rV_norm nu th.
Proof.
rewrite normrM ger0_norm ?expR_ge0//.
apply: le_trans (cf_rV_kernel_le w th); rewrite -[leRHS]mul1r.
apply: ler_wpM2r => //; rewrite -[leRHS]expR0 ler_expR !mulNr oppr_le0.
by rewrite divr_ge0// mulr_ge0 ?sqr_ge0// mxdot_ge0.
Qed.

Let integrable_reg (s : R) w : (lebesgue_rV m).-integrable [set: 'rV[R]_m]
  (EFin \o (fun th => expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_kernel w th)).
Proof.
apply: (le_integrable measurableT _ _ integrable_cf_rV_norm).
  apply/measurable_EFinP; apply: measurable_funM.
    apply: measurableT_comp; first exact: measurable_expR.
    apply: measurable_funM; last exact: measurable_cst.
    apply: measurable_funM; first exact: measurable_cst.
    exact: measurable_mxdot_self.
  exact: measurable_cf_rV_kernel.
move=> th _; rewrite /comp !abse_EFin lee_fin.
by rewrite (ger0_norm (cf_rV_norm_ge0 nu th)); exact: reg_le.
Qed.

(* For s > 0, the regularized density is the density of the law of
   Y + s G, for Y of law nu and G of law gauss m, independent:
   w |-> s^-m E[gauss_pdf ((w - Y) / s)]. *)
Lemma cf_rV_density_regE (s : R) w : 0 < s ->
  cf_rV_density_reg s w = s ^- m * \int[nu]_y gauss_pdf (s^-1 *: (w - y)).
Proof.
move=> s0; have sn0 : s != 0 by rewrite gt_eqF.
pose c : R := Num.sqrt (2 * pi) ^- m.
pose k := cf_rV_kernel w.
have mk : measurable_fun [set: 'rV[R]_m] k := measurable_cf_rV_kernel w.
have k1 th : `|k th| <= 1.
  exact: le_trans (cf_rV_kernel_le w th) (cf_rV_norm_le1 nu th).
have msc := measurable_rV_scale (n := m) s^-1.
have mks : measurable_fun [set: 'rV[R]_m] (fun g => k (s^-1 *: g)).
  exact: measurableT_comp mk msc.
have mker : measurable_fun [set: 'rV[R]_m]
    (fun y => expR (- mxdot (w - y) (w - y) / (2 * s ^+ 2))).
  apply: measurableT_comp; first exact: measurable_expR.
  apply: measurable_funM; last exact: measurable_cst.
  apply: measurable_funN.
  exact: measurable_mxdot2 (measurable_rV_subl w) (measurable_rV_subl w).
have ker1 y : `|expR (- mxdot (w - y) (w - y) / (2 * s ^+ 2))| <= 1.
  rewrite ger0_norm ?expR_ge0// -[X in _ <= X]expR0 ler_expR mulNr oppr_le0.
  by rewrite divr_ge0 ?mxdot_ge0// mulr_ge0// exprn_ge0// ltW.
have E1 : \int[nu]_y gauss_pdf (s^-1 *: (w - y)) =
    c * \int[gauss m]_g k (s^-1 *: g).
  transitivity (\int[nu]_y (c * expR (- mxdot (w - y) (w - y) / (2 * s ^+ 2)))).
    by apply: eq_Rintegral => y _; rewrite gauss_pdf_scale.
  rewrite RintegralZl.
  - exact: measurableT.
  - exact: (bounded_integrable nu mker ker1).
  by rewrite (cf_rV_regularization nu w s0).
have igk : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun g => k (s^-1 *: g))).
  exact: (bounded_integrable (gauss m) mks (fun g => k1 _)).
have mE : measurable_fun [set: 'rV[R]_m]
    (EFin \o (fun g => k (s^-1 *: g))).
  by apply/measurable_EFinP.
have il := (integrable_gauss_pdf mE).1 igk.
have E2 : (\int[gauss m]_g (k (s^-1 *: g))%:E =
    (s ^+ m * c)%:E * \int[lebesgue_rV m]_th
      ((expR (- s ^+ 2 * mxdot th th / 2) * k th)%:E))%E.
  rewrite (integral_gauss_pdf igk).
  have H := integral_lebesgue_rV_scale (n := m) (a := s) sn0 il.
  rewrite (gtr0_norm s0) in H.
  transitivity ((s ^+ m)%:E * \int[lebesgue_rV m]_x
      ((EFin \o (fun g => k (s^-1 *: g))) (s *: x) *
       (gauss_pdf (s *: x))%:E))%E.
    rewrite H muleA -EFinM mulfV ?mul1e//.
    exact: expf_neq0.
  rewrite EFinM -muleA; apply: (congr1 (fun X => ((s ^+ m)%:E * X)%E)).
  rewrite -integralZl.
  - exact: measurableT.
  - exact: integrable_reg.
  apply: eq_integral => x _.
  rewrite /= scalerA mulVf// scale1r /gauss_pdf mxdotZl mxdotZr -!EFinM.
  congr (_%:E).
  have -> : - (s * (s * mxdot x x)) / 2 = - s ^+ 2 * mxdot x x / 2 by ring.
  by rewrite /c; ring.
have E3 : \int[gauss m]_g k (s^-1 *: g) =
    s ^+ m * c * \int[lebesgue_rV m]_th
      (expR (- s ^+ 2 * mxdot th th / 2) * k th).
  rewrite [LHS]/Rintegral E2 fineM//.
  exact: (integrable_fin_num measurableT (integrable_reg s w)).
have cc : c * c = (2 * pi) ^- m.
  rewrite /c -invfM -expr2 -exprM mulnC exprM sqr_sqrtr//.
  by rewrite mulr_ge0// pi_ge0.
have ss : s ^- m * s ^+ m = 1 by rewrite mulVf// expf_neq0.
rewrite E1 E3 /cf_rV_density_reg /k.
move: (\int[lebesgue_rV m]_th _) => I.
transitivity (s ^- m * s ^+ m * (c * c) * I); first by rewrite ss mul1r cc.
by ring.
Qed.

(* The Gaussian side: E[cf_rV_kernel (w + s G) theta] for G of law gauss m
   is exp (- s^2 |theta|^2 / 2) cf_rV_kernel w theta. *)
Lemma integral_cf_rV_kernel_gauss (s : R) w th :
  \int[gauss m]_g cf_rV_kernel (w + s *: g) th =
  expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_kernel w th.
Proof.
set a := cf_rV_re nu th; set b := cf_rV_im nu th.
pose A := a * cos (mxdot th w) + b * sin (mxdot th w).
pose B := b * cos (mxdot th w) - a * sin (mxdot th w).
have mY : measurable_fun [set: 'rV[R]_m] (fun g => mxdot g (s *: th)).
  exact: measurable_mxdot.
have E g : cf_rV_kernel (w + s *: g) th =
    A * cos (mxdot g (s *: th)) + B * sin (mxdot g (s *: th)).
  rewrite /cf_rV_kernel -/a -/b.
  have -> : mxdot th (w + s *: g) = mxdot th w + mxdot g (s *: th).
    by rewrite mxdotDr !mxdotZr (mxdotC th g).
  by rewrite cosD sinD /A /B; ring.
under eq_Rintegral do rewrite E.
have iA : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun g => A * cos (mxdot g (s *: th)))).
  have mA : measurable_fun [set: 'rV[R]_m]
      (fun g => A * cos (mxdot g (s *: th))).
    by apply: measurable_funM => //; exact: measurable_cos_comp.
  have bA g : `|A * cos (mxdot g (s *: th))| <= `|A|.
    by rewrite normrM ler_piMr// cos_max.
  exact: (bounded_integrable (gauss m) mA bA).
have iB : (gauss m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun g => B * sin (mxdot g (s *: th)))).
  have mB : measurable_fun [set: 'rV[R]_m]
      (fun g => B * sin (mxdot g (s *: th))).
    by apply: measurable_funM => //; exact: measurable_sin_comp.
  have bB g : `|B * sin (mxdot g (s *: th))| <= `|B|.
    by rewrite normrM ler_piMr// sin_max.
  exact: (bounded_integrable (gauss m) mB bB).
rewrite RintegralD.
- exact: measurableT.
- exact: iA.
- exact: iB.
rewrite RintegralZl.
- exact: measurableT.
- exact: integrable_cos_comp.
rewrite RintegralZl.
- exact: measurableT.
- exact: integrable_sin_comp.
have := cf_rV_gauss (s *: th); rewrite /cf_rV /cf_rV_re /cf_rV_im.
move=> [-> ->]; rewrite mulr0 addr0 mxdotZl mxdotZr.
by rewrite /cf_rV_kernel /A -/a -/b mulrC; congr (expR _ * _); ring.
Qed.

(* Convolution: the density at w + s G, averaged over G of law gauss m, is
   the regularized density at w. *)
Lemma integral_cf_rV_density_gauss (s : R) w :
  \int[gauss m]_g cf_rV_density (w + s *: g) = cf_rV_density_reg s w.
Proof.
pose F (p : 'rV[R]_m * 'rV[R]_m) := cf_rV_kernel (w + s *: p.1) p.2.
have mws : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
    (fun p : 'rV[R]_m * 'rV[R]_m => w + s *: p.1).
  apply: measurable_addmx; first exact: measurable_cst.
  apply: measurable_scalemx; first exact: measurable_cst.
  exact: measurable_fst.
have mF : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] F.
  apply: measurable_funD; apply: measurable_funM.
  - apply: measurable_cos_comp.
    exact: measurable_mxdot2 measurable_snd mws.
  - exact: measurableT_comp (measurable_cf_rV_re nu) measurable_snd.
  - apply: measurable_sin_comp.
    exact: measurable_mxdot2 measurable_snd mws.
  - exact: measurableT_comp (measurable_cf_rV_im nu) measurable_snd.
have Fg g th : `|F (g, th)| <= cf_rV_norm nu th := cf_rV_kernel_le _ _.
have iF g : (lebesgue_rV m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun th => F (g, th))).
  exact: (integrable_cf_rV_kernel (w + s *: g)).
have iaF g : (lebesgue_rV m).-integrable [set: 'rV[R]_m]
    (EFin \o (fun th => `|F (g, th)|)).
  apply: (le_integrable measurableT _ _ integrable_cf_rV_norm).
    apply/measurable_EFinP; apply: measurableT_comp => //.
    exact: (measurable_cf_rV_kernel (w + s *: g)).
  move=> th _; rewrite /comp !abse_EFin normr_id lee_fin.
  by rewrite (ger0_norm (cf_rV_norm_ge0 nu th)); exact: Fg.
have bnd g : `|\int[lebesgue_rV m]_th F (g, th)| <=
    \int[lebesgue_rV m]_th cf_rV_norm nu th.
  apply: le_trans (le_normr_Rintegral measurableT (iF g)) _.
  by apply: le_Rintegral => //; exact: integrable_cf_rV_norm.
have mI := measurable_Rintegral1 (gauss m) mF integrable_cf_rV_norm Fg.
transitivity (\int[gauss m]_g ((2 * pi) ^- m *
    \int[lebesgue_rV m]_th F (g, th))).
  by apply: eq_Rintegral => g _.
rewrite RintegralZl.
- exact: measurableT.
- exact: (bounded_integrable (gauss m) mI bnd).
rewrite (Rintegral_fubini (gauss m) mF integrable_cf_rV_norm Fg).
rewrite /cf_rV_density_reg; congr (_ * _).
by apply: eq_Rintegral => th _; exact: integral_cf_rV_kernel_gauss.
Qed.

(* The density is nonnegative, as a limit of the densities of Y + s G. *)
Lemma cf_rV_density_ge0 w : 0 <= cf_rV_density w.
Proof.
have H := cvg_at_right_filter (@cvg_cf_rV_density_reg w).
apply: (cvgr_to_ge H).
near=> s.
have s0 : 0 < s by near: s; exact: nbhs_right_gt.
rewrite cf_rV_density_regE//.
apply: mulr_ge0; first by rewrite invr_ge0 exprn_ge0// ltW.
by apply: Rintegral_ge0 => y _; exact: gauss_pdf_ge0.
Unshelve. all: by end_near.
Qed.

Lemma measurable_cf_rV_density :
  measurable_fun [set: 'rV[R]_m] cf_rV_density.
Proof. exact: continuous_measurable_mx continuous_cf_rV_density. Qed.

(* The density has integral one. *)
Lemma integral_cf_rV_density :
  (\int[lebesgue_rV m]_w (cf_rV_density w)%:E = 1)%E.
Proof.
have mf := measurable_cf_rV_density.
have mpdf := @measurable_gauss_pdf R m.
pose c : R := Num.sqrt (2 * pi) ^- m.
have pdf_le (x : 'rV[R]_m) : `|gauss_pdf x| <= c.
  rewrite ger0_norm ?gauss_pdf_ge0// /gauss_pdf -/c -[leRHS]mulr1.
  apply: ler_wpM2l; first by rewrite invr_ge0 exprn_ge0// sqrtr_ge0.
  rewrite -[leRHS]expR0 ler_expR mulNr oppr_le0 divr_ge0//.
  exact: mxdot_ge0.
pose p (w : 'rV[R]_m) := cf_rV_density_reg 1 w.
have pE w : p w = \int[nu]_y gauss_pdf (w - y).
  rewrite /p cf_rV_density_regE//.
  have -> : (1 : R) ^- m = 1 by rewrite expr1n invr1.
  rewrite mul1r.
  by apply: eq_Rintegral => y _; rewrite invr1 scale1r.
have msub : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
    (fun q : 'rV[R]_m * 'rV[R]_m => q.2 - q.1).
  apply/measurable_fun_mxP => i j.
  rewrite (_ : (fun q => _) =
      (fun q : 'rV[R]_m * 'rV[R]_m => q.2 i j - q.1 i j)).
    by apply/funext => q; rewrite !mxE.
  apply: measurable_funB.
  - exact: measurableT_comp (measurable_mxentry i j) measurable_snd.
  - exact: measurableT_comp (measurable_mxentry i j) measurable_fst.
have I1 : (\int[lebesgue_rV m]_w (p w)%:E = 1)%E.
  pose K (q : 'rV[R]_m * 'rV[R]_m) := (gauss_pdf (q.2 - q.1))%:E.
  have mK : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] K.
    by apply/measurable_EFinP; exact: measurableT_comp mpdf msub.
  have K0 q : (0 <= K q)%E by rewrite lee_fin gauss_pdf_ge0.
  transitivity (\int[lebesgue_rV m]_w \int[nu]_y K (y, w))%E.
    apply: eq_integral => w _; rewrite pE.
    have my : measurable_fun [set: 'rV[R]_m] (fun y => gauss_pdf (w - y)).
      exact: measurableT_comp mpdf (measurable_rV_subl w).
    by rewrite (EFin_Rintegral_bounded nu my (fun y => pdf_le _)).
  rewrite -(fubini_tonelli K mK K0).
  transitivity (\int[nu]_y (1 : \bar R))%E.
    apply: eq_integral => y _.
    have mpdfE : measurable_fun [set: 'rV[R]_m] (fun x => (gauss_pdf x)%:E).
      by apply/measurable_EFinP.
    have pdf0 (x : 'rV[R]_m) : (0 <= (gauss_pdf x)%:E)%E.
      by rewrite lee_fin gauss_pdf_ge0.
    transitivity (\int[lebesgue_rV m]_x (gauss_pdf (x + - y))%:E)%E.
      by apply: eq_integral.
    rewrite (ge0_integral_lebesgue_rV_shift (- y) mpdfE pdf0).
    rewrite -(gauss_lebesgue_rV measurableT).
    exact: probability_setT.
  rewrite integral_cst// mul1e; exact: probability_setT.
have f0 := cf_rV_density_ge0.
have fle w : `|cf_rV_density w| <=
    (2 * pi) ^- m * \int[lebesgue_rV m]_th cf_rV_norm nu th.
  exact: cf_rV_density_le.
have I2 : (\int[lebesgue_rV m]_w (p w)%:E =
    \int[lebesgue_rV m]_w (cf_rV_density w)%:E)%E.
  have pE2 w : p w = \int[gauss m]_g cf_rV_density (w + g).
    rewrite /p -integral_cf_rV_density_gauss.
    by apply: eq_Rintegral => g _; rewrite scale1r.
  pose H (q : 'rV[R]_m * 'rV[R]_m) := (cf_rV_density (q.2 + q.1))%:E.
  have madd : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
      (fun q : 'rV[R]_m * 'rV[R]_m => q.2 + q.1).
    by apply: measurable_addmx; [exact: measurable_snd|exact: measurable_fst].
  have mH : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] H.
    by apply/measurable_EFinP; exact: measurableT_comp mf madd.
  have H0 q : (0 <= H q)%E by rewrite lee_fin f0.
  transitivity (\int[lebesgue_rV m]_w \int[gauss m]_g H (g, w))%E.
    apply: eq_integral => w _; rewrite pE2.
    have mg : measurable_fun [set: 'rV[R]_m] (fun g => cf_rV_density (w + g)).
      apply: measurableT_comp mf _.
      by apply: measurable_addmx; [exact: measurable_cst|exact: measurable_id].
    by rewrite (EFin_Rintegral_bounded (gauss m) mg (fun g => fle _)).
  rewrite -(fubini_tonelli H mH H0).
  transitivity (\int[gauss m]_g
      (\int[lebesgue_rV m]_w (cf_rV_density w)%:E))%E.
    apply: eq_integral => g _.
    have mfE : measurable_fun [set: 'rV[R]_m] (fun w => (cf_rV_density w)%:E).
      by apply/measurable_EFinP.
    have fE0 w : (0 <= (cf_rV_density w)%:E)%E by rewrite lee_fin f0.
    transitivity (\int[lebesgue_rV m]_w (cf_rV_density (w + g))%:E)%E.
      by apply: eq_integral.
    exact: (ge0_integral_lebesgue_rV_shift g mfE fE0).
  rewrite integral_cst// -[RHS]mule1; congr (_ * _)%E.
  exact: probability_setT.
by rewrite -I2 I1.
Qed.


(* The law with density cf_rV_density with respect to lebesgue_rV m; the
   proof h of the integrability of |cf nu| makes it a probability. *)
Definition cf_rV_inv_prob
    (h : (\int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E < +oo)%E) :
    set 'rV[R]_m -> \bar R :=
  fun A => (\int[lebesgue_rV m]_(w in A) (cf_rV_density w)%:E)%E.

End cf_rV_density.

Section cf_rV_inv_prob.
Context {R : realType} {m : nat} (nu : probability 'rV[R]_m R).
Variable h : (\int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E < +oo)%E.

Lemma cf_rV_inv_prob0 : cf_rV_inv_prob h set0 = 0%E.
Proof. by rewrite /cf_rV_inv_prob integral_set0. Qed.

Lemma cf_rV_inv_prob_ge0 A : (0 <= cf_rV_inv_prob h A)%E.
Proof.
by apply: integral_ge0 => w _; rewrite lee_fin (cf_rV_density_ge0 h).
Qed.

Lemma cf_rV_inv_prob_sigma : semi_sigma_additive (cf_rV_inv_prob h).
Proof.
apply: semi_sigma_additive_nng_induced.
- by apply/measurable_EFinP; exact: (measurable_cf_rV_density h).
- by move=> w; rewrite lee_fin (cf_rV_density_ge0 h).
Qed.

Lemma cf_rV_inv_prob_setT : cf_rV_inv_prob h [set: 'rV[R]_m] = 1%E.
Proof. exact: (integral_cf_rV_density h). Qed.

End cf_rV_inv_prob.

(* HB declares canonical projections that the structures of the measure
   already provide; the warning says so. The setting lasts until the end of
   this file and is not exported. *)
Set Warnings "-redundant-canonical-projection".

HB.instance Definition _ (R : realType) (m : nat)
    (nu : probability 'rV[R]_m R)
    (h : (\int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E < +oo)%E) :=
  isMeasure.Build _ _ _ (@cf_rV_inv_prob R m nu h)
    (@cf_rV_inv_prob0 R m nu h) (@cf_rV_inv_prob_ge0 R m nu h)
    (@cf_rV_inv_prob_sigma R m nu h).

HB.instance Definition _ (R : realType) (m : nat)
    (nu : probability 'rV[R]_m R)
    (h : (\int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E < +oo)%E) :=
  Measure_isProbability.Build _ _ _ (@cf_rV_inv_prob R m nu h)
    (@cf_rV_inv_prob_setT R m nu h).


Section add_gauss.
Context {R : realType} {m : nat}.

Let measurable_mxdot_self :
  measurable_fun [set: 'rV[R]_m] (fun x => mxdot x x).
Proof.
apply: measurable_sum => i; apply: measurable_sum => j.
by apply: measurable_funM; exact: measurable_mxentry.
Qed.

Let measurable_rV_subl (w : 'rV[R]_m) :
  measurable_fun [set: 'rV[R]_m] (fun y : 'rV[R]_m => w - y).
Proof.
apply/measurable_fun_mxP => i j.
rewrite (_ : (fun y : 'rV[R]_m => (w - y) i j) =
    (fun y : 'rV[R]_m => w i j - y i j)).
  by apply/funext => y; rewrite !mxE.
by apply: measurable_funB; [exact: measurable_cst|exact: measurable_mxentry].
Qed.

Let msub2 : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
  (fun q : 'rV[R]_m * 'rV[R]_m => q.2 - q.1).
Proof.
apply/measurable_fun_mxP => i j.
rewrite (_ : (fun q => _) =
    (fun q : 'rV[R]_m * 'rV[R]_m => q.2 i j - q.1 i j)).
  by apply/funext => q; rewrite !mxE.
apply: measurable_funB.
- exact: measurableT_comp (measurable_mxentry i j) measurable_snd.
- exact: measurableT_comp (measurable_mxentry i j) measurable_fst.
Qed.

Let pdf_le2 (x : 'rV[R]_m) : `|gauss_pdf x| <= Num.sqrt (2 * pi) ^- m.
Proof.
rewrite ger0_norm ?gauss_pdf_ge0// /gauss_pdf -[leRHS]mulr1.
apply: ler_wpM2l; first by rewrite invr_ge0 exprn_ge0// sqrtr_ge0.
rewrite -[leRHS]expR0 ler_expR mulNr oppr_le0 divr_ge0//.
exact: mxdot_ge0.
Qed.

(* For Y of law mu and G of law gauss m, independent, and s > 0, the law
   of Y + s G has the density w |-> s^-m E[gauss_pdf ((w - Y) / s)]. *)
Lemma integral_add_gauss (mu : probability 'rV[R]_m R)
    (phi : 'rV[R]_m -> R) (s : R) :
  0 < s -> measurable_fun [set: 'rV[R]_m] phi -> (forall x, 0 <= phi x) ->
  (\int[mu]_y \int[gauss m]_g (phi (y + s *: g))%:E =
   (s ^- m)%:E * \int[lebesgue_rV m]_w
     ((phi w)%:E * (\int[mu]_y gauss_pdf (s^-1 *: (w - y)))%:E))%E.
Proof.
move=> s0 mphi phi0.
have mpE : measurable_fun [set: 'rV[R]_m] (fun w => (phi w)%:E).
  by apply/measurable_EFinP.
have p0 w : (0 <= (phi w)%:E)%E by rewrite lee_fin.
have mpdf := @measurable_gauss_pdf R m.
have msc := measurable_rV_scale (n := m) s^-1.
pose K (q : 'rV[R]_m * 'rV[R]_m) :=
  ((phi q.2)%:E * (gauss_pdf (s^-1 *: (q.2 - q.1)))%:E)%E.
have mK : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] K.
  apply: emeasurable_funM.
    by apply/measurable_EFinP; exact: measurableT_comp mphi measurable_snd.
  apply/measurable_EFinP; apply: measurableT_comp mpdf _.
  exact: measurableT_comp msc msub2.
have K0 q : (0 <= K q)%E by rewrite mule_ge0// lee_fin gauss_pdf_ge0.
transitivity (\int[mu]_y ((s ^- m)%:E *
    \int[lebesgue_rV m]_w K (y, w)))%E.
  apply: eq_integral => y _.
  exact: (ge0_integral_gauss_affine y s0 mpE p0).
rewrite ge0_integralZl_EFin.
- exact: measurableT.
- by move=> y _; apply: integral_ge0 => w _; exact: K0.
- exact: (measurable_fun_fubini_tonelli_F K mK K0).
- by rewrite invr_ge0 exprn_ge0// ltW.
apply: (congr1 (fun X => ((s ^- m)%:E * X)%E)).
rewrite (fubini_tonelli K mK K0).
apply: eq_integral => w _.
have my : measurable_fun [set: 'rV[R]_m]
    (fun y => gauss_pdf (s^-1 *: (w - y))).
  apply: measurableT_comp mpdf _.
  exact: measurableT_comp msc (measurable_rV_subl w).
rewrite (EFin_Rintegral_bounded mu my (fun y => pdf_le2 _)).
rewrite -ge0_integralZl_EFin.
- exact: measurableT.
- by move=> y _; rewrite lee_fin gauss_pdf_ge0.
- by apply/measurable_EFinP.
- exact: phi0.
by apply: eq_integral => y _.
Qed.

(* For a law mu, s > 0 and phi with values in [0, 1] and Lipschitz with
   constant L: |E[phi (Y + s G)] - E[phi Y]| <= |L| s (1 + m) / 2. *)
Lemma lipschitz_add_gauss (mu : probability 'rV[R]_m R)
    (phi : 'rV[R]_m -> R) (L s : R) :
  0 < s -> (forall x, 0 <= phi x <= 1) ->
  (forall x y, `|phi x - phi y| <= L * frobenius (x - y)) ->
  `|\int[mu]_y \int[gauss m]_g phi (y + s *: g) - \int[mu]_y phi y| <=
  `|L| * s * (1 + m%:R) / 2.
Proof.
move=> s0 phi01 phiL.
have mphi : measurable_fun [set: 'rV[R]_m] phi.
  exact: continuous_measurable_mx (lipschitz_frobenius_continuous phiL).
have phi1 x : `|phi x| <= 1.
  by have /andP[h0 h1] := phi01 x; rewrite ger0_norm.
have maff y : measurable_fun [set: 'rV[R]_m] (fun g : 'rV[R]_m => y + s *: g).
  apply: measurable_addmx; first exact: measurable_cst.
  exact: measurable_rV_scale.
have mFy y : measurable_fun [set: 'rV[R]_m] (fun g => phi (y + s *: g)).
  exact: measurableT_comp mphi (maff y).
pose K : R := `|L| * s / 2.
have K0 : 0 <= K by rewrite divr_ge0// mulr_ge0// ltW.
have inner y : `|\int[gauss m]_g phi (y + s *: g) - phi y| <=
    `|L| * s * (1 + m%:R) / 2.
  have iFy := bounded_integrable (gauss m) (mFy y) (fun g => phi1 _).
  have icst : (gauss m).-integrable [set: 'rV[R]_m]
      (EFin \o (fun _ : 'rV[R]_m => phi y)).
    exact: (bounded_integrable (gauss m) (measurable_cst _) (fun _ => phi1 y)).
  have -> : \int[gauss m]_g phi (y + s *: g) - phi y =
      \int[gauss m]_g (phi (y + s *: g) - phi y).
    rewrite RintegralB.
    - exact: measurableT.
    - exact: iFy.
    - exact: icst.
    by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
  have mD : measurable_fun [set: 'rV[R]_m]
      (fun g => phi (y + s *: g) - phi y).
    by apply: measurable_funB => //; exact: mFy.
  have D1 g : `|phi (y + s *: g) - phi y| <= 2.
    by rewrite (le_trans (ler_normB _ _))// -(@natr1 R 1) lerD.
  apply: le_trans (le_normr_Rintegral measurableT
    (bounded_integrable (gauss m) mD D1)) _.
  have mA : measurable_fun [set: 'rV[R]_m]
      (fun g => `|phi (y + s *: g) - phi y|).
    exact: measurableT_comp mD.
  have A2 g : `| `|phi (y + s *: g) - phi y| | <= 2 by rewrite normr_id.
  rewrite -lee_fin (EFin_Rintegral_bounded (gauss m) mA A2).
  have mxx : measurable_fun [set: 'rV[R]_m] (fun g : 'rV[R]_m => mxdot g g).
    exact: measurable_mxdot_self.
  apply: (@le_trans _ _
    (\int[gauss m]_g (K * (1 + mxdot g g))%:E)%E).
    apply: ge0_le_integral.
    - exact: measurableT.
    - by move=> g _; rewrite lee_fin.
    - by apply/measurable_EFinP.
    - apply/measurable_EFinP; apply: measurable_funM => //.
      by apply: measurable_funD => //.
    move=> g _; rewrite lee_fin.
    apply: le_trans (phiL _ _) _.
    have -> : y + s *: g - y = s *: g by rewrite addrC addKr.
    rewrite frobeniusZ gtr0_norm//.
    apply: (@le_trans _ _ (`|L| * (s * frobenius g))).
      apply: ler_wpM2r; last exact: ler_norm.
      by rewrite mulr_ge0 ?frobenius_ge0 ?ltW.
    have hg : frobenius g <= (1 + mxdot g g) / 2.
      rewrite -frobenius_sqr; have := frobenius_ge0 g.
      by move: (frobenius g) => a a0; have := sqr_ge0 (a - 1); nra.
    rewrite /K (_ : `|L| * s / 2 * (1 + mxdot g g) =
        `|L| * (s * ((1 + mxdot g g) / 2))); first by ring.
    apply: ler_wpM2l; first exact: normr_ge0.
    by apply: ler_wpM2l; [exact: ltW|exact: hg].
  under eq_integral do rewrite EFinM.
  rewrite ge0_integralZl_EFin.
  - exact: measurableT.
  - by move=> g _; rewrite lee_fin addr_ge0// mxdot_ge0.
  - by apply/measurable_EFinP; apply: measurable_funD.
  - exact: K0.
  under eq_integral do rewrite EFinD.
  rewrite ge0_integralD.
  - exact: measurableT.
  - by move=> g _; rewrite lee_fin.
  - exact: measurable_cst.
  - by move=> g _; rewrite lee_fin mxdot_ge0.
  - by apply/measurable_EFinP.
  have I1 : (\int[gauss m]_g (1%:E : \bar R) = 1)%E.
    by rewrite integral_cst// mul1e; exact: probability_setT.
  rewrite I1 integral_gauss_mxdot_self -EFinD -EFinM lee_fin /K.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
have mI : measurable_fun [set: 'rV[R]_m]
    (fun y => \int[gauss m]_g phi (y + s *: g)).
  pose F (p : 'rV[R]_m * 'rV[R]_m) := phi (p.1 + s *: p.2).
  have mF : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] F.
    apply: measurableT_comp mphi _.
    apply: measurable_addmx; first exact: measurable_fst.
    apply: measurable_scalemx; first exact: measurable_cst.
    exact: measurable_snd.
  have i1 : (gauss m).-integrable [set: 'rV[R]_m]
      (EFin \o (fun _ : 'rV[R]_m => (1 : R))).
    exact: finite_measure_integrable_cst.
  exact: (measurable_Rintegral1 mu mF i1 (fun y g => phi1 _)).
have I1b y : `|\int[gauss m]_g phi (y + s *: g)| <= 1.
  rewrite ger0_norm.
    by apply: Rintegral_ge0 => g _; case/andP: (phi01 (y + s *: g)).
  apply: (@le_trans _ _ (\int[gauss m]_g (1 : R))).
    apply: le_Rintegral.
    - exact: measurableT.
    - exact: (bounded_integrable (gauss m) (mFy y) (fun g => phi1 _)).
    - exact: finite_measure_integrable_cst.
    - by move=> g _; case/andP: (phi01 (y + s *: g)).
  by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
have iI := bounded_integrable mu mI I1b.
have iphi := bounded_integrable mu mphi phi1.
rewrite -RintegralB.
- exact: measurableT.
- exact: iI.
- exact: iphi.
have mdiff : measurable_fun [set: 'rV[R]_m]
    (fun y => \int[gauss m]_g phi (y + s *: g) - phi y).
  exact: measurable_funB.
have diff2 y : `|\int[gauss m]_g phi (y + s *: g) - phi y| <= 2.
  by rewrite (le_trans (ler_normB _ _))// -(@natr1 R 1) lerD.
apply: le_trans (le_normr_Rintegral measurableT
  (bounded_integrable mu mdiff diff2)) _.
apply: (@le_trans _ _ (\int[mu]_y (`|L| * s * (1 + m%:R) / 2))).
  apply: le_Rintegral.
  - exact: measurableT.
  - have mA : measurable_fun [set: 'rV[R]_m]
        (fun y => `|\int[gauss m]_g phi (y + s *: g) - phi y|).
      exact: measurableT_comp mdiff.
    have A2 y : `| `|\int[gauss m]_g phi (y + s *: g) - phi y| | <= 2.
      by rewrite normr_id.
    exact: (bounded_integrable mu mA A2).
  - exact: finite_measure_integrable_cst.
  - by move=> y _; exact: inner.
by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
Qed.

End add_gauss.

Section cf_rV_inversion.
Context {R : realType} {m : nat}.
Variable nu : probability 'rV[R]_m R.
Hypothesis int_cf :
  (\int[lebesgue_rV m]_th (cf_rV_norm nu th)%:E < +oo)%E.

Local Notation P := (cf_rV_inv_prob int_cf).

Let measurable_rV_subl (w : 'rV[R]_m) :
  measurable_fun [set: 'rV[R]_m] (fun y : 'rV[R]_m => w - y).
Proof.
apply/measurable_fun_mxP => i j.
rewrite (_ : (fun y : 'rV[R]_m => (w - y) i j) =
    (fun y : 'rV[R]_m => w i j - y i j)).
  by apply/funext => y; rewrite !mxE.
by apply: measurable_funB; [exact: measurable_cst|exact: measurable_mxentry].
Qed.

(* The law with density cf_rV_density nu is absolutely continuous with respect
   to lebesgue_rV m, and integrals against it carry the density. *)
Lemma cf_rV_inv_prob_dominates : P `<< lebesgue_rV m.
Proof.
apply/null_content_dominatesP => A mA A0.
rewrite /cf_rV_inv_prob null_set_integral//.
apply/measurable_EFinP; apply: measurable_funTS.
exact: (measurable_cf_rV_density int_cf).
Qed.

Let RN_density : ae_eq (lebesgue_rV m) [set: 'rV[R]_m]
  (Radon_Nikodym_SigmaFinite.f P (lebesgue_rV m))
  (fun w => (cf_rV_density nu w)%:E).
Proof.
have mf : measurable_fun [set: 'rV[R]_m] (fun w => (cf_rV_density nu w)%:E).
  by apply/measurable_EFinP; exact: (measurable_cf_rV_density int_cf).
apply: integral_ae_eq => //.
- exact: Radon_Nikodym_SigmaFinite.f_integrable cf_rV_inv_prob_dominates.
- move=> E _ mE.
  by rewrite -(Radon_Nikodym_SigmaFinite.f_integral
    cf_rV_inv_prob_dominates mE).
Qed.

Lemma ge0_integral_cf_rV_inv_prob (g : 'rV[R]_m -> \bar R) :
  measurable_fun [set: 'rV[R]_m] g -> (forall x, 0 <= g x)%E ->
  (\int[P]_x g x = \int[lebesgue_rV m]_x (g x * (cf_rV_density nu x)%:E))%E.
Proof.
move=> mg g0.
rewrite -(Radon_Nikodym_SigmaFinite.change_of_variables
  cf_rV_inv_prob_dominates g0 measurableT mg).
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //.
  exact: measurable_int
    (Radon_Nikodym_SigmaFinite.f_integrable cf_rV_inv_prob_dominates).
- apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: (measurable_cf_rV_density int_cf).
- exact: ae_eqe_mul2l RN_density.
Qed.

(* The densities of Y + s G for Y of law nu and for Y of law P coincide. *)
Lemma integral_gauss_pdf_inv_prob (s : R) w : 0 < s ->
  \int[P]_y gauss_pdf (s^-1 *: (w - y)) =
  \int[nu]_y gauss_pdf (s^-1 *: (w - y)).
Proof.
move=> s0; have sn0 : s != 0 by rewrite gt_eqF.
have sm0 : s ^+ m != 0 by rewrite expf_neq0.
have Enu : \int[nu]_y gauss_pdf (s^-1 *: (w - y)) =
    s ^+ m * cf_rV_density_reg nu s w.
  by rewrite (cf_rV_density_regE int_cf)// mulrA mulfV// mul1r.
rewrite Enu.
have mpdf := @measurable_gauss_pdf R m.
have msc := measurable_rV_scale (n := m) s^-1.
have mf := (measurable_cf_rV_density int_cf).
have mfE : measurable_fun [set: 'rV[R]_m] (fun v => (cf_rV_density nu v)%:E).
  by apply/measurable_EFinP.
have fE0 v : (0 <= (cf_rV_density nu v)%:E)%E.
  by rewrite lee_fin (cf_rV_density_ge0 int_cf).
have fle v : `|cf_rV_density nu v| <=
    (2 * pi) ^- m * \int[lebesgue_rV m]_th cf_rV_norm nu th.
  exact: (cf_rV_density_le int_cf).
have E1 : (\int[P]_y (gauss_pdf (s^-1 *: (w - y)))%:E =
    \int[lebesgue_rV m]_v ((cf_rV_density nu v)%:E *
      (gauss_pdf (s^-1 *: (v - w)))%:E))%E.
  rewrite ge0_integral_cf_rV_inv_prob.
  - apply/measurable_EFinP; apply: measurableT_comp mpdf _.
    exact: measurableT_comp msc (measurable_rV_subl w).
  - by move=> y; rewrite lee_fin gauss_pdf_ge0.
  apply: eq_integral => v _; rewrite muleC; congr (_ * _%:E)%E.
  by rewrite /gauss_pdf -opprB scalerN mxdotNl mxdotNr opprK.
have E2 := ge0_integral_gauss_affine w s0 mfE fE0.
have mg : measurable_fun [set: 'rV[R]_m]
    (fun g => cf_rV_density nu (w + s *: g)).
  apply: measurableT_comp mf _.
  apply: measurable_addmx; first exact: measurable_cst.
  exact: measurable_rV_scale.
have E3 : (\int[gauss m]_g (cf_rV_density nu (w + s *: g))%:E =
    (cf_rV_density_reg nu s w)%:E)%E.
  rewrite -(EFin_Rintegral_bounded (gauss m) mg (fun g => fle _)).
  by rewrite (integral_cf_rV_density_gauss int_cf).
have E4 : (\int[lebesgue_rV m]_v ((cf_rV_density nu v)%:E *
      (gauss_pdf (s^-1 *: (v - w)))%:E) =
    (s ^+ m * cf_rV_density_reg nu s w)%:E)%E.
  rewrite E3 in E2.
  by rewrite EFinM E2 muleA -EFinM mulfV// mul1e.
transitivity (fine (\int[P]_y (gauss_pdf (s^-1 *: (w - y)))%:E)).
  by [].
by rewrite E1 E4.
Qed.

Let smooth_EFin (mu : probability 'rV[R]_m R) (Phi : 'rV[R]_m -> R) (s : R) :
  0 < s -> (forall x, 0 <= Phi x <= 1) -> measurable_fun [set: 'rV[R]_m] Phi ->
  (\int[mu]_y \int[gauss m]_g Phi (y + s *: g))%:E =
  ((s ^- m)%:E * \int[lebesgue_rV m]_w
    ((Phi w)%:E * (\int[mu]_y gauss_pdf (s^-1 *: (w - y)))%:E))%E.
Proof.
move=> s0 Phi01 mPhi.
have Phi1 x : `|Phi x| <= 1 by have /andP[h0 h1] := Phi01 x; rewrite ger0_norm.
have maff y : measurable_fun [set: 'rV[R]_m] (fun g : 'rV[R]_m => y + s *: g).
  apply: measurable_addmx; first exact: measurable_cst.
  exact: measurable_rV_scale.
have mFy y : measurable_fun [set: 'rV[R]_m] (fun g => Phi (y + s *: g)).
  exact: measurableT_comp mPhi (maff y).
have mI : measurable_fun [set: 'rV[R]_m]
    (fun y => \int[gauss m]_g Phi (y + s *: g)).
  pose F (p : 'rV[R]_m * 'rV[R]_m) := Phi (p.1 + s *: p.2).
  have mF : measurable_fun [set: 'rV[R]_m * 'rV[R]_m] F.
    apply: measurableT_comp mPhi _.
    apply: measurable_addmx; first exact: measurable_fst.
    apply: measurable_scalemx; first exact: measurable_cst.
    exact: measurable_snd.
  have i1 : (gauss m).-integrable [set: 'rV[R]_m]
      (EFin \o (fun _ : 'rV[R]_m => (1 : R))).
    exact: finite_measure_integrable_cst.
  exact: (measurable_Rintegral1 mu mF i1 (fun y g => Phi1 _)).
have I1 y : `|\int[gauss m]_g Phi (y + s *: g)| <= 1.
  rewrite ger0_norm.
    by apply: Rintegral_ge0 => g _; case/andP: (Phi01 (y + s *: g)).
  apply: (@le_trans _ _ (\int[gauss m]_g (1 : R))).
    apply: le_Rintegral.
    - exact: measurableT.
    - exact: (bounded_integrable (gauss m) (mFy y) (fun g => Phi1 _)).
    - exact: finite_measure_integrable_cst.
    - by move=> g _; case/andP: (Phi01 (y + s *: g)).
  by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
rewrite (EFin_Rintegral_bounded mu mI I1).
transitivity (\int[mu]_y \int[gauss m]_g (Phi (y + s *: g))%:E)%E.
  apply: eq_integral => y _.
  exact: (EFin_Rintegral_bounded (gauss m) (mFy y) (fun g => Phi1 _)).
apply: integral_add_gauss => //.
by move=> x; case/andP: (Phi01 x).
Qed.

(* The inversion theorem: if |cf nu| is integrable with respect to Lebesgue
   measure, then nu has the density cf_rV_density nu. *)
Theorem cf_rV_inversion (X : set 'rV[R]_m) : measurable X ->
  nu X = (\int[lebesgue_rV m]_(w in X) (cf_rV_density nu w)%:E)%E.
Proof.
move=> mX.
have -> : (\int[lebesgue_rV m]_(w in X) (cf_rV_density nu w)%:E)%E = P X by [].
apply: measure_lipschitz_unique => //.
  by apply: le_lt_trans (probability_le1 nu measurableT) _; exact: ltry.
move=> Phi L Phi01 PhiL.
have mPhi : measurable_fun [set: 'rV[R]_m] Phi.
  exact: continuous_measurable_mx (lipschitz_frobenius_continuous PhiL).
have Phi1 x : `|Phi x| <= 1.
  by have /andP[h0 h1] := Phi01 x; rewrite ger0_norm.
rewrite -(EFin_Rintegral_bounded nu mPhi Phi1).
rewrite -(EFin_Rintegral_bounded P mPhi Phi1).
apply: (congr1 EFin).
have key s : 0 < s -> \int[nu]_y \int[gauss m]_g Phi (y + s *: g) =
    \int[P]_y \int[gauss m]_g Phi (y + s *: g).
  move=> s0.
  suff : (\int[nu]_y \int[gauss m]_g Phi (y + s *: g))%:E =
      (\int[P]_y \int[gauss m]_g Phi (y + s *: g))%:E by move=> [].
  rewrite !smooth_EFin//.
  apply: (congr1 (fun Z => ((s ^- m)%:E * Z)%E)).
  apply: eq_integral => w _.
  by rewrite (integral_gauss_pdf_inv_prob w s0).
have hb s : 0 < s ->
    `|\int[nu]_y Phi y - \int[P]_y Phi y| <= `|L| * s * (1 + m%:R).
  move=> s0.
  have h1 := lipschitz_add_gauss nu s0 Phi01 PhiL.
  have h2 := lipschitz_add_gauss P s0 Phi01 PhiL.
  rewrite (key s s0) in h1.
  move: h1 h2; set x := \int[P]_y _; set a := \int[nu]_y _.
  set b := \int[P]_y _.
  move=> h1 h2.
  have -> : a - b = (x - b) - (x - a) by ring.
  apply: le_trans (ler_normB _ _) _.
  have -> : `|L| * s * (1 + m%:R) =
      `|L| * s * (1 + m%:R) / 2 + `|L| * s * (1 + m%:R) / 2.
    by field.
  exact: lerD h2 h1.
apply/eqP; rewrite -subr_eq0 -normr_le0.
apply/ler_addgt0Pr => e e0; rewrite add0r.
pose c := `|L| * (1 + m%:R).
have c0 : 0 <= c by rewrite mulr_ge0// addr_ge0// ler0n.
have c1 : 0 < c + 1 by rewrite ltr_wpDl.
have es0 : 0 < e / (c + 1) by rewrite divr_gt0.
apply: le_trans (hb _ es0) _.
rewrite (_ : `|L| * (e / (c + 1)) * (1 + m%:R) = e * (c / (c + 1))).
  by rewrite /c; field; rewrite gt_eqF.
apply: ler_piMr; first exact: ltW.
by rewrite ler_pdivrMr// mul1r lerDl ler01.
Qed.

End cf_rV_inversion.
