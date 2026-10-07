From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun.
From mathcomp Require Import exp trigo measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.gaussian Require Import parameter_integral gauss.

(**md**************************************************************************)
(* # Characteristic functions of laws on the real line                        *)
(*                                                                            *)
(* MathComp-Analysis has no complex numbers, so the characteristic function   *)
(* t |-> E[exp (i t X)] of a law mu on R is given by its real part cf_re mu   *)
(* and its imaginary part cf_im mu. A pair z : R * R stands for the complex   *)
(* number z.1 + i z.2: cmul is the complex product and cmod the modulus.      *)
(*                                                                            *)
(* A law nu on R is the image of a probability P on T under a measurable      *)
(* g : T -> R when P (g @^-1` A) = nu A for every measurable A; then          *)
(* cf_re nu t is the integral of cos (t * g x) against P (cf_re_image).       *)
(*                                                                            *)
(* ```                                                                        *)
(*      cmul z w == the complex product of the pairs z and w                  *)
(*        cmod z == the modulus sqrt (z.1 ^ 2 + z.2 ^ 2) of the pair z        *)
(*    cf_re mu t == \int[mu]_x cos (t * x), the real part of the              *)
(*                  characteristic function of the law mu at t                *)
(*    cf_im mu t == \int[mu]_x sin (t * x), its imaginary part                *)
(*       cf mu t == the pair (cf_re mu t, cf_im mu t)                         *)
(*  cf_norm mu t == the modulus of the characteristic function of mu at t     *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section complex_pair.
Context {R : rcfType}.
Implicit Types z w : R * R.

Definition cmul z w : R * R := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1).

Definition cmod z : R := Num.sqrt (z.1 ^+ 2 + z.2 ^+ 2).

Lemma cmulE a b c e : cmul (a, b) (c, e) = (a * c - b * e, a * e + b * c).
Proof. by []. Qed.

Lemma cmulA : associative cmul.
Proof. by move=> [a b] [c e] [f g]; rewrite /cmul /=; congr pair; ring. Qed.

Lemma cmulC : commutative cmul.
Proof. by move=> [a b] [c e]; rewrite /cmul /=; congr pair; ring. Qed.

Lemma cmul1z : left_id (1, 0) cmul.
Proof. by move=> [a b]; rewrite /cmul /=; congr pair; ring. Qed.

Lemma cmod_ge0 z : 0 <= cmod z.
Proof. exact: sqrtr_ge0. Qed.

Lemma cmod1 : cmod (1, 0) = 1.
Proof. by rewrite /cmod /= expr1n expr0n addr0 sqrtr1. Qed.

Lemma cmodM z w : cmod (cmul z w) = cmod z * cmod w.
Proof.
rewrite /cmod -sqrtrM ?addr_ge0 ?sqr_ge0//; congr Num.sqrt.
by rewrite /cmul /=; ring.
Qed.

Lemma cmod_prod I (r : seq I) (P : pred I) (F : I -> R * R) :
  cmod (\big[cmul/(1, 0)]_(i <- r | P i) F i) =
  \prod_(i <- r | P i) cmod (F i).
Proof. exact: (big_morph cmod cmodM cmod1). Qed.

(* For a unit vector (u, v), `|a u + b v| is at most the modulus of (a, b). *)
Lemma cmod_ge_dot a b u v :
  u ^+ 2 + v ^+ 2 = 1 -> `|a * u + b * v| <= cmod (a, b).
Proof.
move=> uv; rewrite /cmod /= -sqrtr_sqr ler_sqrt ?addr_ge0 ?sqr_ge0//.
have : 0 <= (a * v - b * u) ^+ 2 by exact: sqr_ge0.
by rewrite -[a ^+ 2 + b ^+ 2]mulr1 -uv => h; nra.
Qed.

End complex_pair.

Section measurable_trigo.
Context {R : realType}.

Lemma measurable_cos : measurable_fun [set: R] cos.
Proof. apply: continuous_measurable_fun; exact: continuous_cos. Qed.

Lemma measurable_sin : measurable_fun [set: R] sin.
Proof. apply: continuous_measurable_fun; exact: continuous_sin. Qed.

Lemma measurable_cos_comp d (T : measurableType d) (g : T -> R) :
  measurable_fun [set: T] g -> measurable_fun [set: T] (fun x => cos (g x)).
Proof. by move=> mg; apply: measurableT_comp; first exact: measurable_cos. Qed.

Lemma measurable_sin_comp d (T : measurableType d) (g : T -> R) :
  measurable_fun [set: T] g -> measurable_fun [set: T] (fun x => sin (g x)).
Proof. by move=> mg; apply: measurableT_comp; first exact: measurable_sin. Qed.

Lemma measurable_cos_mul d (T : measurableType d) (g : T -> R) (t : R) :
  measurable_fun [set: T] g -> measurable_fun [set: T] (fun x => cos (t * g x)).
Proof. by move=> mg; apply: measurable_cos_comp; exact: measurable_funM. Qed.

Lemma measurable_sin_mul d (T : measurableType d) (g : T -> R) (t : R) :
  measurable_fun [set: T] g -> measurable_fun [set: T] (fun x => sin (t * g x)).
Proof. by move=> mg; apply: measurable_sin_comp; exact: measurable_funM. Qed.

Lemma integrable_cos_comp d (T : measurableType d) (P : probability T R)
    (g : T -> R) : measurable_fun [set: T] g ->
  P.-integrable [set: T] (EFin \o (fun x => cos (g x))).
Proof.
move=> mg; apply: (bounded_integrable P (measurable_cos_comp mg) (C := 1)).
by move=> x; exact: cos_max.
Qed.

Lemma integrable_sin_comp d (T : measurableType d) (P : probability T R)
    (g : T -> R) : measurable_fun [set: T] g ->
  P.-integrable [set: T] (EFin \o (fun x => sin (g x))).
Proof.
move=> mg; apply: (bounded_integrable P (measurable_sin_comp mg) (C := 1)).
by move=> x; exact: sin_max.
Qed.

Lemma integrable_cos_mul d (T : measurableType d) (P : probability T R)
    (g : T -> R) (t : R) : measurable_fun [set: T] g ->
  P.-integrable [set: T] (EFin \o (fun x => cos (t * g x))).
Proof. by move=> mg; apply: integrable_cos_comp; exact: measurable_funM. Qed.

Lemma integrable_sin_mul d (T : measurableType d) (P : probability T R)
    (g : T -> R) (t : R) : measurable_fun [set: T] g ->
  P.-integrable [set: T] (EFin \o (fun x => sin (t * g x))).
Proof. by move=> mg; apply: integrable_sin_comp; exact: measurable_funM. Qed.

(* Integrals of a p cos (g x) + q sin (g x), with constants p and q. *)
Lemma Rintegral_cos_sin d (T : measurableType d) (P : probability T R)
    (g : T -> R) (p q : R) : measurable_fun [set: T] g ->
  \int[P]_x (p * cos (g x) + q * sin (g x)) =
  p * \int[P]_x cos (g x) + q * \int[P]_x sin (g x).
Proof.
move=> mg; have ic := integrable_cos_comp P mg.
have iS := integrable_sin_comp P mg.
rewrite RintegralD// ?RintegralZl//.
- have := integrableZl measurableT p ic.
  by apply: eq_integrable => // x _; rewrite /= EFinM.
- have := integrableZl measurableT q iS.
  by apply: eq_integrable => // x _; rewrite /= EFinM.
Qed.

Lemma RintegralN d (T : measurableType d) (mu : {measure set T -> \bar R})
    (f : T -> R) :
  mu.-integrable [set: T] (EFin \o f) -> \int[mu]_x (- f x) = - \int[mu]_x f x.
Proof.
move=> fi; rewrite -mulN1r -RintegralZl//.
by apply: eq_Rintegral => x _; rewrite mulN1r.
Qed.

End measurable_trigo.

Section charfun.
Context {R : realType}.
Implicit Types (mu : probability R R) (t : R).

Definition cf_re mu t := \int[mu]_x cos (t * x).

Definition cf_im mu t := \int[mu]_x sin (t * x).

Definition cf mu t : R * R := (cf_re mu t, cf_im mu t).

Definition cf_norm mu t := Num.sqrt (cf_re mu t ^+ 2 + cf_im mu t ^+ 2).

Lemma cf_normE mu t : cf_norm mu t = cmod (cf mu t).
Proof. by []. Qed.

Lemma cf_norm_ge0 mu t : 0 <= cf_norm mu t.
Proof. exact: sqrtr_ge0. Qed.

Lemma cf_re0 mu : cf_re mu 0 = 1.
Proof.
rewrite /cf_re; under eq_Rintegral do rewrite mul0r cos0.
by rewrite Rintegral_cst// [X in fine X]probability_setT mul1r.
Qed.

Lemma cf_im0 mu : cf_im mu 0 = 0.
Proof.
rewrite /cf_im; under eq_Rintegral do rewrite mul0r sin0.
by rewrite Rintegral_cst// mul0r.
Qed.

Lemma cf_norm0 mu : cf_norm mu 0 = 1.
Proof. by rewrite /cf_norm cf_re0 cf_im0 expr1n expr0n addr0 sqrtr1. Qed.

Lemma cf_reN mu t : cf_re mu (- t) = cf_re mu t.
Proof. by apply: eq_Rintegral => x _; rewrite mulNr cosN. Qed.

Lemma cf_imN mu t : cf_im mu (- t) = - cf_im mu t.
Proof.
rewrite /cf_im; under eq_Rintegral do rewrite mulNr sinN.
by rewrite RintegralN//; exact: integrable_sin_mul.
Qed.

Lemma cf_normN mu t : cf_norm mu (- t) = cf_norm mu t.
Proof. by rewrite /cf_norm cf_reN cf_imN sqrrN. Qed.

Lemma cf_re_le1 mu t : `|cf_re mu t| <= 1.
Proof.
apply: Rintegral_bounded => [|x]; last exact: cos_max.
exact: measurable_cos_mul.
Qed.

Lemma cf_im_le1 mu t : `|cf_im mu t| <= 1.
Proof.
apply: Rintegral_bounded => [|x]; last exact: sin_max.
exact: measurable_sin_mul.
Qed.

(* The modulus is at most one: with c = cf_re mu t and s = cf_im mu t,
   c^2 + s^2 is the integral of c cos (t x) + s sin (t x), which is at most
   sqrt (c^2 + s^2) by the Cauchy-Schwarz inequality in the plane. *)
Lemma cf_norm_le1 mu t : cf_norm mu t <= 1.
Proof.
set c := cf_re mu t; set s := cf_im mu t.
have mid := @measurable_id _ R setT.
have E : c ^+ 2 + s ^+ 2 = \int[mu]_x (c * cos (t * x) + s * sin (t * x)).
  by rewrite Rintegral_cos_sin -?expr2//; exact: measurable_funM.
have le : c ^+ 2 + s ^+ 2 <= cf_norm mu t.
  rewrite E; apply: le_trans (ler_norm _) _.
  apply: Rintegral_bounded => [|x].
    by apply: measurable_funD; apply: measurable_funM => //;
      [exact: measurable_cos_mul|exact: measurable_sin_mul].
  by apply: cmod_ge_dot; rewrite addrC sin2cos2 subrK.
have r0 := cf_norm_ge0 mu t.
have r2 : cf_norm mu t ^+ 2 = c ^+ 2 + s ^+ 2.
  by rewrite sqr_sqrtr// addr_ge0// sqr_ge0.
rewrite -r2 in le; nra.
Qed.

Lemma continuous_cf_re mu : continuous (cf_re mu).
Proof.
move=> t0; apply: (@continuity_under_integral_at _ _ _ _ mu
  (fun t x => cos (t * x)) setT t0 setT (fun=> 1)) => //.
- exact: filterT.
- by move=> t _; exact: integrable_cos_mul.
- move=> x _; apply: (@continuous_comp _ _ _ (fun t => t * x) cos).
    exact: mulrr_continuous.
  exact: continuous_cos.
- exact: finite_measure_integrable_cst.
- by move=> t _ x _; exact: cos_max.
Qed.

Lemma continuous_cf_im mu : continuous (cf_im mu).
Proof.
move=> t0; apply: (@continuity_under_integral_at _ _ _ _ mu
  (fun t x => sin (t * x)) setT t0 setT (fun=> 1)) => //.
- exact: filterT.
- by move=> t _; exact: integrable_sin_mul.
- move=> x _; apply: (@continuous_comp _ _ _ (fun t => t * x) sin).
    exact: mulrr_continuous.
  exact: continuous_sin.
- exact: finite_measure_integrable_cst.
- by move=> t _ x _; exact: sin_max.
Qed.

Lemma continuous_cf_norm mu : continuous (cf_norm mu).
Proof.
move=> t; apply: (@continuous_comp _ _ _
  (fun t => cf_re mu t ^+ 2 + cf_im mu t ^+ 2) Num.sqrt).
  apply: continuousD.
    apply: (@continuous_comp _ _ _ (cf_re mu) (fun x => x ^+ 2)).
      exact: continuous_cf_re.
    exact: exprn_continuous.
  apply: (@continuous_comp _ _ _ (cf_im mu) (fun x => x ^+ 2)).
    exact: continuous_cf_im.
  exact: exprn_continuous.
exact: sqrt_continuous.
Qed.

End charfun.

(* If nu is the law of g under P, the characteristic function of nu is
   computed under P. *)
Section charfun_image.
Context {R : realType} d (T : measurableType d) (P : probability T R).
Variables (nu : probability R R) (g : T -> R).
Hypothesis mg : measurable_fun [set: T] g.
Hypothesis gnu : forall A, measurable A -> P (g @^-1` A) = nu A.

Lemma cf_re_image t : cf_re nu t = \int[P]_x cos (t * g x).
Proof.
rewrite /cf_re /Rintegral -(integral_image mg gnu)//.
exact: integrable_cos_mul.
Qed.

Lemma cf_im_image t : cf_im nu t = \int[P]_x sin (t * g x).
Proof.
rewrite /cf_im /Rintegral -(integral_image mg gnu)//.
exact: integrable_sin_mul.
Qed.

Lemma cf_image t :
  cf nu t = (\int[P]_x cos (t * g x), \int[P]_x sin (t * g x)).
Proof. by rewrite /cf cf_re_image cf_im_image. Qed.

End charfun_image.

Section charfun_affine.
Context {R : realType}.
Implicit Types (mu nu : probability R R) (a b t : R).

(* The law of a X + b: its characteristic function at t is
   exp (i b t) times that of X at a t. *)
Lemma cf_affine mu nu a b :
    (forall A, measurable A -> mu ((fun x => a * x + b) @^-1` A) = nu A) ->
  forall t, cf nu t = cmul (cos (b * t), sin (b * t)) (cf mu (a * t)).
Proof.
move=> numu t; have ma : measurable_fun [set: R] (fun x => a * x + b).
  by apply: measurable_funD => //; exact: measurable_funM.
have mat : measurable_fun [set: R] (fun x => a * t * x).
  exact: measurable_funM.
rewrite (cf_image ma numu) /cf /cf_re /cf_im cmulE; congr pair.
  transitivity (\int[mu]_x (cos (b * t) * cos (a * t * x) +
      (- sin (b * t)) * sin (a * t * x))).
    apply: eq_Rintegral => x _.
    by rewrite mulrDr addrC cosD mulrA [t * a]mulrC [t * b]mulrC mulNr.
  by rewrite Rintegral_cos_sin// mulNr.
transitivity (\int[mu]_x (sin (b * t) * cos (a * t * x) +
    cos (b * t) * sin (a * t * x))).
  apply: eq_Rintegral => x _.
  by rewrite mulrDr addrC sinD mulrA [t * a]mulrC [t * b]mulrC addrC.
by rewrite Rintegral_cos_sin// addrC.
Qed.

Lemma cf_norm_affine mu nu a b :
    (forall A, measurable A -> mu ((fun x => a * x + b) @^-1` A) = nu A) ->
  forall t, cf_norm nu t = cf_norm mu (a * t).
Proof.
move=> numu t; rewrite !cf_normE (cf_affine numu) cmodM.
have -> : cmod (cos (b * t), sin (b * t)) = 1.
  by rewrite /cmod /= cos2Dsin2 sqrtr1.
by rewrite mul1r.
Qed.

End charfun_affine.

Section charfun_independent.
Context {R : realType}.

(* Fubini for bounded measurable functions on a product of probabilities. *)
Lemma Rintegral_prod_bounded d1 d2 (T1 : measurableType d1)
    (T2 : measurableType d2) (P1 : probability T1 R) (P2 : probability T2 R)
    (F : T1 * T2 -> R) (C : R) :
  measurable_fun [set: T1 * T2] F -> (forall p, `|F p| <= C) ->
  \int[(P1 \x P2)%E]_p F p = \int[P1]_x \int[P2]_y F (x, y).
Proof.
move=> mF FC; have iF := bounded_integrable (P1 \x P2)%E mF FC.
rewrite /Rintegral -(integral12_prod_meas1 iF); congr fine.
apply: eq_integral => x _; rewrite /fubini_F /=.
by rewrite (EFin_Rintegral_bounded P2 (C := C))//; exact: measurable_fun_pair2.
Qed.

(* Independent sums: the characteristic function of g1 X1 + g2 X2, for
   independent X1 and X2, is the complex product of those of g1 X1 and of
   g2 X2. First for iterated integrals, then for the product measure. *)
Lemma cf_iterated d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    (P1 : probability T1 R) (P2 : probability T2 R) (g1 : T1 -> R)
    (g2 : T2 -> R) :
    measurable_fun [set: T1] g1 -> measurable_fun [set: T2] g2 ->
  forall t,
  (\int[P1]_x \int[P2]_y cos (t * (g1 x + g2 y)),
   \int[P1]_x \int[P2]_y sin (t * (g1 x + g2 y))) =
  cmul (\int[P1]_x cos (t * g1 x), \int[P1]_x sin (t * g1 x))
    (\int[P2]_y cos (t * g2 y), \int[P2]_y sin (t * g2 y)).
Proof.
move=> mg1 mg2 t.
have mt1 : measurable_fun [set: T1] (fun x => t * g1 x).
  exact: measurable_funM.
have mt2 : measurable_fun [set: T2] (fun y => t * g2 y).
  exact: measurable_funM.
set c2 := \int[P2]_y cos (t * g2 y); set s2 := \int[P2]_y sin (t * g2 y).
rewrite cmulE; congr pair.
  transitivity (\int[P1]_x (c2 * cos (t * g1 x) + (- s2) * sin (t * g1 x))).
    apply: eq_Rintegral => x _.
    transitivity (\int[P2]_y (cos (t * g1 x) * cos (t * g2 y) +
        (- sin (t * g1 x)) * sin (t * g2 y))).
      by apply: eq_Rintegral => y _; rewrite mulrDr cosD mulNr.
    by rewrite Rintegral_cos_sin// -/c2 -/s2; ring.
  by rewrite Rintegral_cos_sin//; ring.
transitivity (\int[P1]_x (s2 * cos (t * g1 x) + c2 * sin (t * g1 x))).
  apply: eq_Rintegral => x _.
  transitivity (\int[P2]_y (sin (t * g1 x) * cos (t * g2 y) +
      cos (t * g1 x) * sin (t * g2 y))).
    by apply: eq_Rintegral => y _; rewrite mulrDr sinD.
  by rewrite Rintegral_cos_sin// -/c2 -/s2; ring.
by rewrite Rintegral_cos_sin//; ring.
Qed.

Lemma cf_prod_integral d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    (P1 : probability T1 R) (P2 : probability T2 R) (g1 : T1 -> R)
    (g2 : T2 -> R) :
    measurable_fun [set: T1] g1 -> measurable_fun [set: T2] g2 ->
  forall t,
  (\int[(P1 \x P2)%E]_p cos (t * (g1 p.1 + g2 p.2)),
   \int[(P1 \x P2)%E]_p sin (t * (g1 p.1 + g2 p.2))) =
  cmul (\int[P1]_x cos (t * g1 x), \int[P1]_x sin (t * g1 x))
    (\int[P2]_y cos (t * g2 y), \int[P2]_y sin (t * g2 y)).
Proof.
move=> mg1 mg2 t.
have mg : measurable_fun [set: T1 * T2] (fun p => g1 p.1 + g2 p.2).
  by apply: measurable_funD; apply: measurableT_comp.
rewrite (Rintegral_prod_bounded _ _ (measurable_cos_mul t mg)
  (fun p => cos_max _)).
rewrite (Rintegral_prod_bounded _ _ (measurable_sin_mul t mg)
  (fun p => sin_max _)).
exact: (cf_iterated P1 P2 mg1 mg2 t).
Qed.

Lemma cf_prod d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    (P1 : probability T1 R) (P2 : probability T2 R) (g1 : T1 -> R)
    (g2 : T2 -> R) (nu1 nu2 nu : probability R R) :
    measurable_fun [set: T1] g1 -> measurable_fun [set: T2] g2 ->
    (forall A, measurable A -> P1 (g1 @^-1` A) = nu1 A) ->
    (forall A, measurable A -> P2 (g2 @^-1` A) = nu2 A) ->
    (forall A, measurable A ->
      (P1 \x P2)%E ((fun p => g1 p.1 + g2 p.2)%R @^-1` A) = nu A) ->
  forall t, cf nu t = cmul (cf nu1 t) (cf nu2 t).
Proof.
move=> mg1 mg2 g1nu g2nu gnu t.
have mg : measurable_fun [set: T1 * T2] (fun p => g1 p.1 + g2 p.2)%R.
  by apply: measurable_funD; apply: measurableT_comp.
by rewrite (cf_image mg gnu) (cf_image mg1 g1nu) (cf_image mg2 g2nu)
  cf_prod_integral.
Qed.

Lemma cf_norm_prod d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    (P1 : probability T1 R) (P2 : probability T2 R) (g1 : T1 -> R)
    (g2 : T2 -> R) (nu1 nu2 nu : probability R R) :
    measurable_fun [set: T1] g1 -> measurable_fun [set: T2] g2 ->
    (forall A, measurable A -> P1 (g1 @^-1` A) = nu1 A) ->
    (forall A, measurable A -> P2 (g2 @^-1` A) = nu2 A) ->
    (forall A, measurable A ->
      (P1 \x P2)%E ((fun p => g1 p.1 + g2 p.2)%R @^-1` A) = nu A) ->
  forall t, (cf_norm nu t = cf_norm nu1 t * cf_norm nu2 t)%R.
Proof.
move=> mg1 mg2 g1nu g2nu gnu t.
by rewrite !cf_normE (cf_prod mg1 mg2 g1nu g2nu gnu) cmodM.
Qed.

End charfun_independent.

Section charfun_tuple_prod.
Context {R : realType}.
Implicit Types (mu : nat -> probability R R) (a : nat -> R).

Lemma measurable_tuple_lincomb n a :
  measurable_fun [set: n.-tuple R] (fun x => \sum_(k < n) a k * tnth x k).
Proof.
apply: measurable_sum => k; apply: measurable_funM => //.
exact: measurable_tnth.
Qed.

Let tuple_lincomb_cons n a (s : R) (ts : n.-tuple R) :
  \sum_(k < n.+1) a k * tnth (tuple_cons (s, ts)) k =
  a 0%N * s + \sum_(k < n) a k.+1 * tnth ts k.
Proof.
rewrite big_ord_recl /tuple_cons /= tnth0; congr (_ + _).
by apply: eq_bigr => k _; rewrite tnthS.
Qed.

(* Independent coordinates: for x of law tuple_prod mu n, the characteristic
   function of \sum_k a_k x_k at t is the complex product of the
   characteristic functions of the laws mu k at a_k t. *)
Lemma cf_tuple_prod_integral mu n a t :
  (\int[tuple_prod mu n]_x cos (t * \sum_(k < n) a k * tnth x k),
   \int[tuple_prod mu n]_x sin (t * \sum_(k < n) a k * tnth x k)) =
  \big[cmul/(1, 0)]_(k < n) cf (mu k) (a k * t).
Proof.
elim: n mu a => [|n IH] mu a.
  have mc : measurable_fun [set: 0.-tuple R]
      (fun x => cos (t * \sum_(k < 0) a k * tnth x k)).
    exact: (measurable_cos_mul t (@measurable_tuple_lincomb 0 a)).
  have ms : measurable_fun [set: 0.-tuple R]
      (fun x => sin (t * \sum_(k < 0) a k * tnth x k)).
    exact: (measurable_sin_mul t (@measurable_tuple_lincomb 0 a)).
  rewrite (Rintegral_tuple_prod0 mu mc) (Rintegral_tuple_prod0 mu ms).
  by rewrite !big_ord0 mulr0 cos0 sin0.
have mc : measurable_fun [set: n.+1.-tuple R]
    (fun x => cos (t * \sum_(k < n.+1) a k * tnth x k)).
  exact: (measurable_cos_mul t (@measurable_tuple_lincomb n.+1 a)).
have ms : measurable_fun [set: n.+1.-tuple R]
    (fun x => sin (t * \sum_(k < n.+1) a k * tnth x k)).
  exact: (measurable_sin_mul t (@measurable_tuple_lincomb n.+1 a)).
rewrite (Rintegral_tuple_prodS mu mc (fun x => cos_max _)).
rewrite (Rintegral_tuple_prodS mu ms (fun x => sin_max _)).
have ma0 : measurable_fun [set: R] (fun s => a 0%N * s).
  exact: measurable_funM.
have ma' := @measurable_tuple_lincomb n (fun i => a i.+1).
transitivity (cmul
  (\int[mu 0%N]_s cos (t * (a 0%N * s)), \int[mu 0%N]_s sin (t * (a 0%N * s)))
  (\int[tuple_prod (fun i => mu i.+1) n]_ts
     cos (t * \sum_(k < n) a k.+1 * tnth ts k),
   \int[tuple_prod (fun i => mu i.+1) n]_ts
     sin (t * \sum_(k < n) a k.+1 * tnth ts k))).
  rewrite -(cf_iterated (mu 0%N) (tuple_prod (fun i => mu i.+1) n) ma0 ma' t).
  by congr pair; apply: eq_Rintegral => s _; apply: eq_Rintegral => ts _;
    rewrite tuple_lincomb_cons.
rewrite big_ord_recl; congr cmul.
  rewrite /cf /cf_re /cf_im; congr pair; apply: eq_Rintegral => x _;
    by rewrite mulrA [t * _]mulrC.
exact: (IH (fun i => mu i.+1) (fun i => a i.+1)).
Qed.

Lemma cf_tuple_prod mu n a (nu : probability R R) :
    (forall A, measurable A ->
      tuple_prod mu n ((fun x => \sum_(k < n) a k * tnth x k) @^-1` A) =
      nu A) ->
  forall t, cf nu t = \big[cmul/(1, 0)]_(k < n) cf (mu k) (a k * t).
Proof.
move=> numu t; rewrite (cf_image (@measurable_tuple_lincomb n a) numu).
exact: cf_tuple_prod_integral.
Qed.

Lemma cf_norm_tuple_prod mu n a (nu : probability R R) :
    (forall A, measurable A ->
      tuple_prod mu n ((fun x => \sum_(k < n) a k * tnth x k) @^-1` A) =
      nu A) ->
  forall t, cf_norm nu t = \prod_(k < n) cf_norm (mu k) (a k * t).
Proof. by move=> numu t; rewrite cf_normE (cf_tuple_prod numu) cmod_prod. Qed.

End charfun_tuple_prod.

Section charfun_symmetrization.
Context {R : realType}.
Implicit Types (mu nu : probability R R).

(* The law of X - X', for independent X and X' of law mu, has the real
   characteristic function |cf mu|^2. *)
Lemma cf_sym mu nu :
    (forall A : set R, measurable A ->
      (mu \x mu)%E ((fun p => p.1 - p.2) @^-1` A) = nu A) ->
  forall t, cf nu t = (cf_norm mu t ^+ 2, 0).
Proof.
move=> numu t.
have mg : measurable_fun [set: R * R] (fun p : R * R => p.1 - p.2).
  by apply: measurable_funB; [exact: measurable_fst|exact: measurable_snd].
have mN : measurable_fun [set: R] (fun y : R => - y).
  exact: measurable_funN.
have E1 : \int[mu]_y cos (t * - y) = cf_re mu t.
  by apply: eq_Rintegral => y _; rewrite mulrN cosN.
have E2 : \int[mu]_y sin (t * - y) = - cf_im mu t.
  rewrite /cf_im -RintegralN; first exact: integrable_sin_mul.
  by apply: eq_Rintegral => y _; rewrite mulrN sinN.
have := cf_prod_integral mu mu (@measurable_id _ R setT) mN t.
rewrite /= E1 E2 => E; rewrite (cf_image mg numu) E cmulE.
rewrite /cf_norm sqr_sqrtr ?addr_ge0 ?sqr_ge0//.
by congr pair; rewrite /cf_re /cf_im; ring.
Qed.

Lemma cf_norm_sym mu nu :
    (forall A : set R, measurable A ->
      (mu \x mu)%E ((fun p => p.1 - p.2) @^-1` A) = nu A) ->
  forall t, cf_norm nu t = cf_norm mu t ^+ 2.
Proof.
move=> numu t; rewrite cf_normE (cf_sym numu) /cmod /= expr0n addr0.
by rewrite sqrtr_sqr ger0_norm// exprn_ge0// cf_norm_ge0.
Qed.

End charfun_symmetrization.
