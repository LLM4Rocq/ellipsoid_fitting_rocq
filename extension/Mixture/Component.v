(* Component laws of a finite mixture of product laws, at Stdlib's R: the
   facts about mixture_component_law (MixtureDefinitions) that the proofs of
   the finite-mixture theorem share. A component law has mean 0, variance 1
   and E exp (X^2 / K^2) <= 2 (the condition (M2) of
   notes/mixture-product-universality.md); it is universality_coordinate_law
   without the condition on the fourth moment.

   Results.
   - coordinate_law_component: a coordinate law with fourth moment kappa
     and constant K (universality_coordinate_law kappa K) is a component law
     with constant K. The proofs of the universality theorem therefore
     apply to component laws wherever they do not use the fourth moment.
   - component_law_K, component_law_subgaussian, component_law_integrable,
     component_law_mean, component_law_second, component_law_moment: K > 0,
     X is subgaussian with constant K (subgaussian of
     library/probability/subgaussian.v), every power of X is integrable,
     E X = 0 and E X^2 = 1 as integrals, and E X^(2k) <= 2 k! K^(2k).
   - component_law_fourth_le: E X^4 <= 4 K^4.
   - component_law_truncated: the truncated second moment
     E[X^2 1_(|X| <= sqrt 8 K^2)] is at least 1/2, since
     X^2 1_(|X| > M) <= X^4 / M^2 and M^2 = 8 K^4 >= 2 E X^4: the
     hypothesis of the vector small-ball estimate (vector_small_ball_moments
     of library/fourier/small_ball.v) with the level sqrt 8 K^2.
   - component_law_nonzero: P(X != 0) >= 1 / (4 K^4), from
     X^2 <= X^4 / (2 k) + k / 2 1_(X != 0) with k = 4 K^4. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import normedtype sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import subgaussian.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure. *)
Local Notation RR := (R : realType).

Lemma coordinate_law_component (kappa K : R)
    (mu : probability (measurableTypeR R) R) :
  universality_coordinate_law kappa K mu -> mixture_component_law K mu.
Proof.
by move=> [K0 [h1 [h2 [_ hs]]]]; exact: (conj K0 (conj h1 (conj h2 hs))).
Qed.

Section component_law.
Local Open Scope ereal_scope.
Variables (K : R) (mu : probability (measurableTypeR R) R).
Hypothesis hmu : mixture_component_law K mu.

Lemma component_law_K : (0 < K)%R.
Proof. by case: hmu. Qed.

Lemma component_law_subgaussian : subgaussian mu (fun x : R => x) K.
Proof.
case: hmu => K0 [_ [_ h]]; split => //.
by move: h; rewrite unlock /universality_subgaussian_test.
Qed.

Lemma component_law_integrable k :
  mu.-integrable setT (fun x : measurableTypeR R => ((x : R) ^+ k)%:E).
Proof. exact: integrable_subgaussian_exprn component_law_subgaussian. Qed.

Lemma component_law_mean : \int[mu]_x ((x : R))%:E = 0.
Proof.
case: hmu => _ [h _]; move: h; rewrite unlock /universality_power.
by under eq_integral do rewrite expr1.
Qed.

Lemma component_law_second : \int[mu]_x ((x : R) ^+ 2)%:E = 1.
Proof. by case: hmu => _ [_ [h _]]; move: h; rewrite unlock. Qed.

Lemma component_law_moment k :
  \int[mu]_x ((x : R) ^+ (2 * k))%:E <= (2 * k`!%:R * K ^+ (2 * k))%:E.
Proof. exact: subgaussian_moment component_law_subgaussian. Qed.

Lemma component_law_fourth_le :
  \int[mu]_x ((x : R) ^+ 4)%:E <= ((4%:R * K ^+ 4)%R)%:E.
Proof.
apply: le_trans (component_law_moment 2) _; rewrite lee_fin.
have -> : (2 * 2`!%:R = 4%:R :> RR)%R by rewrite -natrM.
by [].
Qed.

Lemma component_law_truncated :
  (2^-1)%:E <= \int[mu]_x
    (((x : RR) ^+ 2 *
      \1_[set y : RR | (`|y| <= Num.sqrt 8%:R * K ^+ 2)%R] x)%R)%:E.
Proof.
set M := (Num.sqrt 8%:R * K ^+ 2)%R.
have K0 := component_law_K.
have K40 : (0 < K ^+ 4)%R by rewrite exprn_gt0.
have M0 : (0 <= M)%R by rewrite mulr_ge0 ?sqrtr_ge0 ?sqr_ge0.
have M2 : (M ^+ 2 = 8%:R * K ^+ 4)%R.
  by rewrite /M exprMn sqr_sqrtr ?ler0n // -exprM.
pose c := ((8%:R * K ^+ 4)^-1)%R.
have c0 : (0 <= c)%R by rewrite invr_ge0 mulr_ge0 ?ler0n // ltW.
have i2 := component_law_integrable 2.
have i4 := component_law_integrable 4.
pose f (x : RR) := (x ^+ 2 - c * x ^+ 4)%R.
pose g (x : RR) := (x ^+ 2 * \1_[set y : RR | (`|y| <= M)%R] x)%R.
have mA : measurable [set y : RR | (`|y| <= M)%R].
  rewrite (_ : [set y | _] = `[(- M)%R, M]%classic); last exact: measurable_itv.
  by apply/seteqP; split => y /=; rewrite in_itv /= ler_norml.
have i4c : mu.-integrable setT
    (fun x : measurableTypeR R => (c * (x : RR) ^+ 4)%:E).
  have := integrableZl measurableT c i4.
  by apply: eq_integrable => // x _; rewrite EFinM.
have fi : mu.-integrable setT (EFin \o f).
  have := integrableB measurableT i2 i4c.
  by apply: eq_integrable => // x _; rewrite /f /= EFinB.
have mg : measurable_fun setT g.
  apply: measurable_funM; first exact: measurable_funX.
  exact: measurable_indic.
have gi : mu.-integrable setT (EFin \o g).
  apply: le_integrable i2 => //; first exact/measurable_EFinP.
  move=> x _; rewrite /comp /g !abse_EFin lee_fin (ger0_norm (sqr_ge0 x)) indicE.
  case: (x \in _); rewrite ?mulr1 ?mulr0 ?normr0 ?(ger0_norm (sqr_ge0 x)) //.
  exact: sqr_ge0.
have fg x : (f x <= g x)%R.
  rewrite /f /g indicE; case: (boolP (x \in _)) => [hx|hx].
    rewrite mulr1 lerBlDr lerDl; apply: mulr_ge0 => //.
    by rewrite (_ : 4%N = (2 * 2)%N) // exprM sqr_ge0.
  rewrite mulr0 subr_le0.
  have hM : (M ^+ 2 <= x ^+ 2)%R.
    have hx' : (M <= `|x|)%R.
      apply: ltW; rewrite ltNge; apply/negP => h; apply: (negP hx).
      by rewrite in_setE.
    have h1 : (M * M <= `|x| * `|x|)%R by apply: ler_pM.
    have h2 : (`|x| * `|x| = x ^+ 2)%R.
      by rewrite -normrM -expr2 (ger0_norm (sqr_ge0 x)).
    by rewrite [(M ^+ 2)%R]expr2 -h2.
  have Mp : (0 < M ^+ 2)%R by rewrite M2 mulr_gt0 ?ltr0n.
  have x4 : (x ^+ 4 = x ^+ 2 * x ^+ 2)%R by rewrite -exprD.
  rewrite /c -M2 mulrC ler_pdivlMr // x4.
  exact: (ler_wpM2l (sqr_ge0 x) hM).
apply: le_trans (_ : \int[mu]_x (f x)%:E <= _); last first.
  by apply: le_integral => // x _; rewrite lee_fin; exact: fg.
rewrite (integralB_EFin measurableT i2 i4c).
have e4 : \int[mu]_x ((c * (x : RR) ^+ 4)%R)%:E =
    c%:E * \int[mu]_x (((x : RR) ^+ 4)%R)%:E.
  transitivity (\int[mu]_x (c%:E * (((x : RR) ^+ 4)%R)%:E)).
    by apply: eq_integral => x _; rewrite EFinM.
  by rewrite integralZl.
rewrite e4 component_law_second.
have f4 := integrable_fin_num measurableT i4.
have h4 := component_law_fourth_le.
set a := fine (\int[mu]_x ((x : R) ^+ 4)%:E).
have Ia : \int[mu]_x (((x : RR) ^+ 4)%R)%:E = a%:E by rewrite /a fineK.
rewrite Ia -EFinM -EFinB lee_fin.
have ha : (a <= 4%:R * K ^+ 4)%R by rewrite -lee_fin -Ia; exact: h4.
have hca : (c * a <= c * (4%:R * K ^+ 4))%R by rewrite ler_wpM2l.
have Kn : K != 0%R by rewrite gt_eqF.
have hc : (c * (4%:R * K ^+ 4) = 2^-1)%R by rewrite /c; field.
by rewrite hc in hca; lra.
Qed.

End component_law.

(* The nonzero probability, in ring_scope as the proof it adapts
   (coordinate_nonzero of Sat/Universality). *)

Section component_nonzero.
Variables (K : R) (mu : probability (measurableTypeR R) R).
Hypothesis hmu : mixture_component_law K mu.

Lemma component_law_nonzero :
  ((((4%:R * K ^+ 4)^-1)%R)%:E <=
     mu [set x : measurableTypeR R | ((x : R) != 0)%R])%E.
Proof.
set k := (4%:R * K ^+ 4)%R.
have k0 : (0 < k)%R by rewrite mulr_gt0 ?ltr0n // exprn_gt0 // (component_law_K K mu hmu).
pose A := [set x : measurableTypeR R | (x : R) != 0].
have mA : measurable A.
  have -> : A = ~` [set (0 : R)].
    by apply/seteqP; split => x /=; [move=> /eqP|move=> h; apply/eqP].
  exact: measurableC.
pose g (x : measurableTypeR R) : RR :=
  (x : R) ^+ 4 / (2 * k) + k / 2 * (\1_A x : RR).
have hpt (x : measurableTypeR R) : ((x : R) ^+ 2 <= g x)%R.
  rewrite /g indicE; have [x0|x0] := eqVneq (x : R) 0.
    rewrite x0 expr0n /= expr0n /= mul0r add0r.
    by apply: mulr_ge0; [rewrite divr_ge0 // ltW | exact: ler0n].
  rewrite mem_set //= mulr1.
  have : (0 <= ((x : R) ^+ 2 - k) ^+ 2 / (2 * k))%R.
    by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 // ltW.
  have kn : k != 0 by rewrite gt_eqF.
  have -> : (((x : R) ^+ 2 - k) ^+ 2 / (2 * k) =
      (x : R) ^+ 4 / (2 * k) + k / 2 - (x : R) ^+ 2)%R.
    by field.
  by rewrite subr_ge0.
have i4 := component_law_integrable K mu hmu 4.
have mI : measurable_fun setT (fun x : measurableTypeR R => (\1_A x : RR)).
  exact: measurable_indic.
have h2 := component_law_second K mu hmu.
have hle : (\int[mu]_x ((x : R) ^+ 2)%:E <= \int[mu]_x (g x)%:E)%E.
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin sqr_ge0.
  - apply/measurable_EFinP; exact: measurable_funX.
  - apply/measurable_EFinP; apply: measurable_funD.
      by apply: measurable_funM => //; exact: measurable_funX.
    by apply: measurable_funM => //.
  - by move=> x _; rewrite lee_fin.
have m4 : measurable_fun setT
    (fun x : measurableTypeR R => ((x : R) ^+ 4 : RR)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have p4 (x : measurableTypeR R) : setT x -> (0 <= ((x : R) ^+ 4 : RR)%:E)%E.
  by move=> _; rewrite lee_fin exprn_even_ge0.
have mI' : measurable_fun setT
    (fun x : measurableTypeR R => ((\1_A x : RR))%:E).
  by apply/measurable_EFinP.
have pI (x : measurableTypeR R) : setT x -> (0 <= ((\1_A x : RR))%:E)%E.
  by move=> _; rewrite lee_fin indicE ler0n.
have kk : (0 <= (2 * k)^-1 :> RR)%R by rewrite invr_ge0 mulr_ge0 // ltW.
have k2 : (0 <= k / 2 :> RR)%R by rewrite divr_ge0 // ltW.
have I4 : (\int[mu]_x ((x : R) ^+ 4 / (2 * k) : RR)%:E =
    (2 * k)^-1%:E * \int[mu]_x ((x : R) ^+ 4)%:E)%E.
  under eq_integral do rewrite mulrC EFinM.
  by rewrite ge0_integralZl.
have II : (\int[mu]_x (k / 2 * (\1_A x : RR))%:E = (k / 2)%:E * mu A)%E.
  under eq_integral do rewrite EFinM.
  by rewrite ge0_integralZl // integral_indic // setIT.
have mf4 : measurable_fun setT
    (fun x : measurableTypeR R => ((x : R) ^+ 4 / (2 * k) : RR)%:E).
  apply/measurable_EFinP; apply: measurable_funM; last exact: measurable_cst.
  by apply: measurable_funX.
have f40 (x : measurableTypeR R) : setT x ->
    (0 <= ((x : R) ^+ 4 / (2 * k) : RR)%:E)%E.
  by move=> _; rewrite lee_fin divr_ge0 ?exprn_even_ge0 // mulr_ge0 // ltW.
have mfI : measurable_fun setT
    (fun x : measurableTypeR R => (k / 2 * (\1_A x : RR))%:E).
  by apply/measurable_EFinP; apply: measurable_funM.
have fI0 (x : measurableTypeR R) : setT x ->
    (0 <= (k / 2 * (\1_A x : RR))%:E)%E.
  by move=> _; rewrite lee_fin mulr_ge0 // indicE ler0n.
have hg : (\int[mu]_x (g x)%:E =
    (2 * k)^-1%:E * \int[mu]_x ((x : R) ^+ 4)%:E + (k / 2)%:E * mu A)%E.
  rewrite /g.
  under eq_integral do rewrite EFinD.
  by rewrite ge0_integralD // I4 II.
rewrite hg h2 in hle.
have f4 := integrable_fin_num measurableT i4.
have h4 := component_law_fourth_le K mu hmu.
set a4 := fine (\int[mu]_x ((x : R) ^+ 4)%:E)%E.
have Ia : (\int[mu]_x ((x : R) ^+ 4)%:E = a4%:E)%E by rewrite /a4 fineK.
rewrite Ia in hle h4; rewrite lee_fin in h4.
have PA : (mu A <= 1)%E by apply: probability_le1.
have PA0 : (0 <= mu A)%E by exact: measure_ge0.
move: hle PA PA0; case: (mu A) => [a| |] //= hle _ _.
rewrite -EFinM -EFinM -EFinD lee_fin in hle.
rewrite lee_fin.
have kn : k != 0 by rewrite gt_eqF.
have ha4 : ((2 * k)^-1 * a4 <= 2^-1)%R.
  have : ((2 * k)^-1 * a4 <= (2 * k)^-1 * k)%R by rewrite ler_wpM2l.
  by rewrite (_ : ((2 * k)^-1 * k = 2^-1)%R) //; field.
have h5 : (2^-1 <= k / 2 * a)%R by lra.
rewrite -div1r ler_pdivrMr //.
have -> : (a * k = 2 * (k / 2 * a))%R by field.
by lra.
Qed.

End component_nonzero.
