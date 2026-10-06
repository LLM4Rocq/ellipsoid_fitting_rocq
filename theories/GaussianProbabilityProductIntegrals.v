(* The integral against gaussian_product_law d, the law of d independent
   standard normal coordinates, is the iterated Gaussian expectation
   gaussian_iterated_expectation d, a tuple x being read as its list of
   coordinates tval x. gpp_nonnegative proves it for a measurable
   nonnegative F integrable at every level of the iterated expectation
   (Tonelli); gpp_all_sections, for a measurable F integrable and
   absolutely integrable at every level, also shows that F is integrable
   against the product law (Fubini). *)
From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import measurable_realfun.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityIntegrals.
From EllipsoidFitting Require Import GaussianProbabilityProductMeasure.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma gpp_nonnegative d (F : list R -> R) :
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun x => (F (tval x))%:E) ->
  (forall xs, 0 <= F xs) -> gaussian_iterated_integrable d F ->
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
elim: d F => [|d IH] F mF F0 HI; first exact: gpp_zero_integral.
case: HI => HI hI.
have mH := gpp_cons_measurable d F mF.
have mS a : measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun x => (F (a :: tval x))%:E).
  exact: measurable_fun_pair2 mH.
rewrite /gaussian_product_law -/gaussian_product_law /distribution.
rewrite ge0_integral_pushforward //; first by move=> x _; rewrite lee_fin.
rewrite preimage_setT /gaussian_pair_probability.
rewrite fubini_tonelli1 //; first by move=> x; rewrite lee_fin.
rewrite /fubini_F /=.
under eq_integral do rewrite (IH _ (mS _)
  (fun xs => F0 _) (HI _)).
exact: gpb_law_integral _ hI.
Qed.

Lemma gpp_all_sections d (F : list R -> R) :
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun x => (F (tval x))%:E) ->
  gaussian_iterated_integrable d F ->
  gaussian_iterated_absolutely_integrable d F ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
elim: d F => [|d IH] F mF HI HA.
- split; last exact: gpp_zero_integral.
  apply/integrableP; split=> //.
  under eq_integral do rewrite gpp_zero_tuple.
  by rewrite integral_dirac ?diracT ?mul1e ?ltry //; exact: measurable_cst.
- case: HI => HI hI; case: HA => HA hA.
  have mH := gpp_cons_measurable d F mF.
  have mS a : measurable_fun [set: d.-tuple (measurableTypeR R)]
      (fun x => (F (a :: tval x))%:E).
    exact: measurable_fun_pair2 mH.
  have sec a := IH _ (mS a) (HI a) (HA a).
  have abssec a :
      (\int[gaussian_product_law d]_x `|(F (a :: tval x))%:E| =
       (gaussian_iterated_expectation d (fun xs => Rabs (F (a :: xs))))%:E)%E.
  { under eq_integral do rewrite /= -RabsE.
    apply: gpp_nonnegative; last exact: (HA a).
    - apply/measurable_EFinP.
      apply: (@measurableT_comp _ _ _ _ _ _ (fun x : measurableTypeR R => `|x|)).
      + exact: normr_measurable.
      + apply/measurable_EFinP; exact: (mS a).
    - by move=> xs; apply/RleP; exact: Rabs_pos. }
  have ipair : (gaussian_law_probability \x gaussian_product_law d)%E.-integrable
      setT (fun p => (F (p.1 :: tval p.2))%:E).
  { apply/(integrable12ltyP _ _ mH).
    under eq_integral do rewrite abssec.
    rewrite (gpb_law_integral _ hA) ltry //. }
  have ipre : (gaussian_pair_probability gaussian_law_probability (gaussian_product_law d)).-integrable
      (gaussian_cons_tuple d @^-1` setT)
      ((fun x => (F (tval x))%:E) \o gaussian_cons_tuple d).
    by rewrite preimage_setT; exact: ipair.
  split.
  + exact: (integrable_pushforward (gaussian_cons_tuple_measurable d) mF ipre measurableT).
  + rewrite /gaussian_product_law -/gaussian_product_law /distribution.
    rewrite (integral_pushforward (gaussian_cons_tuple_measurable d) mF ipre measurableT).
    rewrite preimage_setT /gaussian_pair_probability.
    rewrite -integral12_prod_meas1 //.
    rewrite /fubini_F /=.
    under eq_integral do rewrite (sec _).2.
    exact: gpb_law_integral _ hI.
Qed.
