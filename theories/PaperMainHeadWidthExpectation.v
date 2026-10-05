(* Integration of an approximate support bound, with an explicit loss on
   an exceptional set. Here D = paper_main_symmetric_dimension n, Z is the
   symmetric Gaussian matrix paper_main_public_symmetric_gaussian n of D
   standard coordinates, F is the support of the cone sphere
   paper_main_head_cone_sphere kappa at Z
   (paper_main_gaussian_condition_support) and V = |Z|_F.
   - paper_main_head_support_exceptional_point: if |f|, |g| <= v, then
     f <= g + e v + v^2 / a + a, since 2 v <= v^2 / a + a.
   - paper_main_head_width_expectation_transfer: if |G| <= V everywhere and
     F - e V <= G outside a measurable set A of probability at most p, then
     the width E[F] (paper_main_gaussian_condition_width) exceeds E[G] by
     at most e sqrt D + D / a + a p.
   - paper_main_head_width_exceptional_scale: for a = d^2 and p = d^(-4),
     d = n + 1, this loss is at most e d + 1 + 1 / d^2. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix numfun.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProductDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGaussianFeatureCoordinates PaperMainGaussianSymmetricLawPublic
  PaperMainGaussianConditionWidth PaperMainGaussianNorm PaperMainGaussianNormConcentration
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianPsdWidthLimit.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

Lemma paper_main_head_support_exceptional_point f g v e a :
  0 <= e -> 0 <= v -> 0 < a -> Rabs f <= v -> Rabs g <= v ->
  f <= g+e*v+v^2/a+a.
Proof.
move=> He Hv Ha Hf Hg.
have HF := Rle_abs f.
have HG := Rle_abs (-g); rewrite Rabs_Ropp in HG.
have Hsq := pow2_ge_0 (v-a).
have Hyoung : 2*v <= v^2/a+a.
{ apply (Rmult_le_reg_r a); first exact Ha.
  replace ((v^2/a+a)*a) with (v^2+a^2) by (field; lra).
  nra. }
have Hev := Rmult_le_pos e v He Hv.
lra.
Qed.

Theorem paper_main_head_width_expectation_transfer n kappa
    (G : (paper_main_symmetric_dimension n).-tuple T -> R)
    (A : set ((paper_main_symmetric_dimension n).-tuple T)) e a p mG :
  1 <= kappa -> 0 <= e -> 0 < a -> measurable A ->
  (forall x, Rabs (G x) <= paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x))) ->
  (forall x, ~ A x -> paper_main_gaussian_condition_support n kappa (tval x) -
    e* paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x)) <= G x) ->
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT (fun x => (G x)%:E) ->
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_x (G x)%:E = mG%:E)%E ->
  (gaussian_product_law (paper_main_symmetric_dimension n) A <= p%:E)%E ->
  paper_main_gaussian_condition_width n kappa - mG <=
    e*sqrt(INR (paper_main_symmetric_dimension n))+INR (paper_main_symmetric_dimension n)/a+a * p.
Proof.
move=> Hk He Ha mA HG Hgood IG EG Hp.
pose D := paper_main_symmetric_dimension n.
pose F := fun x : D.-tuple T => paper_main_gaussian_condition_support n kappa (tval x).
pose V := fun x : D.-tuple T => paper_main_gaussian_norm (tval x).
pose q := /a.
have Hq : 0 <= q by apply Rlt_le,Rinv_0_lt_compat; exact Ha.
have EV : forall x : D.-tuple T,
    paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x)) = V x.
{ move=> x; apply: paper_main_public_symmetric_gaussian_norm; exact: size_tuple. }
have [IF EF] := paper_main_gaussian_condition_law n kappa Hk.
have [IV EM] := paper_main_gaussian_lipschitz_law D paper_main_gaussian_norm 1 Rle_0_1
  (paper_main_gaussian_norm_lipschitz D).
have [IV2 EV2] := paper_main_public_symmetric_gaussian_law_moments n.
have EQ2 : (fun x : D.-tuple T => (paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x))^2)%:E) =
    (fun x => ((V x)^2)%:E).
{ apply/funext => x; by rewrite EV. }
rewrite EQ2 in IV2 EV2.
case: EV2 => EV2 _.
have II := integrable_indic (gaussian_product_law D) mA.
have IE : (gaussian_product_law D).-integrable setT (fun x => (e%:E*(V x)%:E)%E).
  exact: integrableZl IV.
have IQ : (gaussian_product_law D).-integrable setT (fun x => (q%:E*((V x)^2)%:E)%E).
  exact: integrableZl IV2.
have IA : (gaussian_product_law D).-integrable setT (fun x => (a%:E*(\1_A x)%:E)%E).
  exact: integrableZl II.
have I1 := integrableD measurableT IG IE.
have I2 := integrableD measurableT I1 IQ.
have I3 := integrableD measurableT I2 IA.
have HB : (\int[gaussian_product_law D]_x (F x)%:E <=
  \int[gaussian_product_law D]_x ((G x)%:E+e%:E*(V x)%:E+q%:E*((V x)^2)%:E+a%:E*(\1_A x)%:E))%E.
{ apply: (le_integral measurableT IF I3) => x _.
  rewrite /numfun.indic; case: (boolP (x \in A)) => Hx;
    rewrite -!EFinM -!EFinD lee_fin; apply/RleP.
  - change (F x <= G x+e*V x+q*(V x)^2+a*1).
    rewrite Rmult_1_r /q.
    replace (/a*(V x)^2) with ((V x)^2/a) by (unfold Rdiv; ring).
    apply: paper_main_head_support_exceptional_point => //.
    + exact: paper_main_gaussian_norm_nonnegative.
    + rewrite /F -EV; exact: paper_main_gaussian_condition_abs.
    + by rewrite -EV.
  - change (F x <= G x+e*V x+q*(V x)^2+a*0).
    have Hnot : ~ A x.
    { move=> H; have HH := mem_set H; by move: Hx; rewrite HH. }
    have Hgoodx := Hgood x Hnot; rewrite EV in Hgoodx.
    have HV2 := pow2_ge_0 (V x).
    have HQ := Rmult_le_pos q ((V x)^2) Hq HV2.
    change (F x-e*V x <= G x) in Hgoodx.
    lra. }
rewrite (integralD measurableT I2 IA) (integralD measurableT I1 IQ)
  (integralD measurableT IG IE) (integralZl measurableT IV)
  (integralZl measurableT IV2) (integralZl measurableT II)
  EF EG EM EV2 (integral_indic (gaussian_product_law D) measurableT mA) setIT in HB.
have HP : (a%:E*gaussian_product_law D A <= a%:E* p%:E)%E.
{ apply: lee_wpmul2l Hp; rewrite lee_fin; apply/RleP; change (0 <= a); lra. }
have HB' := le_trans HB (leeD (lexx _) HP).
rewrite -!EFinM -!EFinD lee_fin in HB'.
move/RleP: HB' => HB'.
change (paper_main_gaussian_condition_width n kappa <=
  mG+e*gaussian_iterated_expectation D paper_main_gaussian_norm+q*INR D+a * p) in HB'.
have HM := (proj2 (paper_main_gaussian_norm_expectation D)).
have HE := Rmult_le_compat_l e _ _ He HM.
change (paper_main_gaussian_condition_width n kappa-mG <= e*sqrt(INR D)+INR D/a+a * p).
rewrite /q in HB'; unfold Rdiv in HB' |- *; nra.
Qed.

Lemma paper_main_head_width_exceptional_scale n e :
  0 <= e ->
  e*sqrt(INR (paper_main_symmetric_dimension n))+
    INR (paper_main_symmetric_dimension n)/(INR (S n))^2+
    (INR (S n))^2*(1/(INR (S n))^4) <= e*INR (S n)+1+1/(INR (S n))^2.
Proof.
move=> He.
pose d := INR (S n).
have Hd : 1 <= d by unfold d; rewrite S_INR; have := pos_INR n; lra.
have HD : INR (paper_main_symmetric_dimension n) <= d^2.
{ rewrite paper_main_symmetric_dimension_real; fold d; nra. }
have Hroot : sqrt(INR (paper_main_symmetric_dimension n)) <= d.
{ have HS := sqrt_pos (INR (paper_main_symmetric_dimension n)).
  have HE := pow2_sqrt _ (pos_INR (paper_main_symmetric_dimension n)); nra. }
have HR : INR (paper_main_symmetric_dimension n)/d^2 <= 1.
{ apply (Rmult_le_reg_r (d^2)); first nra.
  replace (INR (paper_main_symmetric_dimension n)/d^2*d^2) with
    (INR (paper_main_symmetric_dimension n)) by (field; nra).
  nra. }
have HE : d^2*(1/d^4) = 1/d^2 by field; nra.
have HM := Rmult_le_compat_l e _ _ He Hroot.
fold d; rewrite HE; lra.
Qed.
