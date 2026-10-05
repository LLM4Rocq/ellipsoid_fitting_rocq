(* Transfer Gaussian Lipschitz lower tails across an exceptional clipping set. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure numfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import GaussianCoordinateDefinitions GaussianProductDefinitions
  GaussianProbabilityProductDefinitions PaperMainGordonLipschitz
  PaperMainGaussianLipschitzClip PaperMainGaussianGordonTail
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianLipschitzVariance.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_clipping_square_loss x y a :
  0 < a -> x-y <= (x*x+y*y)/(2*a)+a.
Proof.
move=> Ha; apply (Rmult_le_reg_r (2*a)); first lra.
have E : ((x*x+y*y)/(2*a)+a)*(2*a) = x*x+y*y+2*a*a by field; lra.
rewrite E; have := pow2_ge_0 (x-y-2*a); have := pow2_ge_0 (x+y); nra.
Qed.

Theorem paper_main_gaussian_clipping_lower_tail d F G L
    (A : set (d.-tuple (measurableTypeR R))) b u :
  finite_joint_continuous d F -> 0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs-G ys) <= L * paper_main_gordon_distance d xs ys) ->
  measurable A -> (forall x, ~ A x -> F (tval x) = G (tval x)) ->
  b <= gaussian_iterated_expectation d G -> 0 < u ->
  (gaussian_product_law d [set x | Rle (F (tval x)) (b-u)] <=
    gaussian_product_law d A + (exp (-u^2/(2*L^2)))%:E)%E.
Proof.
move=> CF HL HG mA Heq Hb Hu.
have CG := paper_main_gaussian_lipschitz_continuous d G L ltac:(lra) HG.
have mF := paper_main_gaussian_continuous_le_measurable d F (b-u) CF.
have mG := paper_main_gaussian_continuous_le_measurable d G (b-u) CG.
have HS : [set x : d.-tuple (measurableTypeR R) | Rle (F (tval x)) (b-u)] `<=`
  A `|` [set x | Rle (G (tval x)) (b-u)].
{ move=> x /= Hx; case: (pselect (A x)) => HA; first by left.
  right; by rewrite -(Heq x HA). }
have HM : (gaussian_product_law d [set x | Rle (F (tval x)) (b-u)] <=
  gaussian_product_law d (A `|` [set x | Rle (G (tval x)) (b-u)]))%E.
{ apply: le_measure; rewrite ?inE; [exact mF|exact: measurableU|exact HS]. }
apply: (le_trans HM).
apply: (le_trans (measureU2 _ mA mG)).
exact: leeD (lexx _) (paper_main_gaussian_lipschitz_lower_margin d G L b u HL HG Hb Hu).
Qed.

Corollary paper_main_gaussian_clipping_lower_tail_bound d F G L
    (A : set (d.-tuple (measurableTypeR R))) p b u :
  finite_joint_continuous d F -> 0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs-G ys) <= L * paper_main_gordon_distance d xs ys) ->
  measurable A -> (forall x, ~ A x -> F (tval x) = G (tval x)) ->
  (gaussian_product_law d A <= p%:E)%E ->
  b <= gaussian_iterated_expectation d G -> 0 < u ->
  (gaussian_product_law d [set x | Rle (F (tval x)) (b-u)] <=
    (p + exp (-u^2/(2*L^2)))%:E)%E.
Proof.
move=> CF HL HG mA Heq Hp Hb Hu.
apply: (le_trans (paper_main_gaussian_clipping_lower_tail d F G L A b u CF HL HG mA Heq Hb Hu)).
rewrite EFinD; exact: leeD Hp (lexx _).
Qed.

Theorem paper_main_gaussian_clipping_mean_loss d F G
    (A : set (d.-tuple (measurableTypeR R))) p a mF mG vF vG :
  0 < a -> measurable A ->
  (forall x, ~ A x -> F (tval x) = G (tval x)) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) ->
  (gaussian_product_law d).-integrable setT (fun x => (G (tval x))%:E) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x)*F (tval x))%:E) ->
  (gaussian_product_law d).-integrable setT (fun x => (G (tval x)*G (tval x))%:E) ->
  (\int[gaussian_product_law d]_x (F (tval x))%:E = mF%:E)%E ->
  (\int[gaussian_product_law d]_x (G (tval x))%:E = mG%:E)%E ->
  (\int[gaussian_product_law d]_x (F (tval x)*F (tval x))%:E = vF%:E)%E ->
  (\int[gaussian_product_law d]_x (G (tval x)*G (tval x))%:E = vG%:E)%E ->
  (gaussian_product_law d A <= p%:E)%E ->
  mF-mG <= (vF+vG)/(2*a)+a * p.
Proof.
move=> Ha mA Heq IF IG IF2 IG2 EF EG EF2 EG2 Hp.
pose q := /(2*a).
have Hq : 0 <= q by apply Rlt_le,Rinv_0_lt_compat; lra.
have II := integrable_indic (gaussian_product_law d) mA.
have IQF : (gaussian_product_law d).-integrable setT
    (fun x => (q%:E * (F (tval x)*F (tval x))%:E)%E) by exact: integrableZl IF2.
have IQG : (gaussian_product_law d).-integrable setT
    (fun x => (q%:E * (G (tval x)*G (tval x))%:E)%E) by exact: integrableZl IG2.
have IQ := integrableD measurableT IQF IQG.
have IA : (gaussian_product_law d).-integrable setT
    (fun x => (a%:E * (\1_A x)%:E)%E) by exact: integrableZl II.
have IR := integrableD measurableT IQ IA.
have IS := integrableD measurableT IG IR.
have HB : (\int[gaussian_product_law d]_x (F (tval x))%:E <=
  \int[gaussian_product_law d]_x
    ((G (tval x))%:E + ((q%:E * (F (tval x)*F (tval x))%:E +
      q%:E * (G (tval x)*G (tval x))%:E) + a%:E * (\1_A x)%:E)))%E.
{ apply: (le_integral measurableT IF IS) => x _.
  rewrite /numfun.indic; case: (boolP (x \in A)) => Hx.
  - rewrite -!EFinM -!EFinD lee_fin; apply/RleP.
    change (F (tval x) <= G (tval x)+(q*(F (tval x)*F (tval x))+q*(G (tval x)*G (tval x))+a*1)).
    have H := paper_main_clipping_square_loss (F (tval x)) (G (tval x)) a Ha.
    rewrite /q; nra.
  - rewrite -!EFinM -!EFinD lee_fin; apply/RleP.
    change (F (tval x) <= G (tval x)+(q*(F (tval x)*F (tval x))+q*(G (tval x)*G (tval x))+a*0)).
    have HA : ~ A x.
    { move=> HA; have HAx : x \in A by exact/asboolP.
      move/negP: Hx => Hx; exact: (Hx HAx). }
    have HGG : 0 <= q*(G (tval x)*G (tval x)).
    { apply Rmult_le_pos; first exact Hq; nra. }
    have HFF : 0 <= q*(F (tval x)*F (tval x)).
    { apply Rmult_le_pos; first exact Hq; nra. }
    have EE := Heq x HA.
    rewrite Rmult_0_r Rplus_0_r.
    eapply Rle_trans; first (right; exact EE).
    have HPsum := Rplus_le_le_0_compat _ _ HFF HGG.
    have HS := Rplus_le_compat_l (G (tval x)) _ _ HPsum.
    by rewrite Rplus_0_r in HS. }
rewrite (integralD measurableT IG IR) (integralD measurableT IQ IA)
  (integralD measurableT IQF IQG) (integralZl measurableT IF2)
  (integralZl measurableT IG2) (integralZl measurableT II)
  (integral_indic (gaussian_product_law d) measurableT mA) setIT EF EG EF2 EG2 in HB.
have Hmult : (a%:E * gaussian_product_law d A <= a%:E * p%:E)%E.
{ apply: lee_wpmul2l Hp.
  rewrite lee_fin; apply/RleP; change (0 <= a); lra. }
have Htotal := le_trans HB (leeD (lexx _) (leeD (lexx _) Hmult)).
rewrite -!EFinM -!EFinD lee_fin in Htotal.
move/RleP: Htotal => Htotal.
change (mF <= mG+(q*vF+q*vG+a * p)) in Htotal.
rewrite /q in Htotal; nra.
Qed.


Corollary paper_main_gaussian_clipping_moment_lower_tail d F G L
    (A : set (d.-tuple (measurableTypeR R))) p a mF vF u :
  finite_joint_continuous d F -> 0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (G xs-G ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 < a -> measurable A ->
  (forall x, ~ A x -> F (tval x) = G (tval x)) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x)*F (tval x))%:E) ->
  (\int[gaussian_product_law d]_x (F (tval x))%:E = mF%:E)%E ->
  (\int[gaussian_product_law d]_x (F (tval x)*F (tval x))%:E = vF%:E)%E ->
  (gaussian_product_law d A <= p%:E)%E -> 0 < u ->
  (gaussian_product_law d [set x | Rle (F (tval x))
    (mF-((vF+gaussian_iterated_expectation d (fun xs => Rmult (G xs) (G xs)))/(2*a)+a * p)-u)] <=
    (p + exp (-u^2/(2*L^2)))%:E)%E.
Proof.
move=> CF HL HG Ha mA Heq IF IF2 EF EF2 Hp Hu.
have [IG EG] := paper_main_gaussian_lipschitz_law d G L ltac:(lra) HG.
have [IG2 EG2] := paper_main_gaussian_lipschitz_square_law d G L ltac:(lra) HG.
have HM := paper_main_gaussian_clipping_mean_loss d F G A p a mF
  (gaussian_iterated_expectation d G) vF
  (gaussian_iterated_expectation d (fun xs => Rmult (G xs) (G xs)))
  Ha mA Heq IF IG IF2 IG2 EF EG EF2 EG2 Hp.
apply: (paper_main_gaussian_clipping_lower_tail_bound d F G L A p _ u CF HL HG mA Heq Hp) => //.
lra.
Qed.
