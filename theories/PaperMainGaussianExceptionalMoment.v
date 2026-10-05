(* Quantitative expectation loss on a measurable exceptional event, using
   the actual public Gaussian law and its proved second moments. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import numfun.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianCoordinateDefinitions
  GaussianProductDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainGordonLipschitz
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianLipschitzVariance.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_exceptional_young x a :
  0 < a -> x <= / (4*a) * (x*x) + a.
Proof.
intros Ha; apply (Rmult_le_reg_r (4*a)); [lra|].
replace ((/(4*a)*(x*x)+a)*(4*a)) with (x*x+4*a*a) by (field; lra).
pose proof (pow2_ge_0 (x-2*a)); nra.
Qed.

Theorem paper_main_gaussian_lipschitz_event_integrable d F L
    (A : set (d.-tuple (measurableTypeR R))) :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs-F ys) <= L * paper_main_gordon_distance d xs ys) ->
  measurable A ->
  (gaussian_product_law d).-integrable A (fun x => (F (tval x))%:E).
Proof.
move=> HL Hlip mA.
have [HF _] := paper_main_gaussian_lipschitz_law d F L HL Hlip.
apply: (integrableS measurableT mA _ HF).
by move=> x _.
Qed.

Theorem paper_main_gaussian_exceptional_second_moment d F L
    (A : set (d.-tuple (measurableTypeR R))) a :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs-F ys) <= L * paper_main_gordon_distance d xs ys) ->
  measurable A -> 0 < a ->
  (\int[gaussian_product_law d]_(x in A) (F (tval x))%:E <=
    ((/ (4*a) * gaussian_iterated_expectation d (fun xs => F xs*F xs))%Rcoq)%:E +
    a%:E * gaussian_product_law d A)%E.
Proof.
move=> HL Hlip mA Ha.
pose q := / (4*a).
have Hq : 0 <= q by apply Rlt_le, Rinv_0_lt_compat; lra.
have HF := paper_main_gaussian_lipschitz_event_integrable d F L A HL Hlip mA.
have HR := (proj1 (integrable_mkcond (fun x : d.-tuple (measurableTypeR R) => (F (tval x))%:E) mA)) HF.
have [HF2 HE2] := paper_main_gaussian_lipschitz_square_law d F L HL Hlip.
have HI := integrable_indic (gaussian_product_law d) mA.
have HQ : (gaussian_product_law d).-integrable setT
  (fun x => (q%:E * (F (tval x)*F (tval x))%:E)%E) by exact: integrableZl HF2.
have HA : (gaussian_product_law d).-integrable setT
  (fun x => (a%:E * (\1_A x)%:E)%E) by exact: integrableZl HI.
have HS := integrableD measurableT HQ HA.
have HB : (\int[gaussian_product_law d]_x
    (((fun y => (F (tval y))%:E) \_ A) x) <=
  \int[gaussian_product_law d]_x
    (q%:E * (F (tval x)*F (tval x))%:E + a%:E * (\1_A x)%:E))%E.
{ eapply (le_integral measurableT HR HS).
  move=> x _; rewrite /restrict /numfun.indic.
  case: (boolP (x \in A)) => Hx.
  - rewrite -!EFinM -EFinD lee_fin; apply/RleP.
    change (F (tval x) <= q * (F (tval x)*F (tval x)) + a*1).
    rewrite Rmult_1_r; exact (paper_main_exceptional_young (F (tval x)) a Ha).
  - rewrite -!EFinM -EFinD lee_fin; apply/RleP.
    change (0 <= q * (F (tval x)*F (tval x)) + a*0); nra. }
rewrite (integralD measurableT HQ HA) (integralZl measurableT HF2)
  (integralZl measurableT HI) HE2 (integral_indic (gaussian_product_law d) measurableT mA) setIT in HB.
rewrite integral_mkcond; move: HB.
by rewrite -EFinM.
Qed.
