(* A lower bound on the mean of a nonnegative loss that is large with high
   probability. paper_main_loss_expected_gap: if F >= 0 is continuous with a
   polynomial bound (pmdf_regular) and F >= e outside a measurable set A of
   Gaussian probability at most p, then the Gaussian mean of F, written as
   the iterated expectation gaussian_iterated_expectation, is at least
   e (1 - p). The proof integrates e times the indicator of the complement
   of A against gaussian_product_law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology ereal measure lebesgue_measure lebesgue_integral
  measurable_realfun probability normal_distribution.
From EllipsoidFitting Require Import AnalysisBridge GaussianProductDefinitions GaussianProbabilityProductDefinitions
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments.
Import GRing.Theory Num.Theory Order.TTheory.
Delimit Scope R_scope with Rcoq.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Theorem paper_main_loss_expected_gap d (F : list R -> R)
  (A : set (d.-tuple (measurableTypeR R))) (e p : R) :
  pmdf_regular d F -> measurable A -> (0<=e)%Rcoq ->
  (forall x : d.-tuple (measurableTypeR R), (0<=F(tval x))%Rcoq) ->
  (forall x : d.-tuple (measurableTypeR R), ~A x -> (e<=F(tval x))%Rcoq) ->
  (gaussian_product_law d A<=p%:E)%E ->
  (e*(1-p)<=gaussian_iterated_expectation d F)%Rcoq.
Proof.
move=> HR mA He HF Hgap HP.
have [HI HE] := pmdf_actual d F HR.
have mAc : measurable (~` A) by exact: measurableC.
have HIA := integrable_indic (gaussian_product_law d) mAc.
have HL : (gaussian_product_law d).-integrable setT (fun x => (e%:E * (numfun.indic (~` A) x)%:E)%E)
  by exact: integrableZl HIA.
have Hle : (\int[gaussian_product_law d]_x (e%:E * (numfun.indic (~` A) x)%:E) <=
  \int[gaussian_product_law d]_x (F(tval x))%:E)%E.
  apply: (le_integral measurableT HL HI) => x _.
  rewrite /numfun.indic -EFinM lee_fin; apply/RleP.
  case: (boolP (x \in ~` A)) => Hx.
  - rewrite mulr1; apply Hgap; move: Hx; by rewrite inE.
  - rewrite mulr0; exact: HF.
rewrite (integralZl measurableT HIA) (integral_indic (gaussian_product_law d) measurableT mAc)
  setIT HE in Hle.
have HAc : gaussian_product_law d (~` A) = (1-gaussian_product_law d A)%E
  by exact: probability_setC.
change (is_true ((e%:E * gaussian_product_law d (~` A) <= (gaussian_iterated_expectation d F)%:E)%E)) in Hle.
rewrite HAc in Hle.
have Hfin : gaussian_product_law d A \is a fin_num by apply: fin_num_measure.
rewrite -(fineK Hfin) -EFinB -EFinM lee_fin in Hle.
rewrite -(fineK Hfin) lee_fin in HP.
move/RleP: Hle => Hle; move/RleP: HP => HP.
change (e*(1-fine(gaussian_product_law d A))<=gaussian_iterated_expectation d F)%Rcoq in Hle.
change (fine(gaussian_product_law d A)<=p)%Rcoq in HP.
nra.
Qed.
