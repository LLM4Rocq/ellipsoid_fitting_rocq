(* The balanced alternative in the supercritical regime.

   paper_main_balanced_from_unsat: assume that the fit event and the
   balanced positive-definite event (eq:alt-cor-event) are measurable, that
   every spanning sample with no fit lies in the balanced event, and that
   the fit probability tends to 0 whenever the liminf of n(d) / d^2 exceeds
   1/4. Then, in that regime, the probability of the balanced event tends
   to 1. These three properties are hypotheses of the theorem.

   The proof: for 0 < d <= n, paper_main_balanced_complement_from_separation
   shows that the balanced event and the complement of the fit event agree
   almost surely, since the Gaussian sample spans almost surely and a fit
   excludes a balanced certificate. When the liminf of the density exceeds
   1/4, d <= n(d) for every large d (paper_main_supercritical_spanning_count),
   so the probability of the balanced event is eventually 1 minus the fit
   probability. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions PaperMainAsymptotics PaperMainFixedDensity
  PaperMainBalancedProbability PaperMainGeometryExclusion
  PaperMainGeometryHomogeneous PaperMainGaussianSpanning.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma paper_main_quarter_density_spanning_count (n : nat -> nat) (d : nat) :
  (4 <= d)%N -> 1 / 4%:R <= paper_main_density n d -> (d <= n d)%N.
Proof.
move=> Hd Hn.
have HdR : (4%:R : R) <= d%:R by rewrite ler_nat.
have Hd0 : (0 : R) < d%:R.
  apply: lt_le_trans _ HdR; by rewrite ltr0n.
have Hsq : (0 : R) < d%:R ^+ 2 by exact: exprn_gt0.
move: Hn; rewrite /paper_main_density ler_pdivlMr // expr2 => /RleP Hn.
move/RleP: HdR => HdR.
rewrite -(ler_nat R); apply/RleP.
apply: (Rle_trans _ ((1 / 4%:R) * (d%:R * d%:R)) _ _ Hn).
apply/RleP.
change ((d%:R : R) <= (1 / 4%:R) * (d%:R * d%:R)).
rewrite mulrCA -[leLHS]mulr1 ler_pM2l // mul1r mulrC.
rewrite ler_pdivlMr ?ltr0n // mul1r.
exact/RleP.
Qed.

Lemma paper_main_supercritical_spanning_count (n : nat -> nat) :
  paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
  exists D : nat, forall d : nat, (D <= d)%N -> (0 < d <= n d)%N.
Proof.
move=> [a [Ha [D HD]]].
exists (maxn 4 D); move=> d.
rewrite geq_max => /andP [Hd4 Hd].
apply/andP; split.
- exact: leq_trans (isT : (0 < 4)%N) Hd4.
- apply: paper_main_quarter_density_spanning_count => //.
  exact: le_trans (ltW Ha) (HD d Hd).
Qed.

Lemma paper_main_probability_ae_equal (n d : nat)
    (E F : set (paper_main_sample n d)) :
  measurable E -> measurable F ->
  {ae gaussian_product_law (n * d)%N, forall x, E x <-> F x} ->
  paper_main_probability n d E = paper_main_probability n d F.
Proof.
move=> mE mF hEF.
have eE := integral_indic (gaussian_product_law (n * d)%N) measurableT mE.
have eF := integral_indic (gaussian_product_law (n * d)%N) measurableT mF.
rewrite setIT in eE.
rewrite setIT in eF.
rewrite /paper_main_probability -eE -eF.
apply: ae_eq_integral; first exact: measurableT.
- apply/measurable_EFinP; exact: measurable_indic.
- apply/measurable_EFinP; exact: measurable_indic.
- apply: (filterS _ hEF) => x h _.
  congr (_%:E); rewrite /numfun.indic.
  have hmem : (x \in E) = (x \in F).
    apply/idP/idP; rewrite !inE; [exact: (proj1 h) | exact: (proj2 h)].
  by rewrite hmem.
Qed.

Lemma paper_main_balanced_complement_from_separation (n d : nat) :
  (0 < d)%N -> (d <= n)%N ->
  measurable (paper_main_fit_event n d) ->
  measurable (paper_main_balanced_pd_event n d) ->
  (forall x : paper_main_sample n d,
    paper_main_spanning x -> ~ paper_main_fit_event n d x ->
    paper_main_balanced_pd_event n d x) ->
  paper_main_probability n d (paper_main_balanced_pd_event n d) =
    (1 - paper_main_probability n d (paper_main_fit_event n d))%E.
Proof.
move=> Hd hdn mF mB Hsep.
rewrite -(paper_main_probability_complement n d _ mF).
apply: paper_main_probability_ae_equal => //; first exact: measurableC.
apply: (filterS _ (paper_main_gaussian_spanning_ae n d hdn)) => x hspan.
split=> [hb hf|hnfit].
- exact: paper_main_fit_balanced_exclusive n d x Hd hf hb.
- exact: Hsep x hspan hnfit.
Qed.

Lemma paper_main_tends_to_complement_one (p : nat -> \bar R) :
  paper_main_tends_to p 0 ->
  paper_main_tends_to (fun d => (1 - p d)%E) 1.
Proof.
move=> Hp eps Heps.
case: (Hp eps Heps) => D HD.
exists D; move=> d Hd.
have Hpd := HD d Hd.
rewrite sube0 in Hpd.
by rewrite addeAC subee // add0e abseN.
Qed.

Lemma paper_main_tends_to_eventually_equal (p q : nat -> \bar R) (l : R) :
  (exists D : nat, forall d, (D <= d)%N -> p d = q d) ->
  paper_main_tends_to p l -> paper_main_tends_to q l.
Proof.
move=> [D0 Heq] Hp eps Heps.
case: (Hp eps Heps) => D HD.
exists (maxn D0 D); move=> d.
rewrite geq_max => /andP [Hd0 Hd].
by rewrite -(Heq d Hd0); exact: HD d Hd.
Qed.

Lemma paper_main_balanced_from_unsat :
  (forall n d : nat, measurable (paper_main_fit_event n d)) ->
  (forall n d : nat, measurable (paper_main_balanced_pd_event n d)) ->
  (forall (n d : nat) (x : paper_main_sample n d),
    (0 < d)%N -> paper_main_spanning x -> ~ paper_main_fit_event n d x ->
    paper_main_balanced_pd_event n d x) ->
  (forall n : nat -> nat,
    paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 0) ->
  forall n : nat -> nat,
    paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d
        (paper_main_balanced_pd_event (n d) d)) 1.
Proof.
move=> mF mB Hsep Hunsat n Hn.
apply: (paper_main_tends_to_eventually_equal
  (fun d => (1 - paper_main_probability (n d) d (paper_main_fit_event (n d) d))%E)).
- have [D HD] := paper_main_supercritical_spanning_count n Hn.
  exists D; move=> d Hd.
  have /andP [d0 hdn] := HD d Hd.
  symmetry; apply: paper_main_balanced_complement_from_separation => //.
  by move=> x; apply: Hsep.
- apply: paper_main_tends_to_complement_one.
  exact: Hunsat n Hn.
Qed.
