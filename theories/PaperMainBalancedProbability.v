(* Probability consequences of deterministic fit/balanced exclusion.
   Measurability and phase estimates remain explicit hypotheses until
   their independent proof modules are complete. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainAsymptotics
  PaperMainFixedDensity PaperMainGeometryExclusion.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma paper_main_probability_complement (n d : nat)
    (E : set (paper_main_sample n d)) :
  measurable E ->
  paper_main_probability n d (~` E) = (1 - paper_main_probability n d E)%E.
Proof.
move=> mE; rewrite /paper_main_probability.
exact: probability_setC.
Qed.

Lemma paper_main_balanced_probability_le_complement (n d : nat) :
  (0 < d)%N -> measurable (paper_main_fit_event n d) ->
  measurable (paper_main_balanced_pd_event n d) ->
  (paper_main_probability n d (paper_main_balanced_pd_event n d) <=
   1 - paper_main_probability n d (paper_main_fit_event n d))%E.
Proof.
move=> Hd mF mB.
rewrite -(paper_main_probability_complement n d _ mF).
apply: paper_main_probability_mono => //.
- exact: measurableC.
- move=> x Hbal Hfit.
  exact: paper_main_fit_balanced_exclusive n d x Hd Hfit Hbal.
Qed.

Lemma paper_main_tends_to_complement_zero (p : nat -> \bar R) :
  paper_main_tends_to p 1 ->
  paper_main_tends_to (fun d => (1 - p d)%E) 0.
Proof.
move=> Hp eps Heps.
case: (Hp eps Heps) => D HD.
exists D; move=> d Hd.
have Hpd := HD d Hd.
rewrite sube0 -abseN oppeB.
- by apply: fin_num_adde_defr.
- by rewrite addeC.
Qed.

Lemma paper_main_balanced_from_sat :
  (forall n d : nat, measurable (paper_main_fit_event n d)) ->
  (forall n d : nat, measurable (paper_main_balanced_pd_event n d)) ->
  (forall n : nat -> nat,
    paper_main_limsup_lt (paper_main_density n) (1 / 4%:R) ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 1) ->
  forall n : nat -> nat,
    paper_main_limsup_lt (paper_main_density n) (1 / 4%:R) ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d
        (paper_main_balanced_pd_event (n d) d)) 0.
Proof.
move=> mF mB Hsat n Hn.
apply: (paper_main_tends_to_zero_squeeze_eventually _
 (fun d => (1 - paper_main_probability (n d) d
   (paper_main_fit_event (n d) d))%E) 1).
- move=> d.
  exact: (proj1 (andP (paper_main_probability_bounds _ _ _ (mB (n d) d)))).
- move=> d Hd.
  by apply: paper_main_balanced_probability_le_complement.
- apply: paper_main_tends_to_complement_zero.
  exact: Hsat n Hn.
Qed.
