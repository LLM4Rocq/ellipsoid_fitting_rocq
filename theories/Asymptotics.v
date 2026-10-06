(* Elementary facts on the probabilities and the asymptotic notions of
   PaperMainDefinitions, and the reduction of the satisfiable half of
   thm:main to thm:conditioned.
   - paper_main_limsup_lt_witness: limsup u < c gives some a < c with
     limsup u <= a.
   - paper_main_conditioned_subset: the well-conditioned fit event is
     contained in the fit event.
   - paper_main_probability_bounds, paper_main_probability_mono: the
     probability of a measurable event is in [0, 1], and it is monotone.
   - paper_main_tends_to_zero_squeeze, paper_main_tends_to_one_squeeze:
     squeezing for the limits 0 and 1 of extended-real sequences.
   - paper_main_sat_from_conditioned: thm:conditioned implies that the fit
     event has probability tending to 1 when limsup n / d^2 < 1/4. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma paper_main_limsup_lt_witness (u : nat -> R) (c : R) :
  paper_main_limsup_lt u c ->
  exists a : R, a < c /\ paper_main_limsup_le u a.
Proof.
move=> [a [Ha [D HD]]].
exists a; split; first exact Ha.
move=> eps /RltP Heps.
exists D; move=> d Hd.
apply/RleP.
move/RleP: (HD d Hd) => Hbound.
change (Rlt R0 eps) in Heps.
change (Rle (u d) (Rplus a eps)); lra.
Qed.

Lemma paper_main_conditioned_subset (n d : nat) (lm lp : R) :
  paper_main_conditioned_event n d lm lp `<=` paper_main_fit_event n d.
Proof.
move=> x [S [HS [Hfit _]]].
by exists S.
Qed.

Lemma paper_main_probability_bounds (n d : nat)
    (E : set (paper_main_sample n d)) :
  measurable E ->
  (0 <= paper_main_probability n d E <= 1)%E.
Proof.
move=> mE; rewrite /paper_main_probability.
apply/andP; split.
- exact: measure_ge0.
- exact: probability_le1.
Qed.

Lemma paper_main_tends_to_zero_squeeze (p q : nat -> \bar R) :
  (forall d, (0 <= p d)%E) ->
  (forall d, (p d <= q d)%E) ->
  paper_main_tends_to q 0 -> paper_main_tends_to p 0.
Proof.
move=> Hp Hpq Hq eps Heps.
case: (Hq eps Heps) => D HD.
exists D; move=> d Hd.
have Hqd := HD d Hd.
rewrite sube0 in Hqd.
rewrite sube0 (gee0_abs (Hp d)).
exact: (le_lt_trans (le_trans (Hpq d) (lee_abs _)) Hqd).
Qed.

Lemma paper_main_probability_mono (n d : nat)
    (E F : set (paper_main_sample n d)) :
  measurable E -> measurable F -> E `<=` F ->
  (paper_main_probability n d E <= paper_main_probability n d F)%E.
Proof.
move=> mE mF EF.
rewrite /paper_main_probability.
apply: le_measure; rewrite ?inE //.
Qed.

Lemma paper_main_tends_to_one_squeeze (p q : nat -> \bar R) :
  (forall d, (p d <= q d)%E) ->
  (forall d, (q d <= 1)%E) ->
  paper_main_tends_to p 1 -> paper_main_tends_to q 1.
Proof.
move=> Hpq Hq1 Hp eps Heps.
case: (Hp eps Heps) => D HD.
exists D; move=> d Hd.
have Hpd := HD d Hd.
rewrite (lee0_abs (x := q d - 1)%E) ?sube_le0 //.
rewrite (lee0_abs (x := p d - 1)%E) ?sube_le0
  ?(le_trans (Hpq d) (Hq1 d)) in Hpd.
- by [].
- apply: le_lt_trans _ Hpd.
  rewrite leeN2.
  exact: leeB (Hpq d) (lexx _).
Qed.

(* The second hypothesis is the statement of thm:conditioned. Given
   limsup n / d^2 < 1/4, pick alpha < 1/4 with limsup n / d^2 <= alpha;
   the well-conditioned fit event for the constants lm, lp of alpha is
   contained in the fit event, whose probability is at most 1. *)
Lemma paper_main_sat_from_conditioned :
  (forall n d : nat, measurable (paper_main_fit_event n d)) ->
  (forall alpha : R, alpha < 1 / 4%:R ->
    exists lm lp : R, 0 < lm /\ lm <= lp /\
    (forall n d : nat, measurable (paper_main_conditioned_event n d lm lp)) /\
    (forall n : nat -> nat,
      paper_main_limsup_le (paper_main_density n) alpha ->
      paper_main_tends_to
        (fun d => paper_main_probability (n d) d
          (paper_main_conditioned_event (n d) d lm lp)) 1)) ->
  forall n : nat -> nat,
    paper_main_limsup_lt (paper_main_density n) (1 / 4%:R) ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 1.
Proof.
move=> mfit Hconditioned n Hn.
case: (paper_main_limsup_lt_witness _ _ Hn) => alpha [Halpha Hbound].
case: (Hconditioned alpha Halpha) => lm [lp [Hlm [Hlp [mconditioned Hlimit]]]].
apply: (paper_main_tends_to_one_squeeze (fun d =>
  paper_main_probability (n d) d (paper_main_conditioned_event (n d) d lm lp))).
- move=> d.
  apply: paper_main_probability_mono;
    [exact: mconditioned | exact: mfit | exact: paper_main_conditioned_subset].
- move=> d.
  exact: (proj2 (andP (paper_main_probability_bounds _ _ _ (mfit (n d) d)))).
- exact: Hlimit n Hbound.
Qed.
