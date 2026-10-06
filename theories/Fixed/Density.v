(* Reduction of thm:conditioned and of the unsatisfiable half of thm:main
   to the fixed sample sizes n = floor(beta d^2) (paper_main_fixed_count).
   - paper_main_fixed_count_dominates, paper_main_fixed_count_below:
     n(d) <= floor(beta d^2) when n(d) / d^2 <= beta, and
     floor(beta d^2) <= n(d) when beta <= n(d) / d^2.
   - paper_main_fit_probability_antitone,
     paper_main_conditioned_probability_antitone: adding points can only
     decrease the probability of the fit event and of the well-conditioned
     fit event (from Gaussian.Sample.Deletion).
   - paper_main_eventual_padding, paper_main_eventual_trimming: the
     eventual comparisons of n(d) with floor(beta d^2) under the limsup and
     liminf conditions.
   - paper_main_conditioned_from_fixed: if, for every 0 < beta < 1/4, the
     well-conditioned fit event has probability tending to 1 at
     n = floor(beta d^2) for some constants lm, lp, then the limit of
     thm:conditioned holds.
   - paper_main_unsat_from_fixed: if, for every 1/4 < beta < 1/2, the fit
     event has probability tending to 0 at n = floor(beta d^2), then it
     tends to 0 whenever liminf n / d^2 > 1/4.
   Both reductions pick an intermediate beta, compare n(d) with
   floor(beta d^2) for all large d, and use the monotonicity in the number
   of points with the squeezes paper_main_tends_to_one_squeeze_eventually
   and paper_main_tends_to_zero_squeeze_eventually. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum archimedean matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions Asymptotics
  Gaussian.Sample.Deletion.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

(* Num.truncn is floor on nonnegative reals, and zero on negative reals.
   The reductions below use only nonnegative densities. *)
Definition paper_main_fixed_count (alpha : R) (d : nat) : nat :=
  Num.truncn (alpha * d%:R ^+ 2).

Lemma paper_main_fixed_count_dominates (n : nat -> nat) (alpha : R) (d : nat) :
  0 <= alpha -> (0 < d)%N -> paper_main_density n d <= alpha ->
  (n d <= paper_main_fixed_count alpha d)%N.
Proof.
move=> Ha Hd Hn.
have HdR : (0 : R) < d%:R by rewrite ltr0n.
have Hsq : (0 : R) < d%:R ^+ 2 by exact: exprn_gt0.
have Hx : 0 <= alpha * d%:R ^+ 2 by exact: mulr_ge0 Ha (sqr_ge0 _).
rewrite /paper_main_fixed_count truncn_ge_nat //.
by move: Hn; rewrite /paper_main_density ler_pdivrMr.
Qed.

Lemma paper_main_fixed_count_below (n : nat -> nat) (alpha : R) (d : nat) :
  (0 < d)%N -> alpha <= paper_main_density n d ->
  (paper_main_fixed_count alpha d <= n d)%N.
Proof.
move=> Hd Hn.
have HdR : (0 : R) < d%:R by rewrite ltr0n.
have Hsq : (0 : R) < d%:R ^+ 2 by exact: exprn_gt0.
have Hbound : alpha * d%:R ^+ 2 <= (n d)%:R.
  by move: Hn; rewrite /paper_main_density ler_pdivlMr.
have := le_truncn Hbound.
by rewrite natrK.
Qed.

Lemma paper_main_fit_probability_antitone (n m d : nat) :
  (n <= m)%N -> measurable (paper_main_fit_event m d) ->
  measurable (paper_main_fit_event n d) ->
  (paper_main_probability m d (paper_main_fit_event m d) <=
   paper_main_probability n d (paper_main_fit_event n d))%E.
Proof.
move=> hnm mM mN.
have E : (m - n + n = m)%N by exact: subnK.
have := paper_main_fit_probability_antitone_add (m - n)%N n d.
by rewrite E; apply.
Qed.

Lemma paper_main_conditioned_probability_antitone (n m d : nat) (lm lp : R) :
  (n <= m)%N -> measurable (paper_main_conditioned_event m d lm lp) ->
  measurable (paper_main_conditioned_event n d lm lp) ->
  (paper_main_probability m d (paper_main_conditioned_event m d lm lp) <=
   paper_main_probability n d (paper_main_conditioned_event n d lm lp))%E.
Proof.
move=> hnm mM mN.
have E : (m - n + n = m)%N by exact: subnK.
have := paper_main_conditioned_probability_antitone_add (m - n)%N n d lm lp.
by rewrite E; apply.
Qed.

Lemma paper_main_tends_to_one_squeeze_eventually (p q : nat -> \bar R) (D0 : nat) :
  (forall d, (D0 <= d)%N -> (p d <= q d)%E) ->
  (forall d, (q d <= 1)%E) ->
  paper_main_tends_to p 1 -> paper_main_tends_to q 1.
Proof.
move=> Hpq Hq1 Hp eps Heps.
case: (Hp eps Heps) => D HD.
exists (maxn D0 D); move=> d.
rewrite geq_max => /andP [Hd0 Hd].
have Hpd := HD d Hd.
have Hpq_d := Hpq d Hd0.
rewrite (lee0_abs (x := q d - 1)%E) ?sube_le0 //.
rewrite (lee0_abs (x := p d - 1)%E) ?sube_le0
  ?(le_trans Hpq_d (Hq1 d)) in Hpd; first by [].
apply: le_lt_trans _ Hpd.
rewrite leeN2.
exact: leeB Hpq_d (lexx _).
Qed.

Lemma paper_main_tends_to_zero_squeeze_eventually (p q : nat -> \bar R) (D0 : nat) :
  (forall d, (0 <= p d)%E) ->
  (forall d, (D0 <= d)%N -> (p d <= q d)%E) ->
  paper_main_tends_to q 0 -> paper_main_tends_to p 0.
Proof.
move=> Hp Hpq Hq eps Heps.
case: (Hq eps Heps) => D HD.
exists (maxn D0 D); move=> d.
rewrite geq_max => /andP [Hd0 Hd].
have Hqd := HD d Hd.
rewrite sube0 in Hqd.
rewrite sube0 (gee0_abs (Hp d)).
exact: (le_lt_trans (le_trans (Hpq d Hd0) (lee_abs _)) Hqd).
Qed.

Lemma paper_main_eventual_padding (n : nat -> nat) (alpha beta : R) :
  alpha < beta -> 0 <= beta ->
  paper_main_limsup_le (paper_main_density n) alpha ->
  exists D : nat, forall d, (D <= d)%N ->
    (n d <= paper_main_fixed_count beta d)%N.
Proof.
move=> Hab Hb Hlim.
have Heps : 0 < beta - alpha by rewrite subr_gt0.
case: (Hlim _ Heps) => D HD.
exists (maxn 1 D); move=> d.
rewrite geq_max => /andP [Hd1 Hd].
apply: paper_main_fixed_count_dominates => //.
have := HD d Hd.
change (paper_main_density n d <= alpha + (beta - alpha) ->
  paper_main_density n d <= beta).
by rewrite addrC subrK.
Qed.

Lemma paper_main_eventual_trimming (n : nat -> nat) (alpha beta : R) :
  beta <= alpha -> paper_main_eventually_ge (paper_main_density n) alpha ->
  exists D : nat, forall d, (D <= d)%N ->
    (paper_main_fixed_count beta d <= n d)%N.
Proof.
move=> Hab [D HD].
exists (maxn 1 D); move=> d.
rewrite geq_max => /andP [Hd1 Hd].
apply: paper_main_fixed_count_below => //.
exact: le_trans Hab (HD d Hd).
Qed.

Lemma paper_main_positive_margin (a c : R) :
  0 < c -> a < c -> exists b : R, 0 < b /\ a < b /\ b < c.
Proof.
move=> Hc Hac.
case: (leP a 0) => Ha.
- have [Hb0 Hbc] := midf_lt Hc.
  exists ((0 + c) / 2); split; first exact Hb0.
  split; last exact Hbc.
  exact: le_lt_trans Ha Hb0.
- have [Hab Hbc] := midf_lt Hac.
  exists ((a + c) / 2); split.
  + exact: lt_trans Ha Hab.
  + by split.
Qed.

(* thm:conditioned from its fixed-density form. Given alpha < 1/4, pick
   beta with 0 < beta, alpha < beta < 1/4. For all large d,
   n(d) <= floor(beta d^2), so the probability at n(d) is at least the
   probability at floor(beta d^2), which tends to 1. *)
Lemma paper_main_conditioned_from_fixed :
  (forall n d : nat, forall lm lp : R,
    measurable (paper_main_conditioned_event n d lm lp)) ->
  (forall beta : R, 0 < beta -> beta < 1 / 4%:R ->
    exists lm lp : R, 0 < lm /\ lm <= lp /\
      paper_main_tends_to
        (fun d => paper_main_probability (paper_main_fixed_count beta d) d
          (paper_main_conditioned_event (paper_main_fixed_count beta d) d lm lp)) 1) ->
  forall alpha : R, alpha < 1 / 4%:R ->
    exists lm lp : R, 0 < lm /\ lm <= lp /\
      (forall n d : nat, measurable (paper_main_conditioned_event n d lm lp)) /\
      (forall n : nat -> nat,
        paper_main_limsup_le (paper_main_density n) alpha ->
        paper_main_tends_to
          (fun d => paper_main_probability (n d) d
            (paper_main_conditioned_event (n d) d lm lp)) 1).
Proof.
move=> mE Hfixed alpha Halpha.
have Hqpos : (0 : R) < 1 / 4%:R by rewrite div1r invr_gt0 ltr0n.
case: (paper_main_positive_margin _ _ Hqpos Halpha) => beta [Hb0 [Hab Hbq]].
case: (Hfixed beta Hb0 Hbq) => lm [lp [Hlm [Hlp Hlimit]]].
exists lm, lp; split; first exact Hlm.
split; first exact Hlp.
split; first by move=> n d; exact: mE.
move=> n Hn.
case: (paper_main_eventual_padding n alpha beta Hab (ltW Hb0) Hn) => D HD.
apply: (paper_main_tends_to_one_squeeze_eventually
 (fun d => paper_main_probability (paper_main_fixed_count beta d) d
  (paper_main_conditioned_event (paper_main_fixed_count beta d) d lm lp)) _ D).
- move=> d Hd.
  apply: paper_main_conditioned_probability_antitone;
    [exact: HD d Hd | exact: mE | exact: mE].
- move=> d.
  exact: (proj2 (andP (paper_main_probability_bounds _ _ _
    (mE (n d) d lm lp)))).
- exact Hlimit.
Qed.

Lemma paper_main_margin_below_two (c a t : R) :
  c < a -> c < t -> exists b : R, c < b /\ b < a /\ b < t.
Proof.
move=> Hca Hct.
case: (leP a t) => Hat.
- have [Hcb Hba] := midf_lt Hca.
  exists ((c + a) / 2); split; first exact Hcb.
  split; first exact Hba.
  exact: lt_le_trans Hba Hat.
- have [Hcb Hbt] := midf_lt Hct.
  exists ((c + t) / 2); split; first exact Hcb.
  split; last exact Hbt.
  exact: lt_trans Hbt Hat.
Qed.

(* The unsatisfiable half of thm:main from its fixed-density form, which
   is needed only for 1/4 < beta < 1/2. If n(d) / d^2 >= a > 1/4 for all
   large d, pick 1/4 < beta < a with beta < 1/2. For all large d,
   floor(beta d^2) <= n(d), so the probability at n(d) is at most the
   probability at floor(beta d^2), which tends to 0. *)
Lemma paper_main_unsat_from_fixed :
  (forall n d : nat, measurable (paper_main_fit_event n d)) ->
  (forall beta : R, 1 / 4%:R < beta -> beta < 1 / 2%:R ->
    paper_main_tends_to
      (fun d => paper_main_probability (paper_main_fixed_count beta d) d
        (paper_main_fit_event (paper_main_fixed_count beta d) d)) 0) ->
  forall n : nat -> nat,
    paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d
        (paper_main_fit_event (n d) d)) 0.
Proof.
move=> mE Hfixed n [a [Hqa Hn]].
have Hqh : (1 / 4%:R : R) < 1 / 2%:R.
  change ((1 : R) / 4%:R < (1 : R) / 2%:R).
  by rewrite !div1r ltf_pV2 ?posrE ?ltr0n // ltr_nat.
case: (paper_main_margin_below_two _ _ _ Hqa Hqh) => beta [Hqb [Hba Hbh]].
case: (paper_main_eventual_trimming n a beta (ltW Hba) Hn) => D HD.
apply: (paper_main_tends_to_zero_squeeze_eventually _
 (fun d => paper_main_probability (paper_main_fixed_count beta d) d
   (paper_main_fit_event (paper_main_fixed_count beta d) d)) D).
- move=> d.
  exact: (proj1 (andP (paper_main_probability_bounds _ _ _ (mE (n d) d)))).
- move=> d Hd.
  apply: paper_main_fit_probability_antitone;
    [exact: HD d Hd | exact: mE | exact: mE].
- exact: Hfixed beta Hqb Hbh.
Qed.
