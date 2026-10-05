(* Conditioned subcritical limit from the checked lower law and spectral reduction. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From EllipsoidFitting Require Import GaussianProbabilityProductContinuity PaperMainDefinitions
 PaperMainFixedDensity PaperMainMeasurabilityConditioned
 PaperMainFixedLowerProbability PaperMainConditionedFromLower.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Theorem paper_main_conditioned_fixed_limit beta :
  0 < beta -> beta < 1 / 4%:R ->
  exists lm lp : R, 0 < lm /\ lm <= lp /\
    paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count beta d) d
      (paper_main_conditioned_event (paper_main_fixed_count beta d) d lm lp)) 1.
Proof.
move=>Hb0 Hbq.
have [Hb0c Hbqc] := paper_main_fixed_beta_coq beta Hb0 Hbq.
have [E [mE [HE HC]]] := paper_main_fixed_lower_probability beta Hb0 Hbq.
exact (paper_main_conditioned_from_lower_exists beta E Hb0c Hbqc mE HE HC).
Qed.

Theorem paper_main_conditioned_limit :
  forall alpha : R, alpha < 1 / 4%:R ->
  exists lm lp : R, 0 < lm /\ lm <= lp /\
  (forall n d : nat, measurable (paper_main_conditioned_event n d lm lp)) /\
  (forall n : nat -> nat,
    paper_main_limsup_le (paper_main_density n) alpha ->
    paper_main_tends_to (fun d => paper_main_probability (n d) d
      (paper_main_conditioned_event (n d) d lm lp)) 1).
Proof.
apply: paper_main_conditioned_from_fixed.
- exact: pm_conditioned_event_measurable.
- exact: paper_main_conditioned_fixed_limit.
Qed.
