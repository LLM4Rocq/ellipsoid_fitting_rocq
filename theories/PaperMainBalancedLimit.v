(* The balanced positive definite event has probability tending to 1 for every
   sample-size sequence whose density has liminf greater than 1/4 (A34, part 1).

   Inputs, all checked and without premises:
   - paper_main_unsat_supercritical_limit (PaperMainUnsatLimit): the fit
     probability tends to 0 for every such sequence;
   - paper_main_not_fit_balanced (PaperMainBalancedLaw): for d > 0, a spanning
     sample that does not fit lies in the balanced event;
   - pm_fit_event_measurable and pm_balanced_pd_event_measurable: both events
     are measurable for every n and d.
   The existing reduction paper_main_balanced_from_unsat turns these into the
   limit 1. This is the supercritical half only: the subcritical half and the
   main result stay open. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainDefinitions
  PaperMainAsymptotics PaperMainFixedDensity PaperMainGeometryHomogeneous
  PaperMainMeasurabilityFit PaperMainMeasurabilityBalanced PaperMainBalancedSupercritical
  PaperMainBalancedLaw PaperMainUnsatLimit.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* The balanced event is measurable, for every n and d. *)
Theorem paper_main_balanced_event_measurable_all :
  forall n d : nat, measurable (paper_main_balanced_pd_event n d).
Proof. exact: pm_balanced_pd_event_measurable. Qed.

(* The balanced probability tends to 1 above density 1/4. *)
Theorem paper_main_balanced_supercritical_limit (n : nat -> nat) :
  paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
  paper_main_tends_to (fun d => paper_main_probability (n d) d
    (paper_main_balanced_pd_event (n d) d)) 1.
Proof.
apply: paper_main_balanced_from_unsat.
- exact: pm_fit_event_measurable.
- exact: pm_balanced_pd_event_measurable.
- by move=> m d x Hd Hspan Hnot; exact: paper_main_not_fit_balanced.
- exact: paper_main_unsat_supercritical_limit.
Qed.

(* Both together: the endpoint with its unconditional measurability. *)
Corollary paper_main_balanced_supercritical_endpoint :
  (forall n d : nat, measurable (paper_main_balanced_pd_event n d)) /\
  forall n : nat -> nat, paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
    paper_main_tends_to (fun d => paper_main_probability (n d) d
      (paper_main_balanced_pd_event (n d) d)) 1.
Proof.
split; first exact: paper_main_balanced_event_measurable_all.
exact: paper_main_balanced_supercritical_limit.
Qed.
