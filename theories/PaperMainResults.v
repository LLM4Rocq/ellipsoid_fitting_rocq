(* Exact fixed main conclusion assembled from the probability limits. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
Open Scope ring_scope.

From EllipsoidFitting Require Import PaperMainFinalAssembly PaperMainConditionedLimit.
Local Open Scope ring_scope.

Theorem paper_main_results :
(* thm:main: the sharp ellipsoid fitting transition, both phases. *)
((forall n d : nat, measurable (paper_main_fit_event n d)) /\
 (forall n : nat -> nat,
   (paper_main_limsup_lt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 1) /\
   (paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 0))) /\
(* thm:conditioned: well-conditioned fits of trace d below the threshold,
   with constants depending only on alpha*. *)
(forall alpha : R, alpha < 1 / 4%:R ->
  exists lm lp : R, 0 < lm /\ lm <= lp /\
  (forall n d : nat, measurable (paper_main_conditioned_event n d lm lp)) /\
  (forall n : nat -> nat,
    paper_main_limsup_le (paper_main_density n) alpha ->
    paper_main_tends_to
      (fun d => paper_main_probability (n d) d (paper_main_conditioned_event (n d) d lm lp)) 1)) /\
(* cor:alternative: the threshold for balanced positive definite
   combinations, both limits. *)
((forall n d : nat, measurable (paper_main_balanced_pd_event n d)) /\
 (forall n : nat -> nat,
   (paper_main_limsup_lt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_balanced_pd_event (n d) d)) 0) /\
   (paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
     paper_main_tends_to
       (fun d => paper_main_probability (n d) d (paper_main_balanced_pd_event (n d) d)) 1))).
Proof. exact (paper_main_results_from_conditioned paper_main_conditioned_limit). Qed.
