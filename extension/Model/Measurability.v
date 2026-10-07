(* The measurability of the events of universality_statement, at Stdlib's R
   (item U11 of extension/README.md), for all n and d.

   Main results to prove (phase 5, stage 1; names come with the proofs):
   - paper_main_fit_event n d is measurable: pm_fit_event_measurable of
     theories/Measurability/Fit.v, which does not depend on the law.
   - The events of the satisfiable phase are countable unions of closed
     sets of samples. If S > 0, then I / m <= S <= m I for some integer
     m > 0, so universality_pd_fit_event n d is the union over m of the
     samples x for which some S with I / m <= S <= m I satisfies
     x_i^T S x_i = 1 for every i; such a set of S is compact and the
     constraints are continuous in (x, S), so each set is closed. For
     universality_conditioned_fit_event n d c, dividing S by lm reduces
     the condition to I <= S <= c I with x_i^T S x_i equal to 1 / lm for
     every i, which is closed in the same way once the value 1 / lm ranges
     over a compact interval [1 / m, m].
   - The optimal squared fitting error universality_fitting_error n d is a
     measurable function of the sample: it is the infimum of a continuous
     function of (x, S, r) over the S >= 0 of trace d and the r >= 0, and
     the same infimum over a countable dense set of such (S, r) (rational
     positive definite S rescaled to trace d, rational r).
   - Hence universality_error_event n d e eps is measurable for all e and
     eps. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import PaperMainDefinitions Measurability.Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions.
