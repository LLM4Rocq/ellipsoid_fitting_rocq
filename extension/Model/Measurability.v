(* The measurability of the events of universality_statement, at Stdlib's R
   (item U11 of extension/README.md), for all n and d.

   Results:
   - paper_main_fit_event n d is measurable: pm_fit_event_measurable of
     theories/Measurability/Fit.v, which does not depend on the law.
   - Z |-> unsat_value n d Z is a measurable function of the n features:
     measurable_unsat_value of Unsat/Regularized.
   - measurable_fitting_error: the optimal squared fitting error
     universality_fitting_error n d is a measurable function of the sample:
     for d >= 1 it is twice unsat_value of the features of the sample
     (unsat_fitting_error of Unsat/LeastSquares, measurable_unsat_features
     of Model/Rows), and for d = 0 the sample has no coordinates, so the
     function is constant. Hence measurable_error_event:
     universality_error_event n d e eps is measurable for all e and eps.

   Main results to prove (phase 5, stages 2 and 3; names come with the
   proofs):
   - The events of the satisfiable phase are countable unions of closed
     sets of samples. If S > 0, then I / m <= S <= m I for some integer
     m > 0, so universality_pd_fit_event n d is the union over m of the
     samples x for which some S with I / m <= S <= m I satisfies
     x_i^T S x_i = 1 for every i; such a set of S is compact and the
     constraints are continuous in (x, S), so each set is closed. For
     universality_conditioned_fit_event n d c, dividing S by lm reduces
     the condition to I <= S <= c I with x_i^T S x_i equal to 1 / lm for
     every i, which is closed in the same way once the value 1 / lm ranges
     over a compact interval [1 / m, m]. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability measurable_realfun.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.convex Require Import ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions Measurability.Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Model Require Import Rows.
Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* The optimal squared fitting error is a measurable function of the
   sample: twice unsat_value of the features for d >= 1, and constant for
   d = 0, where the sample has no coordinates. *)
Lemma measurable_fitting_error n d :
  measurable_fun [set: paper_main_sample n d]
    (fun x => universality_fitting_error n d x : RR).
Proof.
case: (posnP d) => [->|d0].
  pose x0 : paper_main_sample n 0 := [tuple (0 : R) | i < n * 0].
  have xy (x : paper_main_sample n 0) : x = x0.
    by apply: eq_from_tnth => i; have := leq_trans (ltn_ord i) (eq_leq (muln0 n)).
  rewrite (_ : (fun x => universality_fitting_error n 0 x : RR) =
    cst (universality_fitting_error n 0 x0)); last exact: measurable_cst.
  by apply/funext => x; rewrite (xy x).
rewrite (_ : (fun x => universality_fitting_error n d x : RR) =
    fun x => 2 * unsat_value n d (unsat_features n d x)).
  by apply/funext => x; rewrite unsat_fitting_error.
apply: measurable_funM => //.
exact: measurableT_comp (measurable_unsat_value n d)
  (measurable_unsat_features n d).
Qed.

(* The error event of universality_statement is measurable. *)
Lemma measurable_error_event n d (e eps : R) :
  measurable (universality_error_event n d e eps).
Proof.
apply: (measurable_set_lt (f := fun x : paper_main_sample n d =>
  `|universality_fitting_error n d x - e| : RR)).
apply: (measurableT_comp (f := fun r : RR => `|r|)) => //.
by apply: measurable_funB => //; exact: measurable_fitting_error.
Qed.

