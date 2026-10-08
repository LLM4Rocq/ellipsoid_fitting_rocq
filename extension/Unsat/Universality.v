(* The unsatisfiable phase for every fourth moment kappa > 1: Theorem 1.7
   and the second conjunct of Theorem 1.2 (ii) of Koehler and Sohn (arXiv
   2608.27372, lines 1602-1635 of arxiv_v1.tex), at Stdlib's R. It is item
   U10 of stage 2 of phase 5 (AGENTS.md), after the stage 1 theorem at
   kappa = 3 (Unsat/FourthMomentThree).

   Statements to prove (phase 5, stage 2; names come with the proofs): for
   kappa > 1, K > 0, alpha > 0, every family nu of laws with
   universality_coordinate_law kappa K (nu d j) for j < d, and every n
   with universality_density_tends_to n alpha:
   - Theorem 1.7: universality_fitting_error (n d) d converges in
     probability, under universality_sample_law (nu d) (n d) d, to
     universality_e_star alpha kappa.
   - Theorem 1.2 (ii): if universality_alpha_star kappa < alpha, then
     universality_e_star alpha kappa > 0 and the probability of the fit
     event tends to 0; with the measurability of
     universality_error_event (Model/Measurability), this is the second
     conjunct of universality_statement.

   Proof plan.
   1. The features of the sample are independent regular features with
      covariance unsat_cov kappa d and tau = O(d^(-1/2)) (Model/Rows,
      data_feature_regular of Features/Regular); the Gaussian features of
      law gaussian_feature_law kappa d are regular with the same
      covariance (gaussian_feature_regular).
   2. Corollary 2.13 (ii) (Unsat/Regularized): unsat_value of the two
      laws concentrate around the same c d, so the fitting error, twice
      unsat_value (unsat_fitting_error of Unsat/LeastSquares), and its
      Gaussian counterpart have the same limit in probability.
   3. Proposition 1.4 (ii) (item G8 of lane C, extension/Gaussian): the
      Gaussian value 2 unsat_value tends to universality_e_star alpha kappa
      in probability. Hence Theorem 1.7.
   4. If alpha > universality_alpha_star kappa, then e_star > 0
      (Proposition 1.4), and a fit makes the fitting error 0
      (fit_unsat_value of Unsat/FourthMomentThree), an event of probability
      tending to 0 by Theorem 1.7. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows Measurability.
