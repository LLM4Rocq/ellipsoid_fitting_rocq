(* The unsatisfiable phase at fourth moment 3: the first conjunct of
   Theorem 1.2 (ii) of Koehler and Sohn (arXiv 2608.27372, lines 164-190 of
   arxiv_v1.tex) for coordinate laws of fourth moment 3, by the paper's
   route (lines 1602-1635), at Stdlib's R. It is the theorem of stage 1 of
   phase 5 (AGENTS.md).

   Statement to prove (names come with the proofs): for K > 0 and
   alpha > 1/4, for every family nu of laws with
   universality_coordinate_law 3 K (nu d j) for j < d, and every n with
   universality_density_tends_to n alpha,
     paper_main_tends_to
       (fun d => universality_probability (nu d) (n d) d
                   (paper_main_fit_event (n d) d)) 0.
   With universality_alpha_star 3 = 1/4 (Gaussian/Threshold), the same
   holds for every alpha > universality_alpha_star 3.

   Proof plan.
   1. For d >= 1, a fit S >= 0 with x_i^T S x_i = d for every i makes the
      optimal squared fitting error zero, since d S / tr S has trace d and
      constant values; and universality_fitting_error n d x is
      2 unsat_value (unsat_features x) (Unsat/LeastSquares).
   2. The features of the points are independent with law
      data_feature_law (nu d) d (Model/Rows), a regular feature with
      constants C and C / sqrt d and covariance unsat_cov 3 d
      (Features/Regular); the Gaussian features of law
      gaussian_feature_law 3 d are regular with the same covariance.
   3. Corollary 2.13 (ii) (Unsat/Regularized): there are reals c d such
      that, for every eps > 0, unsat_value is within eps of c d with
      probability tending to one, for the data features and for the
      Gaussian features.
   4. The Gaussian lower bound (Unsat/GoeBridge): the Gaussian features
      have unsat_value at least e / 2 with probability tending to one, so
      c d >= e / 4 for every large d, and the data features have
      unsat_value at least e / 8 with probability tending to one, which
      excludes a fit. *)
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
From EllipsoidUniversality.Unsat Require Import GoeBridge.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows Measurability.
