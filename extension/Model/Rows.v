(* The sample as rows, at Stdlib's R: the law of the n * d coordinates of a
   sample of Koehler and Sohn's theorem (arXiv 2608.27372, lines 166-171 of
   arxiv_v1.tex) as the law of n independent points.

   A sample of paper_main_sample n d is a tuple of n * d coordinates, and
   paper_main_point x i is the column of the coordinates i * d + j, j < d.
   Under universality_sample_law nu n d, coordinate k has law nu (k mod d).

   Main results to prove (phase 5, stage 1; names come with the proofs):
   - paper_main_point x i is the tuple_point of row i of tuple_rows n d x
     (probability/tuple_rows.v, Features/Definitions);
   - the image of universality_sample_law nu n d under tuple_rows n d is
     tuple_prod (fun=> tuple_prod nu d) n: the points are independent, and
     each has independent coordinates of laws nu 0, ..., nu (d - 1);
   - for every measurable g on d-tuples of coordinates, the law of
     (g (row i x))_(i < n) under universality_sample_law nu n d is the
     product of n copies of the law of g under tuple_prod nu d; so for
     every bounded measurable, nonnegative measurable or integrable H on
     n-tuples of features, the integral of H (unsat_features n d x) against
     universality_sample_law nu n d is the integral of H against
     tuple_prod (fun=> data_feature_law nu d) n: the features of the points
     are independent with a common law;
   - the same for the frozen gaussian_product_law (n * d), whose rows are
     independent with law gaussian_product_law d. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions.
