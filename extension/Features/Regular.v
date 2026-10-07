(* The regularity of the quadratic features: Proposition 2.6 of Koehler and
   Sohn, "Universality and sharp thresholds for ellipsoid fitting" (arXiv
   2608.27372, lines 1117-1134 of arxiv_v1.tex, proof lines 4233-4438), at
   Stdlib's R, for a point x with independent coordinates of laws nu 0, ...,
   nu (d - 1) as universality_coordinate_law kappa K asks: mean 0, variance
   1, fourth moment kappa and E exp (x^2 / K^2) <= 2. The feature of x is
   unsat_feature d x, the mxvec of W = (x x^T - I) / sqrt d
   (Unsat/LeastSquares), and its law is data_feature_law nu d
   (Features/Definitions). For a symmetric matrix A, <W, A> is
   mxdot (unsat_feature d x) (mxvec A).

   Main results to prove (phase 5, stage 1; names come with the proofs). The
   constants depend only on kappa and K.
   - Moments of the coordinates: E x_j^8 <= 48 K^8, from the subgaussian
     bound (probability/subgaussian.v).
   - Covariance matching (eq:C-kappa-trace, line 271): E <W, A> = 0 and
     E <W, A> <W, B> = feature_cov kappa A B (Gaussian/Cones) for symmetric
     A and B; hence the covariance matrix of data_feature_law nu d is
     unsat_cov kappa d.
   - Linear and quadratic forms (lines 4326-4368), by the moment bounds of
     probability/efron_stein.v with p = 8 and p = 4:
     ||<a, x>||_8 <= C |a| and ||x^T A x - tr A||_4 <= C |A|_F.
   - (F1) in the form that Unsat/Ridge uses: E <W, A>^4 <=
     C (feature_cov kappa A A)^2 for symmetric A.
   - Proposition 2.6: data_feature_law nu d is a regular feature with
     constants C and C / sqrt d and covariance unsat_cov kappa d
     (regular_feature of convex/least_squares.v); first at kappa = 3, where
     unsat_cov 3 d is 2/d times the projection on the symmetric matrices,
     then for every kappa > 1.
   - The Gaussian feature: the covariance matrix of
     gaussian_feature_law kappa d is unsat_cov kappa d, so it is a regular
     feature with that covariance and constants 3^(1/4) and
     sqrt 2 opnorm (unsat_cov kappa d), by the Gaussian case of
     convex/barrier_lindeberg.v. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.probability Require Import efron_stein.
From GaussianAnalysis.convex Require Import least_squares.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions.
