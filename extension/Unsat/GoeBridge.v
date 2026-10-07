(* The Gaussian lower bound at fourth moment 3, from the formal proof of the
   Gaussian ellipsoid fitting theorem in theories/: for alpha > 1/4, the
   optimal squared fitting error of n independent GOE features is bounded
   below with probability tending to one. This is Proposition 1.4 (ii) of
   Koehler and Sohn (arXiv 2608.27372, line 323 of arxiv_v1.tex) at
   kappa = 3, without the limit of the error, at Stdlib's R.

   Main results to prove (phase 5, stage 1; names come with the proofs):
   - The law of the GOE rows of theories/ (the public Gaussian rows of the
     bulk array of theories/Hybrid/Residual.v, for matrices of size d,
     under the frozen gaussian_product_law) is the law of n independent
     features of law gaussian_feature_law 3 d (Features/Definitions), up to
     mxvec: on each row both are centered Gaussian vectors with covariance
     unsat_cov 3 d (gauss_mulmx_law of comparison/gauss_law.v), and the
     rows are independent (Model/Rows).
   - From paper_main_hybrid_gap_event (theories/Hybrid/Assembly.v) at head
     dimension 0 and bulk size d: for alpha > 1/4 there are e > 0 and c > 0
     such that, for every n with n/d^2 -> alpha and every large d, outside
     an event of probability at most exp (- c d^2), every S >= 0 of trace d
     and every b satisfy (1/n) sum_i (<G_i, S> - b)^2 >= e. The loss of
     theories/, 1 - exp (- t^2), is at most t^2, and |S|_F >= sqrt d when
     S >= 0 has trace d, so S / sqrt d is an admissible matrix of that
     theorem.
   - Hence the probability that unsat_value (n d) d Z < e / 2 under
     tuple_prod (fun=> gaussian_feature_law 3 d) (n d) tends to 0. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.comparison Require Import gauss_law.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Hybrid.Residual Hybrid.Assembly.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions.
